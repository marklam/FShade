﻿namespace FShade.Debug

open FShade
open Aardvark.Base
open FSharp.Data.Adaptive

open System
open System.Threading
open System.Collections.Generic
open System.Reflection

module ShaderDebugger =

    type private Project =
        {
            // Metadata about the project
            Data : ProjectData

            // Original assembly of the project
            Assembly : Assembly

            // Callbacks to be invoked when the project is rebuilt
            Callbacks : List<Assembly -> unit>
        }

    type private EffectDefinition =
        {
            // The project in which the effect is defined
            Project : string

            // The name of the declaring type
            TypeName : string

            // The method of the effect
            MethodName : string
        }

    // Contains all found projects stored with project file path as key.
    // Only projects that reference FShade are regarded.
    let private projects = Dictionary<string, Project>()


    module private EffectDefinition =
        open FSharp.Quotations

        let tryResolve (assembly : Assembly) (definition : EffectDefinition) =
            match assembly |> Assembly.tryGetMethod definition.TypeName definition.MethodName with
            | Some mi ->
                let parameters = mi.GetParameters()

                if not <| typeof<Expr>.IsAssignableFrom mi.ReturnType then
                    Result.Error $"Method has an invalid return type of {mi.ReturnType}."

                elif parameters.Length <> 1 then
                    Result.Error $"Effect must have a single parameter (but has {parameters.Length})."

                else
                    let paramType = parameters.[0].ParameterType

                    try
                        let expr = mi.Invoke(null, [| null |]) |> unbox<Expr>
                        let effect = expr |> Effect.ofExpr paramType
                        Result.Ok effect

                    with exn ->
                        Result.Error (string exn)
            | _ ->
                Result.Error $"Failed to resolve effect method {definition.TypeName}.{definition.MethodName}."

        let ofEffect =
            let cache = Dictionary<string, EffectDefinition>()

            fun (effect : FShade.Effect) ->
                match cache.TryGetValue effect.Id with
                | (true, def) -> Some def
                | _ ->
                    let debugRange =
                        match effect.SourceDefintion with
                        | Some (expr, _) -> expr.DebugRange
                        | _ -> None

                    match debugRange with
                    | Some (srcFile, startLine, startCol, _endLine, _endCol) ->
                        projects.Values |> Seq.tryPick (fun p ->
                            if p.Data.Files |> List.contains srcFile then
                                match p.Assembly |> Assembly.tryGetMethodName srcFile startLine startCol with
                                | Some (typeName, methodName) ->
                                    Some {
                                        Project = p.Data.Path
                                        TypeName = typeName
                                        MethodName = methodName
                                    }

                                | None ->
                                    None
                            else
                                None
                        )
                    | None ->
                        None

    // Tries to register an effect to be updated automatically when the corresponding project changes.
    // Note: Only the individual shaders may change, the composition is fixed.
    let private tryRegisterEffect =
        let cache = Dictionary<string, cval<Effect>>()

        let rec getLeaves (e : FShade.Effect) =
            match e.ComposedOf with
            | [] -> [e]
            | [e] -> getLeaves e
            | many -> List.collect getLeaves many

        fun (effect : FShade.Effect) ->
            let mutable success = true

            Log.startTimed "registering effect for debugging"

            let leaves =
                getLeaves effect
                |> List.choose (fun effect ->
                    let id = effect.Id

                    match cache.TryGetValue id with
                    | (true, effect) -> Some effect
                    | _ ->
                        match EffectDefinition.ofEffect effect with
                        | Some def ->
                            let cval = cval effect

                            let update (assembly : Assembly) =
                                match def |> EffectDefinition.tryResolve assembly with
                                | Result.Ok effect ->
                                    cval.Value <- effect

                                | Result.Error error ->
                                    Report.ErrorNoPrefix($"{error} (effect {id})")

                            projects.[def.Project].Callbacks.Add update
                            cache.[id] <- cval
                            Some cval

                        | None ->
                            success <- false
                            None
                )

            if success then
                Log.stop(": success")

                Some <| AVal.custom (fun t ->
                    try
                        leaves |> List.map (fun r -> r.GetValue t) |> Effect.compose
                    with exn ->
                        Log.error "failed to compose modified effect %s: %A" effect.Id exn
                        effect
                )
            else
                Log.stop(": failed")
                None

    let attach() =
        ShaderDebugSystem.initialize (fun _ ->
            Log.startTimed "resolving projects for shader debugger"

            let coreLib = typeof<FShade.Effect>.Assembly.GetName().Name

            for assembly in Introspection.AllAssemblies do
                let refs = assembly.GetReferencedAssemblies()

                if refs |> Array.exists (fun r -> r.Name = coreLib) then
                    match Assembly.tryGetProjectData assembly with
                    | Some data ->
                        projects.[data.Path] <- { Data = data; Assembly = assembly; Callbacks = List() }
                        Log.line "found %s" data.Name

                    | None ->
                        ()

            Log.stop()

            // Spin up thread that recompiles all projects marked as dirty
            let dirty = HashSet<string>()

            let worker =
                if projects.Count > 0 then
                    let mutable running = true

                    let recompile() =
                        let pending =
                            lock dirty (fun () ->
                                let d = dirty.ToArray(dirty.Count)
                                dirty.Clear()
                                d
                            )

                        for projectFile in pending do
                            let project = projects.[projectFile]

                            Log.startTimed "recompiling shaders of %s" project.Data.Name

                            try
                                let result = Compiler.build project.Data

                                match result with
                                | Result.Ok output ->
                                    let assembly = Assembly.LoadFile output

                                    transact (fun () ->
                                        for update in project.Callbacks do
                                            update assembly
                                    )

                                    Log.stop(": success")

                                | Result.Error error ->
                                    Report.ErrorNoPrefix error
                                    Log.stop(": failed")

                            with exn ->
                                Report.ErrorNoPrefix(string exn)
                                Log.stop(": failed")

                    let run() =
                        while running do
                            lock dirty (fun () ->
                                while running && dirty.Count = 0 do
                                    Monitor.Wait dirty |> ignore
                            )

                            if running then
                                Thread.Sleep(500)
                                recompile()

                    let thread = startThread run

                    { new IDisposable with
                        member x.Dispose() =
                            running <- false
                            lock dirty (fun _ -> Monitor.PulseAll dirty)
                            thread.Join()
                    }
                else
                    Disposable.empty

            // Install file watchers
            for p in projects.Values do
                p.Data |> FileWatchers.install (fun _ ->
                    lock dirty (fun () ->
                        if p.Callbacks.Count > 0 && dirty.Add p.Data.Path then
                            Monitor.PulseAll dirty
                    )
                )

            { new ShaderDebugSystem.IShaderDebugger with
                member x.TryRegisterEffect(effect) = tryRegisterEffect effect
                member x.Dispose() =
                    FileWatchers.dispose()
                    worker.Dispose()
            }
        )