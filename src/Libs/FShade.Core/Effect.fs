﻿namespace FShade

open System
open Microsoft.FSharp.Quotations
open Microsoft.FSharp.Quotations.Patterns
open Microsoft.FSharp.Quotations.DerivedPatterns
open Microsoft.FSharp.Quotations.ExprShape
open Microsoft.FSharp.Reflection

open Aardvark.Base
open FShade.Imperative

/// Effect encapsulates a set of shaders for the various ShaderStages defined by FShade.
type Effect internal(shaders : Map<ShaderStage, Shader>) =
        
    let inputToplogy =
        lazy (
            shaders |> Map.toSeq |> Seq.tryPick (fun (_,s) ->
                s.shaderInputTopology
            )
        )

    let first =
        lazy (
            shaders |> Map.toSeq |> Seq.map snd |> Seq.tryHead
        )

    let last =
        lazy (
            shaders |> Map.toSeq |> Seq.map snd |> Seq.tryLast
        )

    let inputs =
        lazy (
            match first.Value with
                | Some shader -> Shader.inputs shader
                | None -> Map.empty
        )

    let outputs =
        lazy (
            match last.Value with
                | Some shader -> Shader.outputs shader
                | None -> Map.empty
        )

    let uniforms =
        lazy (
            shaders 
                |> Map.toSeq 
                |> Seq.map (fun (_,s) -> Shader.uniforms s) 
                |> Seq.fold Map.union Map.empty
        )
        
    /// gets the optionally required InputTopology for the effect.
    /// returns None when the effect is agnostic
    member x.InputToplogy       = inputToplogy.Value
    /// gets the optional first Shader for the effect (in execution-order).
    member x.FirstShader        = first.Value
    /// gets the optional last Shader for the effect (in execution-order).
    member x.LastShader         = last.Value
    /// gets the required inputs for the first Shader in the effect (in execution-order).
    member x.Inputs             = inputs.Value
    /// gets the provided outputs for the last Shader in the effect (in execution-order).
    member x.Outputs            = outputs.Value
    /// gets all required uniforms for the effect (from all shaders).
    member x.Uniforms           = uniforms.Value
    /// gets a Map<ShaderStage, Shader> for the effect containing all Shaders.
    member x.Shaders            = shaders
    /// gets the optional VertexShader for the effect.
    member x.VertexShader       = shaders |> Map.tryFind ShaderStage.Vertex
    /// gets the optional TessControlShader for the effect.
    member x.TessControlShader  = shaders |> Map.tryFind ShaderStage.TessControl
    /// gets the optional TessEvalShader for the effect.
    member x.TessEvalShader     = shaders |> Map.tryFind ShaderStage.TessEval
    /// gets the optional GeometryShader for the effect.
    member x.GeometryShader     = shaders |> Map.tryFind ShaderStage.Geometry
    /// gets the optional FragmentShader for the effect.
    member x.FragmentShader     = shaders |> Map.tryFind ShaderStage.Fragment

/// the Effect module provides functions for accessing, creating and modifying effects.
[<CompilationRepresentation(CompilationRepresentationFlags.ModuleSuffix)>]
module Effect =
    let empty = Effect Map.empty

    /// gets the optional VertexShader for the effect.
    let inline vertexShader (effect : Effect) = effect.VertexShader

    /// gets the optional TessControlShader for the effect.
    let inline tessControlShader (effect : Effect) = effect.TessControlShader

    /// gets the optional TessEvalShader for the effect.
    let inline tessEvalShader (effect : Effect) = effect.TessEvalShader

    /// gets the optional GeometryShader for the effect.
    let inline geometryShader (effect : Effect) = effect.GeometryShader

    /// gets the optional FragmentShader for the effect.
    let inline fragmentShader (effect : Effect) = effect.FragmentShader
    
    /// gets the optionally required InputTopology for the effect.
    /// returns None when the effect is agnostic
    let inline inputTopology (effect : Effect) = effect.InputToplogy

    /// gets the optional first Shader for the effect (in execution-order).
    let inline firstShader (effect : Effect) = effect.FirstShader
    
    /// gets the optional last Shader for the effect (in execution-order).
    let inline lastShader (effect : Effect) = effect.LastShader

    /// gets the optional first ShaderStage for the effect (in execution-order).
    let inline firstStage (effect : Effect) = effect.FirstShader |> Option.map Shader.stage

    /// gets the optional last ShaderStage for the effect (in execution-order).
    let inline lastStage (effect : Effect) = effect.LastShader |> Option.map Shader.stage

    /// gets the required inputs for the first Shader in the effect (in execution-order).
    let inline inputs (effect : Effect) = effect.Inputs

    /// gets the provided outputs for the last Shader in the effect (in execution-order).
    let inline outputs (effect : Effect) = effect.Outputs
    
    /// gets all required uniforms for the effect (from all shaders).
    let inline uniforms (effect : Effect) = effect.Uniforms

    /// creates an effect from a Map<ShaderStage,Shader>.
    let ofMap (shaders : Map<ShaderStage, Shader>) =
        for (stage, shader) in Map.toSeq shaders do
            if stage <> shader.shaderStage then 
                failwithf "[FShade] inconsistent shader-map: %A claims to be %A" shader.shaderStage stage

        Effect shaders
        
    /// creates an effect from a sequence of shaders
    let ofSeq (shaders : seq<Shader>) =
        let mutable map = Map.empty
        for shader in shaders do
            match Map.tryFind shader.shaderStage map with
                | Some prev -> 
                    failwithf "[FShade] conflicting shaders for stage: %A" shader.shaderStage
                | None ->
                    map <- Map.add shader.shaderStage shader map

        Effect map
            
    /// creates an effect from a list of shaders
    let inline ofList (shaders : list<Shader>) = 
        ofSeq shaders
        
    /// creates an effect from an array of shaders
    let inline ofArray (shaders : Shader[]) = 
        ofSeq shaders
        
    /// creates an effect from a single shaders
    let ofShader (shader : Shader) =
        Effect (Map.ofList [shader.shaderStage, shader])
        
    /// creates an effect from an expression (assuming expressions as returned by shader-functions)
    let ofExpr (inputType : Type) (e : Expr) =
        Shader.ofExpr inputType e |> ofList

    /// creates an effect from a shader-function
    let ofFunction (shaderFunction : 'a -> Expr<'b>) =
        Shader.ofFunction shaderFunction |> ofList

    /// gets a Map<ShaderStage, Shader> for the effect containing all Shaders.
    let inline toMap (effect : Effect) = effect.Shaders

    /// gets a sequence of Shaders for the effect
    let toSeq (effect : Effect) =
        effect.Shaders |> Map.toSeq |> Seq.map snd
        
    /// gets a list of Shaders for the effect
    let toList (effect : Effect) =
        effect.Shaders |> Map.toList |> List.map snd
        
    /// gets an array of Shaders for the effect
    let toArray (effect : Effect) =
        effect.Shaders |> Map.toSeq |> Seq.map snd |> Seq.toArray
        
    /// determines whether the effect is empty (has no Shaders).
    let isEmpty (effect : Effect) = 
        Map.isEmpty effect.Shaders
            
    /// gets the optional Shader for the given stage from the effect.
    let tryFindShader (stage : ShaderStage) (effect : Effect) =
        Map.tryFind stage effect.Shaders
        
    /// determines whether the effect includes the given ShaderStage.s
    let hasStage (stage : ShaderStage) (effect : Effect) =
        Map.containsKey stage effect.Shaders

    /// creates a new effect with the given shader addded (replacing the current if it exists).
    let add (shader : Shader) (effect : Effect) =
        Effect (Map.add shader.shaderStage shader effect.Shaders)
        
    /// creates a new effect with the given ShaderStage removed.
    let remove (stage : ShaderStage) (effect : Effect) =
        Effect (Map.remove stage effect.Shaders)
        
    /// creates a new effect by applying the given update-function to
    /// the respective (optional) shader for the given stage.
    /// When update returns Some it will be added/replaced and None will cause the shader to get removed.
    let alter (stage : ShaderStage) (update : Option<Shader> -> Option<Shader>) (effect : Effect) =
        match update (tryFindShader stage effect) with
            | Some n -> 
                if stage <> n.shaderStage then
                    failwithf "[FShade] cannot change shader-stage in Effect.alter from %A to %A" stage n.shaderStage

                add n effect

            | None -> 
                remove stage effect

    /// creates a new effect by adding a shader for the given stage (if none was present).
    let addIfNotPresent (stage : ShaderStage) (create : ShaderStage -> Shader) (effect : Effect) =
        alter stage (function Some o -> Some o | None -> Some (create stage)) effect

    /// creates a new effect which will contain exactly the outputs given by <outputs> at the specified
    /// stage.
    let link (stage : ShaderStage) (outputs : Map<string, Type>) (effect : Effect) =
        let rec linkShaders (needed : Map<string, Type>) (l : list<Shader>) =
            match l with
                | [] -> 
                    []

                | current :: before ->
                    let desired =
                        needed |> Map.union (Shader.systemOutputs current)

                    let newCurrent = 
                        Shader.withOutputs desired current

                    let newBefore = 
                        linkShaders (Shader.inputs newCurrent) before

                    newCurrent :: newBefore
                             
        effect 
            // add the final desired stage passing all desired
            // outputs (if not yet present)
            |> addIfNotPresent stage (Shader.passing outputs)

            // add an empty vertex shader when none is present
            |> addIfNotPresent ShaderStage.Vertex (Shader.passing Map.empty)

            // link all shaders (backward)
            |> toList
            |> List.rev
            |> linkShaders outputs        
                
            // and create the new effect                              
            |> ofList
          
    /// creates a Module for the given effect which can be used for compilation.              
    let toModule (effect : Effect) =
        let rec entryPoints (lastStage : Option<Shader>) (shaders : list<Shader>) =
            match shaders with
                | [] -> 
                    []

                | [shader] -> 
                    [ Shader.toEntryPoint lastStage shader None ]

                | shader :: next :: after ->
                    let shaderEntry = Shader.toEntryPoint lastStage shader (Some next) 
                    shaderEntry :: entryPoints (Some shader) (next :: after)

        { entries = entryPoints None (toList effect) }

    /// composes two effects using sequential semantics for 'abstract' stages.
    /// these 'abstract' stages consist of the following 'real' stages:
    ///     - Primitive: [Vertex; TessControl; TessEval; Geometry]
    ///     - Fragment:  [Fragment]
    /// effects are composed sequentially per 'abstract' stage. 
    /// e.g. r's VertexShader will be appended to l's GeometryShader (if present)
    let compose2 (l : Effect) (r : Effect) =
        let geometryLeft = l |> toList |> List.filter (fun s -> s.shaderStage < ShaderStage.Fragment)
        let geometryRight = r |> toList |> List.filter (fun s -> s.shaderStage < ShaderStage.Fragment)

        let rec composeToLast (l : list<Shader>) (r : list<Shader>) =
            match l with
                | [] -> r
                | [l] ->
                    match r with
                        | [] -> [l]
                        | rh :: _ ->
                            if l.shaderStage < rh.shaderStage then
                                l :: r
                            else
                                let mutable res = l
                                for r in r do res <- Shader.compose2 res r
                                [ res ]
                | h :: rest ->
                    h :: composeToLast rest r

        let shaders = 
            composeToLast geometryLeft geometryRight

        let shaders = 
            match l.FragmentShader, r.FragmentShader with
                | Some l, Some r -> (Shader.compose2 l r) :: shaders
                | None, Some r -> r :: shaders
                | Some l, None -> l :: shaders
                | None, None -> shaders
                        
        ofList shaders

    /// composes many effects using the sequential semantics defined in compose2.
    let compose (effects : #seq<Effect>) =
        effects |> Seq.fold compose2 empty


        
            






        

