﻿
open Microsoft.FSharp.Quotations

open Aardvark.Base
open Aardvark.Base.Monads.State
open FShade
open FShade.Imperative
open System.Reflection
open System.Threading
open Microsoft.FSharp.Quotations
open Microsoft.FSharp.Quotations.Patterns
open Microsoft.FSharp.Quotations.DerivedPatterns
open Microsoft.FSharp.Quotations.ExprShape
open System
open System.Runtime.InteropServices

#nowarn "9"

[<RequireQualifiedAccess>]
type SegmentMergeMode =
    | ValueToAvg
    | AvgToAvg
    | TTest


[<StructLayout(LayoutKind.Sequential); StructuredFormatDisplay("{AsString}")>]
type RegionStats =
    struct
        val mutable public Count : int
        val mutable public SurfaceCount : int
        val mutable public Id : int
        val mutable public Average : float32
        val mutable public StdDev : float32
        val mutable public TwoLargeNeighbours : int

        member private x.AsString = x.ToString()

        [<ReflectedDefinition>]
        new(count, surface, id, avg, dev) = { Count = count; SurfaceCount = surface; Id = id; Average = avg; StdDev = dev; TwoLargeNeighbours = 0 }

        override x.ToString() =
            sprintf "{ Count = %A; SurfaceCount = %A; Average = %A; StdDev = %A; Id = %A; Two = %A }" x.Count x.SurfaceCount x.Average x.StdDev x.Id (x.TwoLargeNeighbours <> 0)

    end

module Shader =
    open FShade


    type UniformScope with
        member x.RegionBuffer : RegionStats[] = uniform?StorageBuffer?RegionStats

    type RegionVertex =
        {
            [<Semantic("RegionId")>]
            id : int

            [<Semantic("Average")>]
            avg : float

            [<Semantic("StdDev")>]
            stddev : float

            [<Semantic("Surface")>]
            surface : int

            [<Semantic("Count")>]
            count : int
        }

    [<GLSLIntrinsic("gl_VertexIndex")>]
    let getVertexId() : int = onlyInShaderCode "getVertexId"

    let regionVertex (v : RegionVertex) =
        vertex {
            let id = getVertexId()
            return {
                id = ~~~uniform.RegionBuffer.[id].Id
                avg = float uniform.RegionBuffer.[id].Average
                stddev = float uniform.RegionBuffer.[id].StdDev
                surface = uniform.RegionBuffer.[id].SurfaceCount
                count = uniform.RegionBuffer.[id].Count
            }
        }



let compileEffect (e : list<Effect>) =
    let e = Effect.compose e
    
    let lastShader = e.LastShader

    let lastStage, outputs =
        match lastShader with
            | Some shader ->
                let mutable id = 0
                let newId() = Interlocked.Increment(&id)
                let outputs = shader.shaderOutputs |> Map.map (fun name p -> p.paramType, newId())
                shader.shaderStage, outputs
            | None ->
                ShaderStage.Fragment, Map.ofList ["Colors", (typeof<V4d>, 0)]

    let glsl =
        e |> Effect.toModule { EffectConfig.empty with lastStage = lastStage; outputs = outputs } |> ModuleCompiler.compileGLSL410
    
    
    
    glsl


type Vertex = { [<Position>] pos : V4d }

let shaderA (v : Vertex) =
    fragment {
        return v.pos
    }
    


let funny (v : Vertex) =
    vertex {
        if v.pos.X > 0.0 then
            let Positions = v.pos.W + v.pos.X
            let (a,b) = 
                let v = 2.0 * v.pos
                (v.X, v.Y + 1.0 + Positions)
            return { v with pos = V4d(a,b,b,a) }
        else
            return { pos = V4d.Zero }
    }


type Fragment = 
    {
        [<Color>] c : V4d
        [<Depth(DepthWriteMode.OnlyLess)>] d : float
    }

let fraggy (v : Vertex) =
    fragment {
        return {
            c = V4d.IIII
            d = 0.5
        }
    }

type Payload =
    {
        hitCount : int
    }

type Result =
    {
        value : float
    }

type Ray =
    { origin : V3d; direction : V3d }

type Scene =
    | Self
    | Named of string

[<AutoOpen>]
module Intrinsics = 


    type ShaderTable =
        {
            miss        : int
            offset      : int
            stride      : int
        }

        static member Default = { miss = 0; offset = 1; stride = 1 }

    let trace<'a, 's> (table : ShaderTable) (state : RayQuery<'s, 'a>) : 'a = failwith ""

    let buffers = UniformScope.Global

    type UniformScope with
        member x.Index : int[][] = uniform?StorageBuffer?Index
        member x.Positions : V4d[][] = uniform?StorageBuffer?Positions
        member x.Colors : V4d[][] = uniform?StorageBuffer?Colors
        member x.TexCoords : V2d[][] = uniform?StorageBuffer?TexCoords



type Assign =
    {
        uniforms : Map<string,Type>
        buffers  : Map<string,Type> //contenttype
        samplers : Map<string,SamplerDimension>
    }

type Binding =
    {
        uniforms : list<int * int * list<string * Type>>
        buffers  : Map<string,int * int> //contenttype
        samplers : Map<string,int * int>
    }

let compile (shader : System.Object) (f : Assign -> Binding) : string =
    failwith ""


let test (state : RayHit<Payload, Result>) =
    rayhit {
        let i0 = buffers.Index.[state.instanceIndex].[3 * state.primitiveId + 0]
        return { 
            value = float state.query.payload.hitCount + float i0 
        }
    }

[<EntryPoint>]
let main args =
    let res = 
        RayHitShader.ofFunction test
        |> RayHitShader.toModule
        |> ModuleCompiler.compileGLSLVulkan

    printfn "%A" res.code
    

    0

