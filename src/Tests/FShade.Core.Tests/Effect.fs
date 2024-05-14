module Effect

open Microsoft.FSharp.Quotations
open Microsoft.FSharp.Quotations.Patterns
open Microsoft.FSharp.Quotations.DerivedPatterns
open Microsoft.FSharp.Quotations.ExprShape
open System.Runtime.CompilerServices

open FsUnit
open NUnit.Framework
open Aardvark.Base
open Aardvark.Base.Monads.State

open FShade

#nowarn "4321"

type Vertex =
    {
        [<Position>] pos : V4d
        [<Color>] color : V4d
    }

type [<Struct>] SVertex =
    {
        [<Position>] pos : V4d
        [<Color>] color : V4d
    }

type [<Struct; IsReadOnly>] ROSVertex =
    {
        [<Position>] pos : V4d
        [<Color>] color : V4d
    }

type S2Vertex = struct
   val pos : V4d
   val color : V4d

   new (pos,color) =
      {pos=pos; color=color}
end

let getPos (v : SVertex) = v.pos
let getColor (v : SVertex) = v.color
let inline getPosInline (v : SVertex) = v.pos
let inline getColorInline (v : SVertex) = v.color
let [<ReflectedDefinition>] getPosReflected (v : SVertex) = v.pos
let [<ReflectedDefinition>] getColorReflected (v : SVertex) = v.color

let shader0 (v : Vertex) =
    vertex {
        return { v with pos = V4d.IIII + v.pos }
    }

#if false
let shader0Struct (v : SVertex) =
    vertex {
        return { pos = V4d.IIII + v.pos; color = v.color } // FS3155: A quotation may not involve an assignment to or taking the address of a captured local variable.
    }

let shader0ReadOnlyStruct (v : ROSVertex) =
    vertex {
        return { pos = V4d.IIII + v.pos; color = v.color } // FS3155: A quotation may not involve an assignment to or taking the address of a captured local variable.
    }

let shader0Struct2 (v : S2Vertex) =
    vertex {
        return { pos = V4d.IIII + v.pos; color = v.color } // FS3155: A quotation may not involve an assignment to or taking the address of a captured local variable.
    }
#endif

let shader0StructGetters (v : SVertex) =
    vertex {
        return { pos = V4d.IIII + getPos v; color = getColor v }
    }

let shader0StructInlineGetters (v : SVertex) =
    vertex {
        return { pos = V4d.IIII + getPosInline v; color = getColorInline v }
    }

let shader0StructGettersReflected (v : SVertex) =
    vertex {
        return { pos = V4d.IIII + getPosReflected v; color = getColorReflected v }
    }

let shader1 (offset : V4d) (v : Vertex) =
    vertex {
        return { v with pos = offset + v.pos }
    }

let shader3 (a : V4d) (b : V4d) (v : Vertex) =
    vertex {
        return { v with pos = a + b * v.pos }
    }

let setup() =
    Effect.clearCaches()

[<Test>]
let ``[OfFunction] static``() =
    setup()
    let e0 = Effect.ofFunction shader0
    let e1 = Effect.ofFunction shader0
    e0 |> should equal e1

[<Test>]
let ``[OfFunction] static with closure``() =
    setup()
    let e0 = Effect.ofFunction (shader1 V4d.OIOI)
    let e1 = Effect.ofFunction (shader1 V4d.OIOI)
    e0 |> should equal e1
    let e2 = Effect.ofFunction (shader1 V4d.IOIO)
    e2 |> should not' (equal e1)

[<Test>]
let ``[OfFunction] local``() =
    setup()
    let shader2 (v : Vertex) =
        vertex {
            return { v with pos = V4d.IIII }
        }
    let e0 = Effect.ofFunction shader2
    let e1 = Effect.ofFunction shader2
    e0 |> should equal e1

[<Test>]
let ``[OfFunction] local with closure value``() =
    setup()
    let aaaa = 2.0
    let shader213 (p : V4d) (v : Vertex) =
        vertex {
            return {  pos = aaaa * p; color = v.color }
        }

    let e0 = Effect.ofFunction (shader213 V4d.OIOI)
    let e1 = Effect.ofFunction (shader213 V4d.OIOI)
    e0 |> should equal e1
    let e2 = Effect.ofFunction (shader213 V4d.IOIO)
    e2 |> should not' (equal e1)

[<Test>]
let ``[OfFunction] static curried closure``() =
    setup()
    let t0 = shader3 V4d.Zero
    let t1 = t0 V4d.IIII

    let e0 = Effect.ofFunction t1
    let e1 = Effect.ofFunction (fun a -> shader3 V4d.Zero V4d.IIII a)
    let e2 = Effect.ofFunction (fun a -> t0 V4d.IIII a)
    e0 |> should equal e1
    e0 |> should equal e2
    let e3 = Effect.ofFunction (fun a -> shader3 V4d.IIII V4d.Zero a)
    e3 |> should not' (equal e0)

[<Test>]
let ``[OfFunction] local curried closure``() =
    setup()
    let shader2 (a : V4d) (b : V4d) (v : Vertex) =
        vertex {
            return { v with pos = a + b + v.pos }
        }


    let t0 = shader2 V4d.Zero
    let t1 = t0 V4d.IIII

    let e0 = Effect.ofFunction t1
    let e1 = Effect.ofFunction (fun a -> shader2 V4d.Zero V4d.IIII a)
    let e2 = Effect.ofFunction (fun a -> t0 V4d.IIII a)
    e0 |> should equal e1
    e0 |> should equal e2
    let e3 = Effect.ofFunction (fun a -> shader2 V4d.IIII V4d.Zero a)
    e3 |> should not' (equal e0)




[<Test>]
let ``[Compose] associativity``() =
    setup()
    let a = Effect.ofFunction shader0
    let b = Effect.ofFunction (shader1 V4d.IIII)
    let c = Effect.ofFunction (shader3 V4d.IIII V4d.IIII)

    let r = Effect.compose [ a; Effect.compose [ b; c ] ]
    let l = Effect.compose [ Effect.compose [ a; b ]; c ]

    l |> should equal r

[<Test>]
let ``[Compose] neutral element``() =
    setup()
    let z = Effect.empty
    let a = Effect.ofFunction shader0

    Effect.compose [ z; a ] |> should equal a
    Effect.compose [ a; z ] |> should equal a

[<Test>]
let ``[Compose] caching``() =
    setup()
    let a = Effect.ofFunction shader0
    let b = Effect.ofFunction (shader1 V4d.IIII)
    let c = Effect.ofFunction (shader3 V4d.IIII V4d.IIII)

    let e = Effect.compose [ a; b; c ]
    Effect.compose [ a; b; c ] |> should equal e

[<Test>]
let ``Effect struct parameter with getters``() =
    setup()
    let a = Effect.ofFunction shader0StructGetters

    a.Inputs.Count |> should equal 2

[<Test>]
let ``Effect struct parameter with inline getters``() =
    setup()
    let a = Effect.ofFunction shader0StructInlineGetters

    a.Inputs.Count |> should equal 2

[<Test>]
let ``Effect struct parameter with getters and reflected definition``() =
    setup()
    let a = Effect.ofFunction shader0StructGettersReflected

    a.Inputs.Count |> should equal 2
