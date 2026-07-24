module

import LowDimLinAlg.Internal.Dimensionalities
import LowDimLinAlg.Internal.Scalars

@[expose] public section

set_option hygiene false

namespace LowDimLinAlg

open Lean Elab Command
open Internal

run_cmd
  for dims in dimensionalities do
    let bvName := Lean.Name.mkSimple <| "BVector" ++ toString dims.size
    let bvTy := Lean.mkIdent bvName
    let bvMask := Lean.Syntax.mkNatLit <| (1 <<< dims.size) - 1
    Lean.Elab.Command.elabCommand <| ← `(
      structure $bvTy where
        /-- Creates a vector from its bitwise representation. -/
        ofBits ::
        /-- Bitwise representation of the vector. -/
        bits : UInt8
        /-- Only the significant bits may be set. -/
        and_mask_eq_self : bits &&& $bvMask = bits
      deriving DecidableEq
    )
    addDocStringCore (← resolveGlobalConstNoOverload bvTy) <|
      s!"{dims.size}D Bool vector\n\nStored as a single `UInt8` with each component `i` represented by bit `1 <<< i`."

run_cmd
  scalars.forM fun cx => do
    if cx.isBoolean then return
    let sTy := cx.scalarType
    let v2Ty : Ident := cx.structure "Vector2"
    let v3Ty : Ident := cx.structure "Vector3"
    let v4Ty : Ident := cx.structure "Vector4"
    elabCommand <| ← `(
      structure $v2Ty where
        x : $sTy
        y : $sTy
      deriving Repr, Inhabited

      structure $v3Ty where
        x : $sTy
        y : $sTy
        z : $sTy
      deriving Repr, Inhabited

      structure $v4Ty where
        x : $sTy
        y : $sTy
        z : $sTy
        w : $sTy
      deriving Repr, Inhabited
    )
    for (n, vTy) in (2...=4).iter.zip #[v2Ty, v3Ty, v4Ty].iter do
      addDocStringCore (← resolveGlobalConstNoOverload vTy) <|
        s!"{n}D {cx.scalarTypeName} vector"
