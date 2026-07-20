module

import LowDimLinAlg.Internal.Dimensionalities
import LowDimLinAlg.Internal.Scalars

@[expose] public section

set_option hygiene false

namespace LowDimLinAlg

open Lean Elab Command
open Internal

run_cmd
  for dims in dimensionalities 2 4 do
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
  for dims in dimensionalities 2 4 do
    scalars.forM fun cx => do
      let sTy := cx.scalarType
      let vTy := mkIdent <| Name.mkSimple <| cx.scalarPrefix ++ "Vector" ++ toString dims.size
      if cx.isBoolean then return
      elabCommand <| ← `(
        structure $vTy where
          $(← dims.mapM fun dim => `(Parser.Command.structSimpleBinder|
            $dim.ident:ident : $sTy
          )):structSimpleBinder*
        deriving Repr, Inhabited
      )
      addDocStringCore (← resolveGlobalConstNoOverload vTy) <|
        s!"{dims.size}D {cx.scalarTypeName} vector"
