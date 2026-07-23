module

public import LowDimLinAlg.Axis
public import LowDimLinAlg.Vector.Boolean

import LowDimLinAlg.Internal.Dimensionalities
import LowDimLinAlg.Internal.Scalars
import LowDimLinAlg.Internal.Syntax

@[expose] public section

set_option hygiene false

namespace LowDimLinAlg

open Lean Elab Command
open Internal

run_cmd
  for dims in dimensionalities 2 4 do
    scalars.forM fun cx => do
      let sTy := cx.scalarType
      let vTy := cx.structure <| "Vector" ++ toString dims.size
      elabCommand <| ← `(namespace $vTy)
      if dims.size = 2 then
        let v3Ty := cx.structure "Vector3"
        elabCommand <| ← `(
          /-- Creates a vector `⟨v.x, v.y, value⟩`. -/
          @[inline]
          def withZ (v : $vTy) (value : $sTy) : $v3Ty :=
            .mk v.x v.y value
        )
      if dims.size = 3 then
        let v4Ty := cx.structure "Vector4"
        elabCommand <| ← `(
          /-- Creates a vector `⟨v.x, v.y, v.z, value⟩`. -/
          @[inline]
          def withW (v : $vTy) (value : $sTy) : $v4Ty :=
            .mk v.x v.y v.z value
        )
      for dim in dims do
        let fId := mkIdent <| Name.mkSimple s!"with{dim.char.toUpper}"
        elabCommand <| ← `(
          @[inline]
          def $fId (v : $vTy) (value : $sTy) : $vTy :=
            $(app `mk <| Array.set! (dims.map fun d => vget `v d) dim.index (mkIdent `value))
        )
        addDocStringCore (← resolveGlobalConstNoOverload fId)
          s!"Creates a vector `⟨{", ".intercalate <| Array.toList <| dims.map fun d => if d.index == dim.index then "value" else s!"v.{d.char}"}⟩`."
      elabCommand <| ← `(end $vTy)
