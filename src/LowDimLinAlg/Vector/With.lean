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
      let vTy := mkIdent <| Name.mkSimple <| cx.scalarPrefix ++ "Vector" ++ toString dims.size
      elabCommand <| ← `(namespace $vTy)
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
