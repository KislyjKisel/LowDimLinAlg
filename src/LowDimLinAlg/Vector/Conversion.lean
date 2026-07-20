module

public import LowDimLinAlg.Vector.Types

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
    let structureSuffix := "Vector" ++ toString dims.size
    scalars.forM fun cx1 => do
      if !cx1.isNumber then return
      let vTy1 := cx1.structure structureSuffix
      scalars.forM fun cx2 => do
        if !cx2.isNumber then return
        let vTy2 := cx2.structure structureSuffix
        if let some s1To2 ← scalarConvertFn? cx1 cx2 then
          let toV2Ty2 := cx1.structureMember structureSuffix <| "to" ++ cx2.scalarPrefix
          Lean.Elab.Command.elabCommand <| ← `(
            @[inline]
            def $toV2Ty2 (v : $vTy1) : $vTy2 :=
              ⟨$(dims.map fun dim => Syntax.mkApp s1To2 #[vget `v dim]),*⟩
          )
          Lean.addDocStringCore (← Lean.resolveGlobalConstNoOverload toV2Ty2)
            s!"Componentwise conversion to `{cx2.scalarTypeName}` scalar type using `{s1To2.getId}`"
        if let some s2To1 ← scalarConvertFn? cx2 cx1 then
          let ofV2Ty2 := cx1.structureMember structureSuffix <| "of" ++ cx2.scalarPrefix
          Lean.Elab.Command.elabCommand <| ← `(
            @[inline]
            def $ofV2Ty2 (v : $vTy2) : $vTy1 :=
              ⟨$(dims.map fun dim => Syntax.mkApp s2To1 #[vget `v dim]),*⟩
          )
          Lean.addDocStringCore (← Lean.resolveGlobalConstNoOverload ofV2Ty2)
            s!"Componentwise conversion from `{cx2.scalarTypeName}` scalar type using `{s2To1.getId}`"
