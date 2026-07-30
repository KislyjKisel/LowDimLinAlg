module

public import LowDimLinAlg.Vector.Types

meta import LowDimLinAlg.Internal.Dimensionalities
meta import LowDimLinAlg.Internal.Scalars
meta import LowDimLinAlg.Internal.Syntax

@[expose] public section

set_option hygiene false

namespace LowDimLinAlg

open Lean Elab Command
open Internal

run_cmd
  let numbers := scalars.filter fun cx => cx.isNumber
  for dims in dimensionalities do
    let structureSuffix := "Vector" ++ toString dims.size
    numbers.forM fun cx1 => do
      let vTy1 := cx1.structure structureSuffix
      numbers.forM fun cx2 => do
        if cx1.scalarTypeName == cx2.scalarTypeName then return
        let vTy2 := cx2.structure structureSuffix
        if let some s1To2 ← scalarConvertFn? cx1 cx2 then
          let idTo := cx1.structureMember structureSuffix <| "to" ++ cx2.scalarPrefix
          let idOf := cx2.structureMember structureSuffix <| "of" ++ cx1.scalarPrefix
          Lean.Elab.Command.elabCommand <| ← `(
            @[inline]
            def $idTo (v : $vTy1) : $vTy2 :=
              ⟨$(dims.map fun dim => Syntax.mkApp s1To2 #[vget `v dim]),*⟩

            abbrev $idOf := $idTo
          )
          Lean.addDocStringCore (← Lean.resolveGlobalConstNoOverload idTo)
            s!"Converts the vector components to `{cx2.scalarTypeName}` scalar type using `{s1To2.getId}`."
          Lean.addDocStringCore (← Lean.resolveGlobalConstNoOverload idOf)
            s!"Converts the vector components from `{cx1.scalarTypeName}` scalar type using `{s1To2.getId}`."
