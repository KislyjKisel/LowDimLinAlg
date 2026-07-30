module

public import LowDimLinAlg.Matrix.Types

meta import LowDimLinAlg.Internal.Dimensionalities
meta import LowDimLinAlg.Internal.Scalars
meta import LowDimLinAlg.Internal.Syntax

@[expose] public section

set_option hygiene false

namespace LowDimLinAlg

open Lean Elab Command
open Internal

run_cmd
  for dims in dimensionalities do
    let structureSuffix := "Matrix" ++ toString dims.size
    floats.forM fun cx1 => do
      let mTy1 := cx1.structure structureSuffix
      floats.forM fun cx2 => do
        if cx1.scalarTypeName == cx2.scalarTypeName then return
        let mTy2 := cx2.structure structureSuffix
        if let some s1To2 ← scalarConvertFn? cx1 cx2 then
          let idTo := cx1.structureMember structureSuffix <| "to" ++ cx2.scalarPrefix
          let idOf := cx2.structureMember structureSuffix <| "of" ++ cx1.scalarPrefix
          Lean.Elab.Command.elabCommand <| ← `(
            @[inline]
            def $idTo (m : $mTy1) : $mTy2 :=
              ⟨$(dims.flatMap fun dim1 => dims.map fun dim2 => Syntax.mkApp s1To2 #[mget `m dim1 dim2]),*⟩

            abbrev $idOf := $idTo
          )
          Lean.addDocStringCore (← Lean.resolveGlobalConstNoOverload idTo)
            s!"Converts the matrix components to `{cx2.scalarTypeName}` scalar type using `{s1To2.getId}`."
          Lean.addDocStringCore (← Lean.resolveGlobalConstNoOverload idOf)
            s!"Converts the matrix components from `{cx1.scalarTypeName}` scalar type using `{s1To2.getId}`."
