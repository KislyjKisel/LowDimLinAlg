module

public import LowDimLinAlg.Scalar
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
  for dims in dimensionalities do
    scalars.forM fun cx => do
      let vTy := mkIdent <| Name.mkSimple <| cx.scalarPrefix ++ "Vector" ++ toString dims.size
      elabCommand <| ← `(namespace $vTy)
      if cx.isNumber then
        elabCommand <| ← `(
          /-- All components set to `0`. -/
          @[inline]
          def zero : $vTy :=
            ⟨$(Array.replicate dims.size lit0),*⟩

          /-- All components set to `1`. -/
          @[inline]
          def one : $vTy :=
            ⟨$(Array.replicate dims.size lit1),*⟩

          /-- All components set to `-1`. -/
          @[inline]
          def negOne : $vTy :=
            ⟨$(Array.replicate dims.size <| Lean.Syntax.mkApp (Lean.mkIdent ``Neg.neg) <| #[lit1]),*⟩
        )
      if cx.isFloat then
        elabCommand <| ← `(
          /-- All components set to NaN. -/
          @[inline]
          def nan : $vTy := ⟨$(Array.replicate dims.size (app ``Div.div #[lit0, lit0])),*⟩

          /-- All components set to positive infinity. -/
          @[inline]
          def infinity : $vTy := ⟨$(Array.replicate dims.size (cx.scalarExtMember "infinity")),*⟩

          /-- All components set to negative infinity. -/
          @[inline]
          def negInfinity : $vTy := ⟨$(Array.replicate dims.size (cx.scalarExtMember "negInfinity")),*⟩
        )
      if cx.isBoolean then
        elabCommand <| ← `(
          /-- All components set to `false`. -/
          @[inline]
          protected def false : $vTy :=
            .ofBits 0 (by decide)

          /-- All components set to `true`. -/
          @[inline]
          protected def true : $vTy :=
            .ofBits $(Lean.Syntax.mkNatLit <| (1 <<< dims.size) - 1) (by decide)
        )
      for dim in dims do
        if cx.isNumber then
          let unitPosId := mkIdent <| Name.mkSimple s!"unit{dim.char.toUpper}"
          elabCommand <| ← `(
            @[inline]
            def $unitPosId : $vTy :=
              $(app `mk <| dims.map fun d => if d.index == dim.index then lit1 else lit0)
          )
          addDocStringCore (← resolveGlobalConstNoOverload unitPosId)
            s!"A unit vector pointing along the positive {dim.char.toUpper} axis."
        if cx.isSigned then
          let unitNegId := mkIdent <| Name.mkSimple s!"unitNeg{dim.char.toUpper}"
          elabCommand <| ← `(
            @[inline]
            def $unitNegId : $vTy :=
              $(app `mk <| dims.map fun d => if d.index == dim.index then app ``Neg.neg #[lit1] else lit0)
          )
          addDocStringCore (← resolveGlobalConstNoOverload unitNegId)
            s!"A unit vector pointing along the negative {dim.char.toUpper} axis."
      elabCommand <| ← `(end $vTy)
