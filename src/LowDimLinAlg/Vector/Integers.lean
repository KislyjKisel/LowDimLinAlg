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
  for dims in dimensionalities do
    scalars.forM fun cx => do
      if !cx.isInteger then return
      let sTy := cx.scalarType
      let vTy := cx.structure <| "Vector" ++ toString dims.size
      elabCommand <| ← `(namespace $vTy)
      if cx.isSignedInteger then
        elabCommand <| ← `(
          /-- Componentwise sign (does not return zeros). -/
          @[inline]
          def sign (v : $vTy) : $vTy :=
            ⟨$(dims.map fun dim => app ``ite #[app ``LT.lt #[vget `v dim, lit0], app ``Neg.neg #[lit1], lit1]),*⟩
        )
      if cx.isUnsignedInteger then
        elabCommand <| ← `(
          /-- Squared distance between two points. -/
          @[inline]
          def distanceSqr (a b : $vTy) : $sTy :=
            $(← dims.foldlM
              (fun r dim =>
                lets dim.ident
                  (app ``ite #[
                    app ``LE.le #[vget `b dim, vget `a dim],
                    app ``Sub.sub #[vget `a dim, vget `b dim],
                    app ``Sub.sub #[vget `b dim, vget `a dim],
                  ])
                  r)
              (foldBinopL dims ``Add.add fun dim => app ``Mul.mul #[dim.ident, dim.ident]))
        )
      elabCommand <| ← `(
        deriving instance DecidableEq for $vTy

        /-- Componentwise bitwise `and`. -/
        @[inline]
        def and (a b : $vTy) : $vTy :=
          ⟨$(dims.map fun dim => app ``AndOp.and #[vget `a dim, vget `b dim]),*⟩

        /-- Componentwise bitwise `or`. -/
        @[inline]
        def or (a b : $vTy) : $vTy :=
          ⟨$(dims.map fun dim => app ``OrOp.or #[vget `a dim, vget `b dim]),*⟩

        /-- Componentwise bitwise `xor`. -/
        @[inline]
        def xor (a b : $vTy) : $vTy :=
          ⟨$(dims.map fun dim => app ``XorOp.xor #[vget `a dim, vget `b dim]),*⟩

        /-- Componentwise bitwise `complement` of a vector. -/
        @[inline]
        def complement (a : $vTy) : $vTy :=
          ⟨$(dims.map fun dim => app ``Complement.complement #[vget `a dim]),*⟩

        @[inline] instance : AndOp $vTy := ⟨and⟩
        @[inline] instance : OrOp $vTy := ⟨or⟩
        @[inline] instance : XorOp $vTy := ⟨xor⟩
        @[inline] instance : Complement $vTy := ⟨complement⟩

        /-- Componentwise clamping of components. -/
        @[inline]
        def clamp (v min max : $vTy) : $vTy :=
          ⟨$(dims.map fun dim => app ``Max.max #[vget `min dim, app ``Min.min #[vget `v dim, vget `max dim]]),*⟩

        /-- Componentwise modulo. -/
        @[inline]
        def mod (a b : $vTy) : $vTy :=
          ⟨$(dims.map fun dim => app ``Mod.mod #[vget `a dim, vget `b dim]),*⟩

        @[inline] instance : Mod $vTy := ⟨mod⟩
        @[inline]
        instance : HMod $vTy $sTy $vTy :=
          ⟨fun v s => ⟨$(dims.map fun dim => app ``Mod.mod #[vget `v dim, mkIdent `s]),*⟩⟩

        @[inline]
        instance : HMod $sTy $vTy $vTy :=
          ⟨fun s v => ⟨$(dims.map fun dim => app ``Mod.mod #[mkIdent `s, vget `v dim]),*⟩⟩

        end $vTy
      )
