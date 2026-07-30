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
  floats.forM fun cx => do
    for dims in dimensionalities do
      let mTy := cx.structure <| "Matrix" ++ toString dims.size
      let vTy := cx.structure <| "Vector" ++ toString dims.size
      elabCommand <| ← `(
        namespace $mTy

        /-- Creates a matrix from rows represented as vectors. -/
        @[inline]
        def ofRows ($(dims.map fun dim => dim.ident):ident* : $vTy) : $mTy :=
          ⟨$(
            dims.flatMap fun d1 => dims.map fun d2 =>
            vget d1.name d2
          ):term,*⟩

        /-- Creates a matrix from columns represented as vectors. -/
        @[inline]
        def ofColumns ($(dims.map fun dim => dim.ident):ident* : $vTy) : $mTy :=
          ⟨$(
            dims.flatMap fun d1 => dims.map fun d2 =>
            vget d2.name d1
          ):term,*⟩

        /--
        Creates a rotation matrix from axes.

        The resulting matrix must be used with row vectors,
        e.g. when multiplying a vector it must be on the left of the matrix.
        Assumes the axes are orthonormal.

        Panics in debug if any axis is not normalized.
        -/
        @[inline]
        def ofAxes ($(dims.map fun dim => dim.ident):ident* : $vTy) : $mTy :=
          debug_assert! $(foldBinopL dims ``Bool.and fun dim => mkIdent <| Name.mkStr2 dim.str "isNormalized")
          ofRows $(dims.map fun dim => dim.ident):ident*

        end $mTy
      )
