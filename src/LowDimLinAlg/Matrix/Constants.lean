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
      elabCommand <| ← `(
        namespace $mTy

        /-- All elements set to 0. -/
        @[inline]
        def zero : $mTy :=
          mk $(Array.replicate (dims.size * dims.size) lit0):term*

        /--
        The identity matrix.
        Its multiplication by vector returns the same vector.
        -/
        @[inline]
        def identity : $mTy :=
          mk $(dims.flatMap fun dim => Array.replicate dims.size lit0 |>.set! dim.index lit1):term*

        end $mTy
      )
