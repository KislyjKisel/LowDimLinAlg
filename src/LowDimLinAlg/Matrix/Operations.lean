module

public import LowDimLinAlg.Matrix.Types

import LowDimLinAlg.Internal.Dimensionalities
import LowDimLinAlg.Internal.Scalars
import LowDimLinAlg.Internal.Syntax

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

        /-- The transpose of the matrix. -/
        @[inline]
        def transpose (m : $mTy) : $mTy :=
          mk $(dims.flatMap fun i => dims.map fun j => mget `m j i):ident*

        end $mTy
      )
