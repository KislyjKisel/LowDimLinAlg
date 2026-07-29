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
  let th : Nat → String := fun
    | 1 => "1st"
    | 2 => "2nd"
    | 3 => "3rd"
    | n => toString n ++ "th"
  let m (i j : Nat) (v : Name := `m) : Ident :=
    mkIdent <| v.str s!"m{i + 1}{j + 1}"
  scalars.forM fun cx => do
    if !cx.isFloat then return
    for dims in dimensionalities do
      let mTy := cx.structure <| "Matrix" ++ toString dims.size
      let vTy := cx.structure <| "Vector" ++ toString dims.size
      elabCommand <| ← `(namespace $mTy)
      for dim in dims do
        let axisFn := mkIdent <| .mkSimple s!"{dim.char}Axis"
        elabCommand <| ← `(
          def $axisFn (m : $mTy) : $vTy :=
            ⟨$(dims.map fun dim2 => m dim.index dim2.index):term,*⟩
        )
        addDocStringCore (← resolveGlobalConstNoOverload axisFn) <|
          s!"Returns the {th (dim.index + 1)} row as a vector.\n\n"
          ++ "For a transformation matrix that operates on row vectors this vector represents"
          ++ s!" the result of rotating the {dim.char.toUpper} axis by the matrix."
      elabCommand <| ← `(
        /-- The transpose of the matrix. -/
        @[inline]
        def transpose (m : $mTy) : $mTy :=
          mk $(
            (0...dims.size).toArray.flatMap fun i =>
              (0...dims.size).toArray.map fun (j : Nat) => m j i
          ):ident*

        end $mTy
      )
