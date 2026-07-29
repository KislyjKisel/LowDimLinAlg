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
  floats.forM fun cx => do
    for dims in dimensionalities do
      let mTy := cx.structure <| "Matrix" ++ toString dims.size
      let vTy := cx.structure <| "Vector" ++ toString dims.size
      elabCommand <| ← `(namespace $mTy)
      for dim in dims do
        let rowFn := mkIdent <| .mkSimple s!"row{dim.index + 1}"
        let columnFn := mkIdent <| .mkSimple s!"column{dim.index + 1}"
        let axisFn := mkIdent <| .mkSimple s!"{dim.char}Axis"
        elabCommand <| ← `(
          @[inline]
          def $rowFn (m : $mTy) : $vTy :=
            ⟨$(dims.map fun dim2 => mget `m dim dim2):term,*⟩

          @[inline]
          def $columnFn (m : $mTy) : $vTy :=
            ⟨$(dims.map fun dim2 => mget `m dim2 dim):term,*⟩

          abbrev $axisFn := $rowFn
        )
        addDocStringCore (← resolveGlobalConstNoOverload rowFn) <|
          s!"Returns the {th (dim.index + 1)} row as a vector.\n\n"
        addDocStringCore (← resolveGlobalConstNoOverload columnFn) <|
          s!"Returns the {th (dim.index + 1)} column as a vector.\n\n"
        addDocStringCore (← resolveGlobalConstNoOverload axisFn) <|
          s!"Returns the {th (dim.index + 1)} row as a vector.\n\n"
          ++ "For a transformation matrix that operates on row vectors this vector represents"
          ++ s!" the result of rotating the {dim.char.toUpper} axis by the matrix."
      elabCommand <| ← `(end $mTy)
