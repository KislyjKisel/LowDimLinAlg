module

public import LowDimLinAlg.Internal.Lemmas
public import LowDimLinAlg.Matrix.Types

import LowDimLinAlg.Internal.Dimensionalities
import LowDimLinAlg.Internal.Syntax

@[expose] public section

set_option hygiene false

namespace LowDimLinAlg

open Lean Elab Command
open Internal

run_cmd
  let byDecide ← `(by decide)
  for dims in dimensionalities do
    let mTy := mkIdent <| .mkSimple <| "F64Matrix" ++ toString dims.size
    let dimsSizeSqrLit := Syntax.mkNatLit <| dims.size * dims.size
    let elabRead (rowMajor : Bool) (idUsize idNat : Ident) : CommandElabM Unit := do
      elabCommand <| ← `(
        @[inline]
        def $idUsize (a : FloatArray) (offset : USize) (size_le : a.size <= USize.size) (le_size : offset.toNat + $dimsSizeSqrLit <= a.size) : $mTy :=
          ⟨$(dims.flatMap fun dim1 =>
            dims.map fun dim2 =>
              let idx :=
                if rowMajor
                  then dim1.index * dims.size + dim2.index
                  else dim1.index + dim2.index * dims.size
              app ``FloatArray.uget #[
                mkIdent `a,
                app ``Add.add #[mkIdent `offset, Syntax.mkNatLit idx],
                app ``Lemmas.spanIndex #[
                  app ``FloatArray.size #[mkIdent `a],
                  dimsSizeSqrLit,
                  mkHole .missing,
                  mkIdent `offset,
                  mkIdent `size_le,
                  mkIdent `le_size,
                  byDecide
                ],
              ]
            ):term,*⟩
      )
      addDocStringCore (← resolveGlobalConstNoOverload idUsize) <|
        "Creates a matrix by reading elements from a scalar array. Reads elements in " ++
          (if rowMajor then "row-major order (`m11`, `m12` ...)." else "column-major order (`m11`, `m21` ...).")
      elabCommand <| ← `(
        @[inline, inherit_doc ureadFloatArrayRm]
        def $idNat (a : FloatArray) (offset : Nat) (size_le : a.size ≤ USize.size) (le_size : offset + $dimsSizeSqrLit <= a.size) : $mTy :=
          $idUsize a offset.toUSize size_le (Lemmas.spanIndexNat a.size $dimsSizeSqrLit offset size_le le_size)
      )
    let elabWrite (rowMajor : Bool) (idUsize idNat : Ident) : CommandElabM Unit := do
      elabCommand <| ← `(
        @[inline]
        def $idUsize
          (a : FloatArray)
          (offset : USize)
          (m : $mTy)
          (size_le : a.size <= USize.size)
          (le_size : offset.toNat + $dimsSizeSqrLit <= a.size) :
            { a' : FloatArray // a'.size = a.size } :=
              have : a.size = a.size := rfl
              $(← Array.foldrM
                (fun (dim1, dim2) r =>
                  let rowMajorIdx := dim1.index * dims.size + dim2.index
                  let columnMajorIdx := dim1.index + dim2.index * dims.size
                  let usetIdx := if rowMajor then rowMajorIdx else columnMajorIdx
                  let a' := mkIdent <| .mkSimple <| if rowMajorIdx == 0 then "a" else s!"a{rowMajorIdx - 1}"
                  let a'' := mkIdent <| .mkSimple s!"a{rowMajorIdx}"
                  `(
                    let $a'' := FloatArray.uset
                      $a'
                      (offset + $(Syntax.mkNatLit usetIdx))
                      $(mget `m dim1 dim2)
                      (Nat.lt_of_lt_of_eq (Lemmas.spanIndex a.size $dimsSizeSqrLit $(Syntax.mkNatLit usetIdx) offset size_le le_size $byDecide) this.symm)
                    have : $(a'').size = a.size := Eq.trans (Lemmas.FloatArray_size_uset $a' ..) this
                    $r:term
                  )
                  )
                (← `(⟨$(mkIdent <| .mkSimple s!"a{dims.size * dims.size - 1}"), this⟩))
                (dims.flatMap fun dim1 => dims.map fun dim2 => (dim1, dim2))
              )
      )
      addDocStringCore (← resolveGlobalConstNoOverload idUsize) <|
        "Writes the elements of the matrix to a scalar array in " ++
          (if rowMajor then "row-major order (`m11`, `m12` ...)." else "column-major order (`m11`, `m21` ...).")
      elabCommand <| ← `(
        @[inline, inherit_doc $idUsize]
        def $idNat
          (a : FloatArray)
          (offset : Nat)
          (m : $mTy)
          (size_le : a.size <= USize.size)
          (le_size : offset + $dimsSizeSqrLit <= a.size) :
            { a' : FloatArray // a'.size = a.size } :=
              $idUsize a offset.toUSize m size_le (Lemmas.spanIndexNat a.size $dimsSizeSqrLit offset size_le le_size)
      )
    elabCommand <| ← `(namespace $mTy)
    elabRead (rowMajor := true) (mkIdent `ureadFloatArrayRm) (mkIdent `readFloatArrayRm)
    elabRead (rowMajor := false) (mkIdent `ureadFloatArrayCm) (mkIdent `readFloatArrayCm)
    elabWrite (rowMajor := true) (mkIdent `uwriteFloatArrayRm) (mkIdent `writeFloatArrayRm)
    elabWrite (rowMajor := false) (mkIdent `uwriteFloatArrayCm) (mkIdent `writeFloatArrayCm)
    elabCommand <| ← `(end $mTy)
