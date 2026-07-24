module

public import LowDimLinAlg.Vector.Floats

import LowDimLinAlg.Internal.Dimensionalities
import LowDimLinAlg.Internal.Scalars
import LowDimLinAlg.Internal.Syntax

@[expose] public section

set_option hygiene false
set_option debugAssertions true -- TODO: delete

namespace LowDimLinAlg

open Lean Elab Command
open Internal

run_cmd
  Internal.scalars.forM fun cx => do
    if !cx.isFloat then return
    let sTy := cx.scalarType
    let m2Ty : Ident := cx.structure "Matrix2"
    let m3Ty : Ident := cx.structure "Matrix3"
    let m4Ty : Ident := cx.structure "Matrix4"
    let v2Ty : Ident := cx.structure "Vector2"
    let v3Ty : Ident := cx.structure "Vector3"
    let v4Ty : Ident := cx.structure "Vector4"
    let m (i j : Nat) (v : Name := `m) : Ident :=
      mkIdent <| v.str s!"m{i + 1}{j + 1}"
    let th : Nat → String := fun
    | 1 => "1st"
    | 2 => "2nd"
    | 3 => "3rd"
    | n => toString n ++ "th"
    elabCommand <| ← `(
      structure $m2Ty where
        m11 : $sTy
        m12 : $sTy
        m21 : $sTy
        m22 : $sTy
      deriving BEq, Inhabited, Repr

      structure $m3Ty where
        m11 : $sTy
        m12 : $sTy
        m13 : $sTy
        m21 : $sTy
        m22 : $sTy
        m23 : $sTy
        m31 : $sTy
        m32 : $sTy
        m33 : $sTy
      deriving BEq, Inhabited, Repr

      structure $m4Ty where
        m11 : $sTy
        m12 : $sTy
        m13 : $sTy
        m14 : $sTy
        m21 : $sTy
        m22 : $sTy
        m23 : $sTy
        m24 : $sTy
        m31 : $sTy
        m32 : $sTy
        m33 : $sTy
        m34 : $sTy
        m41 : $sTy
        m42 : $sTy
        m43 : $sTy
        m44 : $sTy
      deriving BEq, Inhabited, Repr
    )
    let dmvs := dimensionalities.iter.zip (#[m2Ty, m3Ty, m4Ty].iter.zip #[v2Ty, v3Ty, v4Ty].iter)
    for (dims, mTy, vTy) in dmvs do
      addDocStringCore (← resolveGlobalConstNoOverload mTy) <|
        s!"{dims.size}×{dims.size} {cx.scalarTypeName} matrix.\n\nFields are stored in row-major order."
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
          ⟨$(
            dims.flatMap fun d1 => dims.map fun d2 =>
            vget d1.name d2
            ):term,*⟩

        /-- The transpose of the matrix. -/
        @[inline]
        def transpose (m : $mTy) : $mTy :=
          mk $(
            (0...dims.size).toArray.flatMap fun i =>
              (0...dims.size).toArray.map fun (j : Nat) => m j i
          ):ident*

        end $mTy
      )
