module

public import LowDimLinAlg.Matrix.Accessors
public import LowDimLinAlg.Matrix.Constants
public import LowDimLinAlg.Matrix.Constructors
public import LowDimLinAlg.Vector.Numbers

meta import Lean.Elab.BuiltinNotation
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
      let sTy := cx.scalarType
      elabCommand <| ← `(
        namespace $mTy
        @[inline]
        def neg (m : $mTy) : $mTy :=
          ⟨$(dims.flatMap fun i => dims.map fun j => app ``Neg.neg #[mget `m i j]):term,*⟩

        @[inline]
        def add (m1 m2 : $mTy) : $mTy :=
          ⟨$(dims.flatMap fun i => dims.map fun j => app ``Add.add #[mget `m1 i j, mget `m2 i j]):term,*⟩

        @[inline]
        def sub (m1 m2 : $mTy) : $mTy :=
          ⟨$(dims.flatMap fun i => dims.map fun j => app ``Sub.sub #[mget `m1 i j, mget `m2 i j]):term,*⟩

        /-- Multiplies all matrix elements with a scalar. -/
        @[inline]
        def smul (s : $sTy) (m : $mTy) : $mTy :=
          ⟨$(dims.flatMap fun i => dims.map fun j => app ``Mul.mul #[mkIdent `s, mget `m i j]):term,*⟩

        @[inline]
        def mul (m1 m2 : $mTy) : $mTy :=
          ⟨$(dims.flatMap fun i => dims.map fun j =>
            foldBinopL dims ``Add.add fun k =>
              app ``Mul.mul #[mget `m1 i k, mget `m2 k j]
          ):term,*⟩

        /-- Multiplies a row vector and a matrix. -/
        @[inline]
        def mulRow (v : $vTy) (m : $mTy) : $vTy :=
          ⟨$(dims.map fun j =>
            foldBinopL dims ``Add.add fun i =>
              app ``Mul.mul #[vget `v i, mget `m i j]
          ):term,*⟩

        /-- Multiplies a matrix and a column vector. -/
        @[inline]
        def mulColumn (m : $mTy) (v : $vTy) : $vTy :=
          ⟨$(dims.map fun i =>
            foldBinopL dims ``Add.add fun j =>
              app ``Mul.mul #[mget `m i j, vget `v j]
          ):term,*⟩

        @[inline] instance : Neg $mTy := ⟨neg⟩
        @[inline] instance : Add $mTy := ⟨add⟩
        @[inline] instance : Sub $mTy := ⟨sub⟩
        @[inline] instance : SMul $sTy $mTy := ⟨smul⟩
        @[inline] instance : Mul $mTy := ⟨mul⟩
        @[inline] instance : HMul $vTy $mTy $vTy := ⟨mulRow⟩
        @[inline] instance : HMul $mTy $vTy $vTy := ⟨mulColumn⟩

        /-- The transpose of the matrix. -/
        @[inline]
        def transpose (m : $mTy) : $mTy :=
          mk $(dims.flatMap fun i => dims.map fun j => mget `m j i):ident*

        /-- The determinant of the matrix. -/
        @[inline]
        def determinant (m : $mTy) : $sTy := $(
          ← match dims.size with
          | 2 => `(
            m.m11 * m.m22 - m.m12 * m.m21
          )
          | 3 => `(
            m.m11 * m.m22 * m.m33
            + m.m12 * m.m23 * m.m31
            + m.m13 * m.m21 * m.m32
            - m.m13 * m.m22 * m.m31
            - m.m12 * m.m21 * m.m33
            - m.m11 * m.m23 * m.m32
          )
          | 4 => `(
            let det2Rows34Cols34 := m.m33 * m.m44 - m.m43 * m.m34
            let det2Rows24Cols34 := m.m23 * m.m44 - m.m43 * m.m24
            let det2Rows23Cols34 := m.m23 * m.m34 - m.m33 * m.m24
            let det2Rows14Cols34 := m.m13 * m.m44 - m.m43 * m.m14
            let det2Rows13Cols34 := m.m13 * m.m34 - m.m33 * m.m14
            let det2Rows12Cols34 := m.m13 * m.m24 - m.m23 * m.m14

            m.m11 * (m.m22 * det2Rows34Cols34 - m.m32 * det2Rows24Cols34 + m.m42 * det2Rows23Cols34)
            - m.m21 * (m.m12 * det2Rows34Cols34 - m.m32 * det2Rows14Cols34 + m.m42 * det2Rows13Cols34)
            + m.m31 * (m.m12 * det2Rows24Cols34 - m.m22 * det2Rows14Cols34 + m.m42 * det2Rows12Cols34)
            - m.m41 * (m.m12 * det2Rows23Cols34 - m.m22 * det2Rows13Cols34 + m.m32 * det2Rows12Cols34)
          )
          | _ => panic! "unexpected dimensionality"
        )

        /-- The inverse of the matrix. -/
        @[inline]
        def inverse? (m : $mTy) : Option $mTy := $(
          ← match dims.size with
          | 2 => `(
            let det := m.determinant
            if det == 0
              then none
              else
                some <| (1 / det) • ⟨
                  m.m22, -m.m12,
                  -m.m21, m.m11
                ⟩
          )
          | 3 => `(
            let c1 := m.column1
            let c2 := m.column2
            let c3 := m.column3
            let «2×3» := c2.cross c3
            let det := c1.dot «2×3»
            if det == 0
              then none
              else
                let «3×1» := c3.cross c1
                let «1×2» := c1.cross c2
                some <| (1 / det) • ofRows «2×3» «3×1» «1×2»
          )
          | 4 => `(
            let s0 := m.m11 * m.m22 - m.m21 * m.m12
            let s1 := m.m11 * m.m23 - m.m21 * m.m13
            let s2 := m.m11 * m.m24 - m.m21 * m.m14
            let s3 := m.m12 * m.m23 - m.m22 * m.m13
            let s4 := m.m12 * m.m24 - m.m22 * m.m14
            let s5 := m.m13 * m.m24 - m.m23 * m.m14
            let c0 := m.m31 * m.m42 - m.m41 * m.m32
            let c1 := m.m31 * m.m43 - m.m41 * m.m33
            let c2 := m.m31 * m.m44 - m.m41 * m.m34
            let c3 := m.m32 * m.m43 - m.m42 * m.m33
            let c4 := m.m32 * m.m44 - m.m42 * m.m34
            let c5 := m.m33 * m.m44 - m.m43 * m.m34
            let det := s0 * c5 - s1 * c4 + s2 * c3 + s3 * c2 - s4 * c1 + s5 * c0
            if det == 0
              then none
              else
                let detInv := 1 / det
                let detInvNeg := -detInv
                some ⟨
                  (m.m22 * c5 - m.m23 * c4 + m.m24 * c3) * detInv,
                  (m.m12 * c5 - m.m13 * c4 + m.m14 * c3) * detInvNeg,
                  (m.m42 * s5 - m.m43 * s4 + m.m44 * s3) * detInv,
                  (m.m32 * s5 - m.m33 * s4 + m.m34 * s3) * detInvNeg,

                  (m.m21 * c5 - m.m23 * c2 + m.m24 * c1) * detInvNeg,
                  (m.m11 * c5 - m.m13 * c2 + m.m14 * c1) * detInv,
                  (m.m41 * s5 - m.m43 * s2 + m.m44 * s1) * detInvNeg,
                  (m.m31 * s5 - m.m33 * s2 + m.m34 * s1) * detInv,

                  (m.m21 * c4 - m.m22 * c2 + m.m24 * c0) * detInv,
                  (m.m11 * c4 - m.m12 * c2 + m.m14 * c0) * detInvNeg,
                  (m.m41 * s4 - m.m42 * s2 + m.m44 * s0) * detInv,
                  (m.m31 * s4 - m.m32 * s2 + m.m34 * s0) * detInvNeg,

                  (m.m21 * c3 - m.m22 * c1 + m.m23 * c0) * detInvNeg,
                  (m.m11 * c3 - m.m12 * c1 + m.m13 * c0) * detInv,
                  (m.m41 * s3 - m.m42 * s1 + m.m43 * s0) * detInvNeg,
                  (m.m31 * s3 - m.m32 * s1 + m.m33 * s0) * detInv,
                ⟩
          )
          | _ => panic! "unexpected dimensionality"
        )

        /--
        The inverse of the matrix.

        If the matrix is not invertible returns zero matrix
        or panics if debug assertions are enabled.
        -/
        @[inline]
        def inverse (m : $mTy) : $mTy :=
          if let some m' := m.inverse?
            then m'
            else $(
              ← if Term.debugAssertions.get (← getOptions)
                then `(panic! "the matrix is not invertible")
                else pure (mkIdent `zero)
            )
      )
      if dims.size = 4 then
        let v3Ty := cx.structure "Vector3"
        elabCommand <| ← `(
          /--
          Expands the vector to 4th dimension by setting `w` to `1`, multiplies it by a matrix
          (the matrix is on the right).
          The 3D part of the result is divided by the 4th component and returned.

          Given a transformation matrix intended to be used with row vectors,
          the result is the application of the transformation to a point.
          -/
          @[inline]
          def transformPoint (m : $mTy) (p : $v3Ty) : $v3Ty :=
            let ⟨x, y, z, w⟩ := m.row1 * p.x + m.row2 * p.y + m.row3 * p.z + m.row4
            ⟨x / w, y / w, z / w⟩

          /--
          Expands the vector to 4th dimension by setting `w` to `1`, multiplies it by a matrix
          (the matrix is on the right).
          The 3D part of the result is returned.

          Given an affine transformation matrix intended to be used with row vectors,
          the result is the application of the transformation to a point.
          Examples of affine transformations include translation, scaling, rotation,
          reflection, shear, homothety, hyperbolic rotation and compositions of them in any combination and sequence.

          Panics in debug if the 4th column of the matrix is not `⟨0, 0, 0, 1⟩`
          (the transformation is not affine).
          -/
          @[inline]
          def transformPointAffine (m : $mTy) (p : $v3Ty) : $v3Ty :=
            debug_assert! m.m14 == 0 && m.m24 == 0 && m.m34 == 0 && m.m44 == 1
            let ⟨x, y, z, w⟩ := m.row1 * p.x + m.row2 * p.y + m.row3 * p.z + m.row4
            ⟨x, y, z⟩

          /--
          Expands the vector to 4th dimension by setting `w` to `0`, multiplies it by a matrix
          (the matrix is on the right).
          The 3D part of the result is returned.

          Given an affine transformation matrix intended to be used with row vectors,
          the result is the application of the rotation part of the transformation to a direction.
          Examples of affine transformations include translation, scaling, rotation,
          reflection, shear, homothety, hyperbolic rotation and compositions of them in any combination and sequence.

          Panics in debug if the 4th column of the matrix is not `⟨0, 0, 0, 1⟩`
          (the transformation is not affine).
          -/
          @[inline]
          def transformDirection (m : $mTy) (p : $v3Ty) : $v3Ty :=
            debug_assert! m.m14 == 0 && m.m24 == 0 && m.m34 == 0 && m.m44 == 1
            let ⟨x, y, z, w⟩ := m.row1 * p.x + m.row2 * p.y + m.row3 * p.z
            ⟨x, y, z⟩
        )
      elabCommand <| ← `(
        end $mTy
      )
