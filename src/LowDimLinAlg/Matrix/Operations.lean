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
      let smallVTy := cx.structure <| "Vector" ++ toString (dims.size - 1)
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

        @[inline] instance : Inv $mTy := ⟨inverse⟩
      )
      if dims.size > 2 then
        elabCommand <| ← `(
          /--
          Checks whether the last column of the matrix is all zeros except the last element which is 1.

          Returns true for matrices representing affine transformations and intended to be used with **row vectors**.
          -/
          @[inline]
          def isAffine (m : $mTy) : Bool :=
            $(foldBinopL dims ``and fun i =>
              app ``BEq.beq #[
                mget `m i dims.back!,
                if i.index < dims.size - 1 then lit0 else lit1
              ]
            )

          /--
          Extends the provided vector with '0' and adds it to the last row of the matrix.

          For a transformation matrix intended to be used with **row vectors**,
          the result applies translation **after** the original transformation.

          Panics in debug if the last column of the matrix is
          not all zeros except the last component, or if the last component is not 1
          (the transformation is not **affine**).
          -/
          @[inline]
          def translate (t : $smallVTy) (m : $mTy) : $mTy :=
            debug_assert! m.isAffine
            ⟨$(dims.flatMap fun i =>
              dims.map fun j =>
                if i.index + 1 < dims.size || j.index + 1 == dims.size
                  then (mget `m i j : Term)
                  else app ``Add.add #[mget `m i j, vget `t j]
            ):term,*⟩

          /--
          Applies translation **before** the original transformation to
          a transformation matrix intended to be used with **row vectors**.

          Panics in debug if the last column of the matrix is
          not all zeros except the last component, or if the last component is not 1
          (the transformation is not **affine**).
          -/
          @[inline]
          def translateBefore (t : $smallVTy) (m : $mTy) : $mTy :=
            debug_assert! m.isAffine
            ⟨$(dims.flatMap fun i =>
              dims.map fun j =>
                if i.index + 1 < dims.size || j.index + 1 == dims.size
                  then (mget `m i j : Term)
                  else
                    foldBinopL dims ``Add.add fun k =>
                      let m := mget `m k j
                      if k.index + 1 < dims.size
                        then app ``Mul.mul #[vget `t k, m]
                        else m
            ):term,*⟩

          /--
          Multiplies each column of the matrix with a component of a vector,
          leaving the last column unaffected.

          For a transformation matrix intended to be used with **row vectors**,
          the result applies scaling **after** the original transformation.

          Panics in debug if the last column of the matrix is
          not all zeros except the last component, or if the last component is not 1
          (the transformation is not **affine**).
          -/
          @[inline]
          def scale (s : $smallVTy) (m : $mTy) : $mTy :=
            debug_assert! m.isAffine
            ofColumns $(dims.map fun j =>
              let column := dot `m s!"column{j.index + 1}"
              if j.index + 1 < dims.size
                then app ``SMul.smul #[vget `s j, column]
                else column
            ):term*

          /--
          Multiplies each matrix row with a component of a vector,
          leaving the last row unaffected.

          For a transformation matrix intended to be used with **row vectors**,
          the result applies scaling **before** the original transformation.

          Panics in debug if the last column of the matrix is
          not all zeros except the last component, or if the last component is not 1
          (the transformation is not **affine**).
          -/
          @[inline]
          def scaleBefore (s : $smallVTy) (m : $mTy) : $mTy :=
            debug_assert! m.isAffine
            ofRows $(dims.map fun i =>
              let row := dot `m s!"row{i.index + 1}"
              if i.index + 1 < dims.size
                then app ``SMul.smul #[vget `s i, row]
                else row
            ):term*

          @[inline]
          def transformPointAffine (m : $mTy) (p : $smallVTy) : $smallVTy :=
            debug_assert! m.isAffine
            let p' := $(
              foldBinopL dims ``Add.add fun i =>
                let row := dot `m s!"row{i.index + 1}"
                if i.index < dims.size - 1 then app ``SMul.smul #[vget `p i, row] else row
            )
            ⟨$(dims.take (dims.size - 1) |>.map <| vget `p'):term,*⟩

          @[inline]
          def transformDirection (m : $mTy) (p : $smallVTy) : $smallVTy :=
            debug_assert! m.isAffine
            let p' := $(
              foldBinopL (dims.take (dims.size - 1)) ``Add.add fun i =>
                app ``SMul.smul #[vget `p i, dot `m s!"row{i.index + 1}"]
            )
            ⟨$(dims.take (dims.size - 1) |>.map <| vget `p'):term,*⟩
        )
        let if4 {α} := @cond α (dims.size == 4)
        let applyDocTransformAffine (fn : Name) (isDir : Bool) : CommandElabM Unit := do
          addDocStringCore (← resolveGlobalConstNoOverload <| mkIdent fn) <|
            s!" Expands the vector to {if4 "4th" "3rd"} dimension by setting `{if4 'w' 'z'}` to `{cond isDir '0' '1'}`, multiplies it by a matrix"
            ++ " (the matrix is on the right)."
            ++ s!" The {if4 '3' '2'}D part of the result is returned.\n"
            ++ "\n"
            ++ " Given an **affine** transformation matrix intended to be used with **row vectors**,"
            ++ s!" the result is the application of the rotation part of the transformation to a {cond isDir "direction" "point"}."
            ++ " Examples of affine transformations include translation, scaling, rotation,"
            ++ " reflection, shear, homothety, hyperbolic rotation and compositions of them in any combination and sequence.\n"
            ++ "\n"
            ++ s!" Panics in debug if the {if4 "4th" "3rd"} column of the matrix is not `⟨0, 0, {if4 "0, " ""}1⟩`"
            ++ " (the transformation is not **affine**)."
        applyDocTransformAffine `transformPointAffine false
        applyDocTransformAffine `transformDirection true
      if dims.size = 3 then
        elabCommand <| ← `(
          /--
          Applies rotation **after** the original transformation to
          a transformation matrix intended to be used with **row vectors**.

          The rotation is "from X to Y", i.e. counterclockwise if X is right and Y is up.

          Panics in debug if the 3rd column of the matrix is not `⟨0, 0, 1⟩`
          (the transformation is not **affine**).
          -/
          @[inline]
          def rotate (angle : $sTy) (m : $mTy) : $mTy :=
            debug_assert! m.isAffine
            let sin := angle.sin
            let cos := angle.cos
            ⟨
              m.m11 * cos - m.m12 * sin, m.m11 * sin + m.m12 * cos, 0,
              m.m21 * cos - m.m22 * sin, m.m21 * sin + m.m22 * cos, 0,
              m.m31 * cos - m.m32 * sin, m.m31 * sin + m.m32 * cos, 1,
            ⟩

          /--
          Applies rotation **before** the original transformation to
          a transformation matrix intended to be used with **row vectors**.

          The rotation is "from X to Y", i.e. counterclockwise if X is right and Y is up.

          Panics in debug if the 3rd column of the matrix is not `⟨0, 0, 1⟩`
          (the transformation is not **affine**).
          -/
          @[inline]
          def rotateBefore (angle : $sTy) (m : $mTy) : $mTy :=
            debug_assert! m.isAffine
            let sin := angle.sin
            let cos := angle.cos
            let sinNeg := -sin
            ⟨
              m.m11 * cos + m.m21 * sin, m.m12 * cos + m.m22 * sin, 0,
              m.m11 * sinNeg + m.m21 * cos, m.m12 * sinNeg + m.m22 * cos, 0,
              m.m31, m.m32, 1,
            ⟩
        )
      if dims.size = 4 then
        elabCommand <| ← `(
          /--
          Expands the vector to 4th dimension by setting `w` to `1`, multiplies it by a matrix
          (the matrix is on the right).
          The 3D part of the result is divided by the 4th component and returned.

          Given a transformation matrix intended to be used with **row vectors**,
          the result is the application of the transformation to a point.
          -/
          @[inline]
          def transformPoint (m : $mTy) (p : $smallVTy) : $smallVTy :=
            let ⟨x, y, z, w⟩ := m.row1 * p.x + m.row2 * p.y + m.row3 * p.z + m.row4
            ⟨x / w, y / w, z / w⟩
        )
      elabCommand <| ← `(
        end $mTy
      )
