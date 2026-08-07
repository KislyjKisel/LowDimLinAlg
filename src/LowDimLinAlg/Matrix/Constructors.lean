module

public import LowDimLinAlg.Matrix.Constants
public import LowDimLinAlg.Vector.Floats

meta import LowDimLinAlg.Internal.Dimensionalities
meta import LowDimLinAlg.Internal.Scalars
meta import LowDimLinAlg.Internal.Syntax

@[expose] public section

set_option hygiene false

namespace LowDimLinAlg

open Lean Elab Command
open Internal

run_cmd
  for dims in dimensionalities do
    let dimsSizeStr := toString dims.size
    floats.forM fun cx => do
      let mTy := cx.structure <| "Matrix" ++ dimsSizeStr
      let vTy := cx.structure <| "Vector" ++ dimsSizeStr
      let sTy := cx.scalarType
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

        The resulting matrix must be used with **row vectors**,
        e.g. when multiplying a vector it must be on the left of the matrix.
        Assumes the axes are orthonormal.

        Panics in debug if any axis is not normalized.
        -/
        @[inline]
        def ofAxes ($(dims.map fun dim => dim.ident):ident* : $vTy) : $mTy :=
          debug_assert! $(foldBinopL dims ``Bool.and fun dim => mkIdent <| Name.mkStr2 dim.str "isNormalized")
          ofRows $(dims.map fun dim => dim.ident):ident*

        /-- Creates a diagonal matrix with elements taken from a vector. -/
        @[inline]
        def ofDiagonal (s : $vTy) : $mTy :=
          ⟨$(dims.flatMap fun i =>
            dims.map fun j =>
              if i.index == j.index
                then (vget `s i : Term)
                else lit0
          ):term,*⟩

        /--
        Creates a diagonal matrix with elements taken from a vector.
        The matrix represents a scaling transformation.
        It can be used with both row and column vectors.
        -/
        abbrev ofScale := ofDiagonal
      )
      if dims.size = 2 then
        elabCommand <| ← `(
          /--
          Creates a matrix representing a rotation.

          The matrix is intended to be used with **row vectors**.
          The rotation is "from X to Y", i.e. counterclockwise if X is right and Y is up.
          -/
          @[inline]
          def ofAngle (angle : $sTy) : $mTy :=
            let sin := angle.sin
            let cos := angle.cos
            ⟨cos, sin, -sin, cos⟩
        )
      if dims.size = 3 then
        elabCommand <| ← `(
          /--
          Creates a matrix representing a rotation around X axis.

          The matrix is intended to be used with **row vectors**.
          In a right-handed coordinate system the rotation is clockwise
          when the axis is the view direction.
          -/
          @[inline]
          def ofAngleX (angle : $sTy) : $mTy :=
            let sin := angle.sin
            let cos := angle.cos
            ⟨
              1, 0, 0,
              0, cos, sin,
              0, -sin, cos,
            ⟩

          /--
          Creates a matrix representing a rotation around Y axis.

          The matrix is intended to be used with **row vectors**.
          In a right-handed coordinate system the rotation is clockwise
          when the axis is the view direction.
          -/
          @[inline]
          def ofAngleY (angle : $sTy) : $mTy :=
            let sin := angle.sin
            let cos := angle.cos
            ⟨
              cos, 0, -sin,
              0, 1, 0,
              sin, 0, cos,
            ⟩

          /--
          Creates a matrix representing a rotation around Z axis.

          The matrix is intended to be used with **row vectors**.
          In a right-handed coordinate system the rotation is clockwise
          when the axis is the view direction.
          -/
          @[inline]
          def ofAngleZ (angle : $sTy) : $mTy :=
            let sin := angle.sin
            let cos := angle.cos
            ⟨
              cos, sin, 0,
              -sin, cos, 0,
              0, 0, 1,
            ⟩

          /--
          Creates a rotation matrix from an axis and an angle.

          In a right-handed coordinate system the rotation is clockwise
          when the axis is the view direction.

          Panics in debug if the axis is not normalized.
          -/
          @[inline]
          def ofAxisAngle (axis : $vTy) (angle : $sTy) : $mTy :=
            debug_assert! axis.isNormalized
            let ⟨x, y, z⟩ := axis
            let sin := angle.sin
            let cos := angle.cos
            ⟨
              x * x * (1 - cos) + cos, y * (x * (1 - cos)) + z * sin, z * (x * (1 - cos)) - y * sin,
              y * (x * (1 - cos)) - z * sin, y * y * (1 - cos) + cos, y * z * (1 - cos) + x * sin,
              z * (x * (1 - cos)) + y * sin, y * z * (1 - cos) - x * sin, z * z * (1 - cos) + cos,
            ⟩

          /--
          Creates a rotation matrix from a rotation vector.
          Normalized vector is used as an axis and its length as an angle.

          In a right-handed coordinate system the rotation is clockwise
          when the axis is the view direction.
          -/
          @[inline]
          def ofScaledAxis (axis : $vTy) : $mTy :=
            let len := axis.length
            if len == 0.0
              then identity
              else ofAxisAngle (axis / len) len
        )
      if dims.size > 2 then
        let smallDimsSize := dims.size - 1
        let smallVTy := cx.structure s!"Vector{smallDimsSize}"
        elabCommand <| ← `(
          @[inline]
          def ofTranslation (t : $smallVTy) : $mTy :=
            ⟨$(dims.flatMap fun i =>
              dims.map fun j =>
                if i.index < smallDimsSize || j.index == smallDimsSize
                  then if i == j then (lit1 : Term) else lit0
                  else vget `t j
            ):term,*⟩
        )
        addDocStringCore (← resolveGlobalConstNoOverload <| mkIdent `ofTranslation) <|
          s!"Creates a matrix representing a {smallDimsSize}D translation.\n"
          ++ "\n"
          ++ "The matrix is intended to be used with **row vectors**."
      elabCommand <| ← `(end $mTy)
      if dims.size < 4 then
        let bigMTy : Ident := cx.structure s!"Matrix{dims.size + 1}"
        let ofBigFn := mkIdent <| mTy.getId.str s!"ofMatrix{dims.size + 1}"
        elabCommand <| ← `(
          /-- Creates a matrix from a bigger matrix by discarding its last row and column. -/
          @[inline]
          def $ofBigFn (m : $bigMTy) : $mTy :=
            ⟨$(dims.flatMap fun i => dims.map fun j => mget `m i j):term,*⟩

          /-- Converts the matrix to a smaller matrix by discarding last row and column. -/
          abbrev $(mkIdent <| bigMTy.getId.str s!"toMatrix{dimsSizeStr}") := $ofBigFn
        )
      if dims.size > 2 then
        let smallDimsSize := dims.size - 1
        let smallMTy : Ident := cx.structure s!"Matrix{smallDimsSize}"
        let ofSmallTransformFn := mkIdent <| mTy.getId.str s!"ofMatrix{smallDimsSize}"
        elabCommand <| ← `(
          @[inline]
          def $ofSmallTransformFn (m : $smallMTy) : $mTy :=
            ⟨$(dims.flatMap fun i =>
              dims.map fun j =>
                if i.index < smallDimsSize && j.index < smallDimsSize
                  then (mget `m i j : Term)
                  else if i.index == smallDimsSize && j.index == smallDimsSize
                    then lit1
                    else lit0
            ):term,*⟩
        )
        addDocStringCore (← resolveGlobalConstNoOverload ofSmallTransformFn) <|
          "Creates an affine transformation matrix from a smaller transformation matrix"
          ++ " by extending it with zeros and setting the last element to `1`.\n"
          ++ "\n"
          ++ "The result can be used with points and directions represented as"
          ++ " vectors of the lower dimension via"
          ++ s!" `LowDimLinAlg.{mTy.getId}.transformPointAffine` and `LowDimLinAlg.{mTy.getId}.transformDirection`.\n"
        elabCommand <| ← `(
          @[inherit_doc $ofSmallTransformFn]
          abbrev $(mkIdent <| smallMTy.getId.str s!"toMatrix{dims.size}") := $ofSmallTransformFn
        )
