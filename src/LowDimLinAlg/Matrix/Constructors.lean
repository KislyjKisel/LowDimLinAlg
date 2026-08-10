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

          /--
          Creates a view matrix given a view direction and an upward vector.
          Transforms right-handed world space points into right-handed **Z-up** view space.

          The resulting matrix is intended to be used with row vectors.

          Panics in debug if either direction or up vector is not normalized.
          -/
          @[inline]
          def lookTo (up dir : $vTy) : $mTy :=
            debug_assert! dir.isNormalized && up.isNormalized
            let right := dir.cross up |>.normalize
            let up' := right.cross dir
            ⟨
              right.x, dir.x, up'.x,
              right.y, dir.y, up'.y,
              right.z, dir.z, up'.z,
            ⟩

          /--
          Creates a view matrix given an eye position, a target position and an upward vector.
          Transforms right-handed world space points into right-handed **Z-up** view space.

          The resulting matrix is intended to be used with row vectors.
          It does not contain translation.

          Panics in debug if up vector is not normalized or
          the distance between eye and target is zero.
          -/
          @[inline]
          def lookAt (up eye target : $vTy) : $mTy :=
            lookTo up (target - eye).normalize
        )
      if dims.size = 4 then
        let v3Ty := cx.structure "Vector3"
        elabCommand <| ← `(
          /--
          Creates a view matrix given an eye position, a view direction and upward vector.
          Transforms right-handed world space points into right-handed **Z-up** view space.

          The resulting matrix is intended to be used with row vectors.

          Panics in debug if either direction or up vector is not normalized.
          -/
          @[inline]
          def lookTo (up eye dir : $v3Ty) : $mTy :=
            debug_assert! dir.isNormalized && up.isNormalized
            let right := dir.cross up |>.normalize
            let up' := right.cross dir
            ⟨
              right.x, dir.x, up'.x, 0,
              right.y, dir.y, up'.y, 0,
              right.z, dir.z, up'.z, 0,
              -(eye.dot right), -(eye.dot dir), -(eye.dot up'), 1,
            ⟩

          /--
          Creates a view matrix given an eye position, a target position and an upward vector.
          Transforms right-handed world space points into right-handed **Z-up** view space.

          The resulting matrix is intended to be used with row vectors.

          Panics in debug if up vector is not normalized or
          the distance between eye and target is zero.
          -/
          @[inline]
          def lookAt (up eye target : $v3Ty) : $mTy :=
            lookTo up eye (target - eye).normalize

          /--
          Creates a perspective projection matrix from a frustum.

          Expects a right-handed Z-up view space input with +Y forward.
          Outputs NDC with Z in [-1, 1] and Y-up.
          The resulting matrix is intended to be used with row vectors.
          For a left-handed Z-up view space with -Y forward flip the sign of the 2nd row.

          Panics in debug if `left` and `right` or `top` and `bottom` are equal,
          if near is not positive, or if `far` is not greater than `near`.
          -/
          @[inline]
          def frustumSymDepth (left right bottom top near far : $sTy) : $mTy :=
            debug_assert! near > 0
            debug_assert! far > near
            debug_assert! right != left
            debug_assert! top != bottom
            let invRL := 1 / (right - left)
            let invTB := 1 / (top - bottom)
            let invFN := 1 / (far - near)
            let ax := 2 * near * invRL
            let ay := 2 * near * invTB
            let cx := -(right + left) * invRL
            let cy := -(top + bottom) * invTB
            let dz := (far + near) * invFN
            let tz := -(2 * far * near * invFN)
            ⟨
              ax, 0, 0, 0,
              cx, cy, dz, 1,
              0, ay, 0, 0,
              0, 0, tz, 0,
            ⟩

          /--
          Creates a perspective projection matrix from a frustum.

          Expects a right-handed Z-up view space input with +Y forward.
          Outputs NDC with Z in [0, 1] and Y-up.
          The resulting matrix is intended to be used with row vectors.
          For a left-handed Z-up view space with -Y forward flip the sign of the 2nd row.

          Panics in debug if `left` and `right` or `top` and `bottom` are equal,
          if `near` is not positive, or if `far` is not greater than `near`.
          -/
          @[inline]
          def frustumPosDepth (left right bottom top near far : $sTy) : $mTy :=
            debug_assert! near > 0
            debug_assert! far > near
            debug_assert! right != left
            debug_assert! top != bottom
            let invRL := 1 / (right - left)
            let invTB := 1 / (top - bottom)
            let invFN := 1 / (far - near)
            let ax := 2 * near * invRL
            let ay := 2 * near * invTB
            let cx := -(right + left) * invRL
            let cy := -(top + bottom) * invTB
            let dz := far * invFN
            let tz := -(far * near * invFN)
            ⟨
              ax, 0, 0, 0,
              cx, cy, dz, 1,
              0, ay, 0, 0,
              0, 0, tz, 0,
            ⟩

          /--
          Creates a symmetric perspective projection matrix.

          Expects a right-handed Z-up view space input with +Y forward.
          Outputs NDC with Z in [-1, 1] and Y-up.
          The resulting matrix is intended to be used with row vectors.
          For a left-handed Z-up view space with -Y forward flip the sign
          of `m23` and `m24` or of the 2nd row.

          Panics in debug if `fovY` or `aspect` is not positive,
          if `near` is not positive, or if `far` is not greater than `near`.
          -/
          @[inline]
          def perspectiveSymDepth (fovY aspect near far : $sTy) : $mTy :=
            debug_assert! near > 0
            debug_assert! far > near
            debug_assert! fovY > 0
            debug_assert! aspect > 0
            let tanHalfFov := (fovY * 0.5).tan
            let ⟨sx, sy⟩ := (1 / (aspect * tanHalfFov), 1 / tanHalfFov)
            let invFN := 1 / (far - near)
            let dz := (far + near) * invFN
            let tz := -(2 * far * near * invFN)
            ⟨
              sx, 0, 0, 0,
              0, 0, dz, 1,
              0, sy, 0, 0,
              0, 0, tz, 0,
            ⟩

          /--
          Creates a symmetric perspective projection matrix.

          Expects a right-handed Z-up view space input with +Y forward.
          Outputs NDC with Z in [0, 1] and Y-up.
          The resulting matrix is intended to be used with row vectors.
          For a left-handed Z-up view space with -Y forward flip the sign
          of `m23` and `m24` or of the 2nd row.

          Panics in debug if `fovY` or `aspect` is not positive,
          if `near` is not positive, or if `far` is not greater than `near`.
          -/
          @[inline]
          def perspectivePosDepth (fovY aspect near far : $sTy) : $mTy :=
            debug_assert! near > 0
            debug_assert! far > near
            debug_assert! fovY > 0
            debug_assert! aspect > 0
            let tanHalfFov := (fovY * 0.5).tan
            let ⟨sx, sy⟩ := (1 / (aspect * tanHalfFov), 1 / tanHalfFov)
            let invFN := 1 / (far - near)
            let dz := far * invFN
            let tz := -(far * near * invFN)
            ⟨
              sx, 0, 0, 0,
              0, 0, dz, 1,
              0, sy, 0, 0,
              0, 0, tz, 0,
            ⟩

          /--
          Creates a symmetric perspective projection matrix
          with an infinite far plane.

          Expects a right-handed Z-up view space input with +Y forward.
          Outputs NDC with Z in [-1, 1] and Y-up.
          The resulting matrix is intended to be used with row vectors.
          For a left-handed Z-up view space with -Y forward flip the sign
          of `m23` and `m24` or of the 2nd row.

          Panics in debug if `fovY` or `aspect` is not positive,
          or if `near` is not positive.
          -/
          @[inline]
          def perspectiveInfSymDepth (fovY aspect near : $sTy) : $mTy :=
            debug_assert! (near > 0)
            debug_assert! fovY > 0
            debug_assert! aspect > 0
            let tanHalfFov := (fovY * 0.5).tan
            let ⟨sx, sy⟩ := (1 / (aspect * tanHalfFov), 1 / tanHalfFov)
            let tz := -(2 * near)
            ⟨
              sx, 0, 0, 0,
              0, 0, 1, 1,
              0, sy, 0, 0,
              0, 0, tz, 0,
            ⟩

          /--
          Creates a symmetric perspective projection matrix
          with an infinite far plane.

          Expects a right-handed Z-up view space input with +Y forward.
          Outputs NDC with Z in [0, 1] and Y-up.
          The resulting matrix is intended to be used with row vectors.
          For a left-handed Z-up view space with -Y forward flip the sign
          of `m23` and `m24` or of the 2nd row.

          Panics in debug if `fovY` or `aspect` is not positive,
          or if `near` is not positive.
          -/
          @[inline]
          def perspectiveInfPosDepth (fovY aspect near : $sTy) : $mTy :=
            debug_assert! (near > 0)
            debug_assert! fovY > 0
            debug_assert! aspect > 0
            let tanHalfFov := (fovY * 0.5).tan
            let ⟨sx, sy⟩ := (1 / (aspect * tanHalfFov), 1 / tanHalfFov)
            let tz := -near
            ⟨
              sx, 0, 0, 0,
              0, 0, 1, 1,
              0, sy, 0, 0,
              0, 0, tz, 0,
            ⟩

          /--
          Creates a symmetric perspective projection matrix
          with an infinite far plane and reversed depth.

          Expects a right-handed Z-up view space input with +Y forward.
          Outputs NDC with Z in [-1, 1] and Y-up, with near mapped to 1 and far mapped
          to -1 in the infinite-far limit.
          The resulting matrix is intended to be used with row vectors.
          For a left-handed Z-up view space with -Y forward flip the sign
          of `m23` and `m24` or of the 2nd row.

          Panics in debug if `fovY` or `aspect` is not positive,
          or if `near` is not positive.
          -/
          @[inline]
          def perspectiveInfRevSymDepth (fovY aspect near : $sTy) : $mTy :=
            debug_assert! (near > 0)
            debug_assert! fovY > 0
            debug_assert! aspect > 0
            let tanHalfFov := (fovY * 0.5).tan
            let ⟨sx, sy⟩ := (1 / (aspect * tanHalfFov), 1 / tanHalfFov)
            let tz := 2 * near
            ⟨
              sx, 0, 0, 0,
              0, 0, -1, 1,
              0, sy, 0, 0,
              0, 0, tz, 0,
            ⟩

          /--
          Creates a symmetric perspective projection matrix
          with an infinite far plane and reversed depth.

          Expects a right-handed Z-up view space input with +Y forward.
          Outputs NDC with Z in [0, 1] and Y-up, with near mapped to 1 and far mapped
          to 0 in the infinite-far limit.
          The resulting matrix is intended to be used with row vectors.
          For a left-handed Z-up view space with -Y forward flip the sign
          of `m23` and `m24` or of the 2nd row.

          Panics in debug if `fovY` or `aspect` is not positive,
          or if `near` is not positive.
          -/
          @[inline]
          def perspectiveInfRevPosDepth (fovY aspect near : $sTy) : $mTy :=
            debug_assert! (near > 0)
            debug_assert! fovY > 0
            debug_assert! aspect > 0
            let tanHalfFov := (fovY * 0.5).tan
            let ⟨sx, sy⟩ := (1 / (aspect * tanHalfFov), 1 / tanHalfFov)
            let tz := near
            ⟨
              sx, 0, 0, 0,
              0, 0, 0, 1,
              0, sy, 0, 0,
              0, 0, tz, 0,
            ⟩

          /--
          Creates an orthographic projection matrix.

          Expects a right-handed Z-up view space input with +Y forward.
          Outputs NDC with Z in [-1, 1] and Y-up.
          The resulting matrix is intended to be used with row vectors.
          For a left-handed Z-up view space with -Y forward flip the sign
          of `m23` or of the 2nd row.

          Panics in debug if the distance between any two opposite sides is zero,
          or if `far` equals `near`.
          -/
          @[inline]
          def orthographicSymDepth (left right bottom top near far : $sTy) : $mTy :=
            debug_assert! right != left
            debug_assert! top != bottom
            debug_assert! far != near
            let invRL := 1 / (right - left)
            let invTB := 1 / (top - bottom)
            let invFN := 1 / (far - near)
            let ax := 2 * invRL
            let ay := 2 * invTB
            let tx := -(right + left) * invRL
            let ty := -(top + bottom) * invTB
            let dz := 2 * invFN
            let tz := -(far + near) * invFN
            ⟨
              ax, 0, 0, 0,
              0, 0, dz, 0,
              0, ay, 0, 0,
              tx, ty, tz, 1,
            ⟩

          /--
          Creates an orthographic projection matrix .

          Expects a right-handed Z-up view space input with +Y forward.
          Outputs NDC with Z in [0, 1] and Y-up.
          The resulting matrix is intended to be used with row vectors.
          For a left-handed Z-up view space with -Y forward flip the sign
          of `m23` or of the 2nd row.

          Panics in debug if the distance between any two opposite sides is zero,
          or if `far` equals `near`.
          -/
          @[inline]
          def orthographicPosDepth (left right bottom top near far : $sTy) : $mTy :=
            debug_assert! right != left
            debug_assert! top != bottom
            debug_assert! far != near
            let invRL := 1 / (right - left)
            let invTB := 1 / (top - bottom)
            let invFN := 1 / (far - near)
            let ax := 2 * invRL
            let ay := 2 * invTB
            let tx := -(right + left) * invRL
            let ty := -(top + bottom) * invTB
            let dz := invFN
            let tz := -(near * invFN)
            ⟨
              ax, 0, 0, 0,
              0, 0, dz, 0,
              0, ay, 0, 0,
              tx, ty, tz, 1,
            ⟩
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
