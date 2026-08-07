module

public import LowDimLinAlg.Vector.Floats
public import LowDimLinAlg.Vector.Swizzling
public import LowDimLinAlg.Matrix

meta import LowDimLinAlg.Internal.Scalars

@[expose] public section

set_option hygiene false

namespace LowDimLinAlg

open Lean Elab Command

run_cmd
  Internal.floats.forM fun cx => do
    let sTy : Ident := cx.scalarType
    let qTy : Ident := cx.structure "Quaternion"
    let v3Ty : Ident := cx.structure "Vector3"
    let v4Ty : Ident := cx.structure "Vector4"
    let m3Ty : Ident := cx.structure "Matrix3"
    let m4Ty : Ident := cx.structure "Matrix4"
    let sEpsilon := cx.scalarExtMember "epsilon"
    let sPi := cx.scalarExtMember "pi"
    elabCommand <| ← `(
      structure $qTy:ident where
        x : $sTy
        y : $sTy
        z : $sTy
        w : $sTy
      deriving BEq, Repr, Inhabited

      namespace $qTy

      /-- The vector part of the quaternion. -/
      @[inline]
      def vector (q : $qTy) : $v3Ty :=
        { q with }

      /-- The scalar part of the quaternion. -/
      abbrev scalar : $qTy → $sTy :=
        w

      /-- The identity quaternion. Corresponds to no rotation. -/
      @[inline]
      def identity : $qTy := ⟨0, 0, 0, 1⟩

      /-- Creates a quaternion with components taken from a vector. -/
      @[inline]
      def ofVector4 (v : $v4Ty) : $qTy :=
        { v with }

      /--
      Creates a quaternion from an axis and an angle.

      In a right-handed coordinate system the rotation is clockwise
      when the axis is the view direction.

      Panics in debug if the axis is not normalized.
      -/
      @[inline]
      def ofAxisAngle (axis : $v3Ty) (angle : $sTy) : $qTy :=
        debug_assert! axis.isNormalized
        let angle := 0.5 * angle
        let v := angle.sin * axis
        { v with w := angle.cos }

      /--
      Creates a quaternion from a rotation vector.
      Normalized vector is used as an axis and its length as an angle.

      In a right-handed coordinate system the rotation is clockwise
      when the axis is the view direction.
      -/
      @[inline]
      def ofScaledAxis (axis : $v3Ty) : $qTy :=
        let len := axis.length
        if len == 0.0
          then identity
          else ofAxisAngle (axis / len) len

      /--
      Creates a quaternion from an angle around the X axis.

      In a right-handed coordinate system the rotation is clockwise
      when the axis is the view direction.
      -/
      @[inline]
      def ofAngleX (angle : $sTy) : $qTy :=
        let angle := angle * 0.5
        ⟨angle.sin, 0, 0, angle.cos⟩

      /--
      Creates a quaternion from an angle around the Y axis.

      In a right-handed coordinate system the rotation is clockwise
      when the axis is the view direction.
      -/
      @[inline]
      def ofAngleY (angle : $sTy) : $qTy :=
        let angle := angle * 0.5
        ⟨0, angle.sin, 0, angle.cos⟩

      /--
      Creates a quaternion from an angle around the Z axis.

      In a right-handed coordinate system the rotation is clockwise
      when the axis is the view direction.
      -/
      @[inline]
      def ofAngleZ (angle : $sTy) : $qTy :=
        let angle := angle * 0.5
        ⟨0, 0, angle.sin, angle.cos⟩

      /--
      Creates a quaternion from axes,
      each representing a global axis rotated by the resulting quaternion.

      Note if the input axes contain scales, shears, or other non-rotation transformations then
      the output of this function is ill-defined.

      Panics in debug if any axis is not normalized.
      -/
      @[inline]
      def ofAxes (xAxis yAxis zAxis : $v3Ty) : $qTy :=
        debug_assert! xAxis.isNormalized && yAxis.isNormalized && zAxis.isNormalized
        let ⟨m00, m01, m02⟩ := xAxis
        let ⟨m10, m11, m12⟩ := yAxis
        let ⟨m20, m21, m22⟩ := zAxis
        if m22 <= 0 then
          let dif10 := m11 - m00
          let omm22 := 1 - m22
          if dif10 <= 0 then
            let fourXsq := omm22 - dif10
            let inv4x := 0.5 / fourXsq.sqrt
            ⟨fourXsq * inv4x, (m01 + m10) * inv4x, (m02 + m20) * inv4x, (m12 - m21) * inv4x⟩
          else
            let fourYsq := omm22 + dif10
            let inv4y := 0.5 / fourYsq.sqrt
            ⟨(m01 + m10) * inv4y, fourYsq * inv4y, (m12 + m21) * inv4y, (m20 - m02) * inv4y⟩
        else
          let sum10 := m11 + m00
          let opm22 := 1 + m22
          if sum10 <= 0 then
            let fourZsq := opm22 - sum10
            let inv4z := 0.5 / fourZsq.sqrt
            ⟨(m02 + m20) * inv4z, (m12 + m21) * inv4z, fourZsq * inv4z, (m01 - m10) * inv4z⟩
          else
            let fourWsq := opm22 + sum10
            let inv4w := 0.5 / fourWsq.sqrt
            ⟨(m12 - m21) * inv4w, (m20 - m02) * inv4w, (m01 - m10) * inv4w, fourWsq * inv4w⟩

      /--
      Creates a quaternion representing the minimal rotation for transforming `from` to `to`.
      Chooses the shorter path.

      Panics in debug if either `from` or `to` is not normalized.
      -/
      @[inline]
      def ofFromTo («from» to : $v3Ty) : $qTy :=
        debug_assert! «from».isNormalized && to.isNormalized
        let dot := «from».dot to
        if dot > 1 - 2 * $sEpsilon then
          .identity
        else if dot < -1 + 2 * $sEpsilon then
          .ofAxisAngle «from».anyOrthogonal $sPi
        else
          let cross := «from».cross to
          ofVector4 <| .normalize { cross with w := 1 + dot }

      /--
      Creates a quaternion representing the minimal rotation for transforming `from` to either `to` or `-to`.
      Chooses the shorter path.

      Panics in debug if either `from` or `to` is not normalized.
      -/
      @[inline]
      def ofFromToCollinear («from» to : $v3Ty) : $qTy :=
        if «from».dot to >= 0
          then ofFromTo «from» to
          else ofFromTo «from» (-to)

      /--
      Creates a quaternion from a 3x3 rotation matrix.

      Expects a matrix intended to be used with **row vectors**.

      Note if the input matrix contain scales, shears, or other non-rotation transformations then
      the output of this function is ill-defined.

      Panics in debug if any matrix row is not normalized.
      -/
      @[inline]
      def ofMatrix3 (m : $m3Ty) : $qTy :=
        ofAxes m.xAxis m.yAxis m.zAxis

      /--
      Creates a quaternion from a 3x3 rotation matrix inside a homogeneous 4x4 matrix.

      Expects a matrix intended to be used with **row vectors**.

      Note if the upper 3x3 matrix contain scales, shears, or other non-rotation transformations then
      the output of this function is ill-defined.

      Panics in debug if any row of the upper 3x3 rotation matrix is not normalized.
      -/
      @[inline]
      def ofMatrix4 (m : $m4Ty) : $qTy :=
        ofAxes m.xAxis.xyz m.yAxis.xyz m.zAxis.xyz

      /-- The quaternion components as a vector `⟨x, y, z, w⟩`. -/
      @[inline]
      def toVector4 (q : $qTy) : $v4Ty :=
        { q with }

      /-- Axis and angle of the rotation represented by the quaternion. -/
      @[inline]
      def toAxisAngle (q : $qTy) : $v3Ty × $sTy :=
        let axis : $v3Ty := { q with }
        let sin := axis.length
        if sin >= 1e-8
          then (axis / sin, 2 * $(cx.scalarMember "atan2") sin q.w)
          else (.unitX, 0)

      /-- Axis of the rotation represented by the quaternion scaled by its angle. -/
      @[inline]
      def toScaledAxis (q : $qTy) : $v3Ty :=
        let (axis, angle) := toAxisAngle q
        axis * angle

      /-- The result of rotating X axis by the quaternion. -/
      @[inline]
      def xAxis (q : $qTy) : $v3Ty := ⟨
        1 - 2 * q.y * q.y - 2 * q.z * q.z,
        2 * q.x * q.y + 2 * q.w * q.z,
        2 * q.x * q.z - 2 * q.w * q.y,
      ⟩

      /-- The result of rotating Y axis by the quaternion. -/
      @[inline]
      def yAxis (q : $qTy) : $v3Ty := ⟨
        2 * q.x * q.y - 2 * q.w * q.z,
        1 - 2 * q.x * q.x - 2 * q.z * q.z,
        2 * q.y * q.z + 2 * q.w * q.x,
      ⟩

      /-- The result of rotating Z axis by the quaternion. -/
      @[inline]
      def zAxis (q : $qTy) : $v3Ty := ⟨
        2 * q.x * q.z + 2 * q.w * q.y,
        2 * q.y * q.z - 2 * q.w * q.x,
        1 - 2 * q.x * q.x - 2 * q.y * q.y,
      ⟩

      /-- The results of rotating main axes by the quaternion. -/
      @[inline]
      def axes (q : $qTy) : $v3Ty × $v3Ty × $v3Ty :=
        let q2x := 2 * q.x
        let q2y := 2 * q.y
        let q2z := 2 * q.z
        let q2xx := q2x * q.x
        let q2xy := q2x * q.y
        let q2xz := q2x * q.z
        let q2yy := q2y * q.y
        let q2yz := q2y * q.z
        let q2yw := q2y * q.w
        let q2xw := q2x * q.w
        let q2zz := q2z * q.z
        let q2zw := q2z * q.w
        (
          ⟨
            1 - q2yy - q2zz,
            q2xy + q2zw,
            q2xz - q2yw,
          ⟩,
          ⟨
            q2xy - q2zw,
            1 - q2xx - q2zz,
            q2yz + q2xw,
          ⟩,
          ⟨
            q2xz + q2yw,
            q2yz - q2xw,
            1 - q2xx - q2yy,
          ⟩,
        )


      /--
      Converts the quaternion to a 3x3 rotation matrix.

      The resulting matrix must be used with **row vectors**,
      e.g. when multiplying a vector by the matrix the vector must be on the left.
      -/
      @[inline]
      def toMatrix3 (q : $qTy) : $m3Ty :=
        let (x, y, z) := q.axes
        .ofAxes x y z

      /--
      Converts the quaternion to a 4x4 homogeneous matrix.

      The resulting matrix must be used with **row vectors**,
      e.g. when multiplying a vector by the matrix the vector must be on the left.
      -/
      @[inline]
      def toMatrix4 (q : $qTy) : $m4Ty :=
        let (x, y, z) := q.axes
        .ofAxes { x with w := 0 } { y with w := 0 } { z with w := 0 } ⟨0, 0, 0, 1⟩

      /--
      Dot product of two quaternions.
      It is equal to the cosine of the angle between two quaternion rotations.
      -/
      @[inline]
      def dot (q1 q2 : $qTy) : $sTy :=
        q1.toVector4.dot q2.toVector4

      /-- The length of the quaternion. -/
      @[inline]
      def length (q : $qTy) : $sTy :=
        q.toVector4.length

      /-- The squared length of the quaternion. -/
      @[inline]
      def lengthSqr (q : $qTy) : $sTy :=
        q.toVector4.lengthSqr

      /--
      Normalizes the quaternion to the length of `1`.

      Panics in debug if any component of `q/|q|` is not finite.
      -/
      @[inline]
      def normalize (q : $qTy) : $qTy :=
        .ofVector4 q.toVector4.normalize

      /--
      Whether the length of the quaternion is 1.
      -/
      @[inline]
      def isNormalized (q : $qTy) : Bool :=
        q.toVector4.isNormalized

      /-- Whether the quaternion rotation angle is roughly equal to zero. -/
      @[inline]
      def isNearIdentity (q : $qTy) : Bool :=
        2 * q.w.abs.acos <
          $(if cx.scalarTypeName = ``Float
            then Lean.Syntax.mkScientificLit "2.827_296_549_232_347_4e-7"
            else Lean.Syntax.mkScientificLit "0.002_847_144_6")

      /--
      The conjugate of the quaternion.
      For a unit quaternion the conjugate is also the inverse.
      -/
      @[inline]
      def conjugate (q : $qTy) : $qTy :=
        ⟨-q.x, -q.y, -q.z, q.w⟩

      /--
      The inverse of a quaternion.

      If the quaternion is expected to be normalized use `conjugate`.
      -/
      @[inline]
      def inverse (q : $qTy) : $qTy :=
        ofVector4 <| q.conjugate.toVector4 / q.lengthSqr

      /--
      Negates a quaternion.

      The negated quaternion represents the same rotation.
      -/
      @[inline]
      def neg (q : $qTy) : $qTy :=
        ofVector4 q.toVector4.neg

      /-- Multiplies all components of the quaternion by `s`. -/
      @[inline]
      def smul (s : $sTy) (q : $qTy) : $qTy :=
        ofVector4 <| s * q.toVector4

      /--
      Multiplies two quaternions.
      If the arguments represent valid rotations, the result will be the combined rotation.

      Due to floating-point rounding the result may not be perfectly normalized.
      -/
      @[inline]
      def mul (q1 q2 : $qTy) : $qTy := ⟨
        q1.w * q2.x + q1.x * q2.w + q1.y * q2.z - q1.z * q2.y,
        q1.w * q2.y - q1.x * q2.z + q1.y * q2.w + q1.z * q2.x,
        q1.w * q2.z + q1.x * q2.y - q1.y * q2.x + q1.z * q2.w,
        q1.w * q2.w - q1.x * q2.x - q1.y * q2.y - q1.z * q2.z,
      ⟩

      @[inline] instance : Inv $qTy := ⟨inverse⟩
      @[inline] instance : Neg $qTy := ⟨neg⟩
      @[inline] instance : SMul $sTy $qTy := ⟨smul⟩
      @[inline] instance : Mul $qTy := ⟨mul⟩

      /--
      Applies the rotation represented by the quaternion to a vector.

      Some equivalent to, but faster:
      `(·.xyz) <| toVector4 <| (q * · * q.conjugate) <| ofVector4 <| v.withW 0`

      Panics in debug if the quaternion is not normalized.
      -/
      @[inline]
      def apply (q : $qTy) (v : $v3Ty) : $v3Ty :=
        debug_assert! q.isNormalized
        let u := q.vector
        v * (q.w * q.w - u.dot u) + 2 * u.dot v * u + 2 * q.w * u.cross v

      /--
      The angle for the minimal rotation between two quaternions in the range `[0, π]`.

      Panics in debug if either quaternion is not normalized.
      -/
      @[inline]
      def angleBetween (q1 q2 : $qTy) : $sTy :=
        debug_assert! q1.isNormalized && q2.isNormalized
        2 * (q1.dot q2 |>.abs.acos)

      @[always_inline] private
      def lerpImpl (q1 q2 : $qTy) (t : $sTy) : $qTy :=
        normalize <|
          ofVector4 <|
            if t < 0.5
              then q1.toVector4 + (q2.toVector4 - q1.toVector4) * t
              else q2.toVector4 - (q2.toVector4 - q1.toVector4) * (1 - t)

      @[always_inline] private
      def slerpImpl (q1 q2 : $qTy) (dot t : $sTy) : $qTy :=
        let angle := dot.acos
        let t1 := (angle * (1 - t)).sin
        let t2 := (angle * t).sin
        ofVector4 <|
          (t1 * q1.toVector4 + t2 * q2.toVector4) * (1 / angle.sin)

      /--
      Performs a linear interpolation between `start` and `end` based on `t`.

      When `t` is `0`, the result will be `start`.
      When `t` is `1`, the result will be `end`.

      Returns `NaN` if `t`, `start` or `end` is NaN.
      Panics in debug if either `start` or `end` is not normalized or `t` is outside the range `[0, 1]`.
      -/
      @[no_expose]
      def lerp (start «end» : $qTy) (t : $sTy) : $qTy :=
        debug_assert! start.isNormalized && «end».isNormalized && t >= 0 && t <= 1
        lerpImpl start (if start.dot «end» >= 0 then «end» else -«end») t

      /--
      Performs a spherical linear interpolation between `start` and `end` based on `t`.
      Takes the shortest path.

      When `t` is `0`, the result will be `start`.
      When `t` is `1`, the result will be `end`.

      Returns `NaN` if `t`, `start` or `end` is NaN.
      Panics in debug if either `start` or `end` is not normalized or `t` is outside the range `[0, 1]`.
      -/
      @[no_expose]
      def slerpShortest (start «end» : $qTy) (t : $sTy) : $qTy :=
        debug_assert! start.isNormalized && «end».isNormalized && t >= 0 && t <= 1
        let («end», dot) :=
          let dot := start.dot «end»
          if dot < 0
            then (-«end», -dot)
            else («end», dot)
        if dot > 1 - $sEpsilon
          then lerpImpl start «end» t
          else slerpImpl start «end» dot t

      /--
      Performs a spherical linear interpolation between `start` and `end` based on `t`.
      May take the longer path.

      When `t` is `0`, the result will be `start`.
      When `t` is `1`, the result will be `end`.

      Returns `NaN` if `t`, `start` or `end` is NaN.
      Panics in debug if either `start` or `end` is not normalized or `t` is outside the range `[0, 1]`.
      -/
      @[no_expose]
      def slerp (start «end» : $qTy) (t : $sTy) : $qTy :=
        debug_assert! start.isNormalized && «end».isNormalized && t >= 0 && t <= 1
        let dot := start.dot «end»
        if dot > 1 - $sEpsilon
          then lerpImpl start «end» t
          else slerpImpl start «end» dot t

      /--
      Rotates the quaternion towards the target up to `maxRotation` radians.

      Panics in debug if either quaternion is not normalized or `maxRotation` is negative.
      -/
      @[inline]
      def rotateTowards (q target : $qTy) (maxRotation : $sTy) : $qTy :=
        debug_assert! q.isNormalized && target.isNormalized && maxRotation >= 0
        let angle := angleBetween q target
        if angle <= maxRotation
          then target
          else inline slerpShortest q target <| $(cx.scalarExtMember "clamp") (-1) 1 (maxRotation / angle)

      end $qTy

      namespace $m3Ty

      /--
      Creates a rotation matrix from a quaternion.

      The resulting matrix must be used with **row vectors**,
      e.g. when multiplying a vector by the matrix the vector must be on the left.
      -/
      abbrev ofQuaternion (q : $qTy) : $m3Ty := q.toMatrix3

      /--
      Converts the matrix to a quaternion.

      Assumes the matrix is intended to be used with **row vectors** and represents a rotation.
      If the input matrix contain scales, shears, or other non-rotation transformations then
      the output of this function is ill-defined.

      Panics in debug if any matrix row is not normalized.
      -/
      abbrev toQuaternion : $m3Ty → $qTy := .ofMatrix3

      end $m3Ty

      namespace $m4Ty

      /--
      Creates a homogeneous rotation matrix from a quaternion.

      The resulting matrix must be used with **row vectors**,
      e.g. when multiplying a vector by the matrix the vector must be on the left.
      -/
      abbrev ofQuaternion (q : $qTy) : $m4Ty := q.toMatrix4

      /--
      Converts the matrix to a quaternion.

      Assumes the matrix is intended to be used with **row vectors**, is homogeneous and represents a rotation.
      If the upper 3x3 matrix contain scales, shears, or other non-rotation transformations then
      the output of this function is ill-defined.

      Panics in debug if any row of the upper 3x3 rotation matrix is not normalized.
      -/
      abbrev toQuaternion : $m4Ty → $qTy := .ofMatrix4

      end $m4Ty
    )

/-- Converts the quaternion components to `Float` scalar type using `Float32.toFloat`. -/
@[inline]
def F32Quaternion.toF64 (q : F32Quaternion) : F64Quaternion :=
  ⟨q.x.toFloat, q.y.toFloat, q.z.toFloat, q.w.toFloat⟩

/-- Converts the quaternion components from `Float32` scalar type using `Float32.toFloat`. -/
abbrev F64Quaternion.ofF32 := F32Quaternion.toF64

/-- Converts the quaternion components to `Float32` scalar type using `Float.toFloat32`. -/
@[inline]
def F64Quaternion.toF32 (q : F64Quaternion) : F32Quaternion :=
  ⟨q.x.toFloat32, q.y.toFloat32, q.z.toFloat32, q.w.toFloat32⟩

/-- Converts the quaternion components from `Float` scalar type using `Float.toFloat32`. -/
abbrev F32Quaternion.ofF64 := F64Quaternion.toF32
