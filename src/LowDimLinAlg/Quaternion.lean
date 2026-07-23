module

public import LowDimLinAlg.Vector.Floats

import LowDimLinAlg.Internal.Scalars

@[expose] public section

set_option hygiene false
set_option debugAssertions true -- TODO: delete

namespace LowDimLinAlg

run_cmd
  Internal.scalars.forM fun cx => do
    if !cx.isFloat then return
    let sTy := cx.scalarType
    let qTy := cx.structure "Quaternion"
    let v3Ty := cx.structure "Vector3"
    let v4Ty := cx.structure "Vector4"
    Lean.Elab.Command.elabCommand <| ← `(
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
      -/
      @[inline]
      def ofScaledAxis (axis : $v3Ty) : $qTy :=
        let len := axis.length
        if len == 0.0
          then identity
          else ofAxisAngle (axis / len) len

      /-- Creates a quaternion from an angle around the X axis. -/
      @[inline]
      def ofAngleX (angle : $sTy) : $qTy :=
        let angle := angle * 0.5
        ⟨angle.sin, 0, 0, angle.cos⟩

      /-- Creates a quaternion from an angle around the Y axis. -/
      @[inline]
      def ofAngleY (angle : $sTy) : $qTy :=
        let angle := angle * 0.5
        ⟨0, angle.sin, 0, angle.cos⟩

      /-- Creates a quaternion from an angle around the Z axis. -/
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
        if m22 <= 2 then
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
        2 * q.w.abs.acos < 2.827_296_549_232_347_4e-7

      /--
      The conjugate of the quaternion.
      For a unit quaternion the conjugate is also the inverse.
      -/
      @[inline]
      def conjugate (q : $qTy) : $qTy :=
        ⟨-q.x, -q.y, -q.z, q.w⟩

      /--
      The inverse of a normalized quaternion.

      Panics in debug if the quaternion is not normalized.
      -/
      @[inline]
      def inverse (q : $qTy) : $qTy :=
        debug_assert! q.isNormalized
        q.conjugate

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

      /--
      Multiplies a quaternion and a 3D vector, returning the rotated vector.

      Panics in debug if the quaternion is not normalized.
      -/
      @[inline]
      def mulVector3 (q : $qTy) (v : $v3Ty) : $v3Ty :=
        debug_assert! q.isNormalized
        let u := q.vector
        v * (q.w * q.w - u.dot u) + 2 * u.dot v * u + 2 * q.w * u.cross v

      @[inline] instance : Neg $qTy := ⟨neg⟩
      @[inline] instance : SMul $sTy $qTy := ⟨smul⟩
      @[inline] instance : Mul $qTy := ⟨mul⟩
      @[inline] instance : HMul $qTy $v3Ty $v3Ty := ⟨mulVector3⟩

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
            q1.toVector4 * (1 - t) + q2.toVector4 * t

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
        if dot > 1 - $(cx.scalarExtMember "epsilon")
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
        if dot > 1 - $(cx.scalarExtMember "epsilon")
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
    )

/-- Converts quaternion components to `Float`. -/
@[inline]
def F32Quaternion.toF64 (q : F32Quaternion) : F64Quaternion :=
  ⟨q.x.toFloat, q.y.toFloat, q.z.toFloat, q.w.toFloat⟩

/-- Converts quaternion components to `Float32`. -/
@[inline]
def F64Quaternion.toF32 (q : F64Quaternion) : F32Quaternion :=
  ⟨q.x.toFloat32, q.y.toFloat32, q.z.toFloat32, q.w.toFloat32⟩
