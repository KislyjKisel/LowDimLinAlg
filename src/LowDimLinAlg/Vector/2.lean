module

public import LowDimLinAlg.Axis
public import LowDimLinAlg.Scalar
public import LowDimLinAlg.Vector.Boolean

import LowDimLinAlg.Meta.Scalars

@[expose] public section

set_option hygiene false

namespace LowDimLinAlg

run_cmd
  Meta.scalars.forM fun cx => do
    let sTy := cx.scalarType
    let v2Ty := cx.structure "Vector2"
    Lean.Elab.Command.elabCommand <| ← `(
      namespace $v2Ty


      end $v2Ty
    )

-- run_cmd
--   Meta.forEachScalar Meta.floats fun cx => do
--     let sTy := cx.scalarType
--     let v2Ty := cx.structure "Vector2"
--     let sInf := cx.scalarExtMember "inf"
--     let sNegInf := cx.scalarExtMember "negInf"
--     let sClamp := cx.scalarExtMember "clamp"
--     let sSign := cx.scalarExtMember "sign"
--     let sSqrt := cx.scalarMember "sqrt"
--     let sIsFinite := cx.scalarMember "isFinite"
--     let sAtan2 := cx.scalarMember "atan2"
--     let sAbs := cx.scalarMember "abs"
--     Lean.Elab.Command.elabCommand <| ← `(
--       namespace $v2Ty

--       deriving instance BEq for $v2Ty

--       /-- All components set to NaN. -/
--       @[inline]
--       def nan : $v2Ty := splat (0 / 0)

--       /-- All components set to positive infinity. -/
--       @[inline]
--       def inf : $v2Ty := splat $sInf

--       /-- All components set to negative infinity. -/
--       @[inline]
--       def negInf : $v2Ty := splat $sNegInf

--       /--
--       Creates a unit vector from `angle`.

--       Angle is counterclockwise if Y is up and X is down.
--       -/
--       @[inline]
--       def fromAngle (angle : $sTy) : $v2Ty :=
--         ⟨angle.cos, angle.sin⟩

--       /--
--       Creates a vector from `length` and `angle`.

--       Angle is counterclockwise if Y is up and X is down.
--       -/
--       @[inline]
--       def fromLengthAngle (length angle : $sTy) : $v2Ty :=
--         length * fromAngle angle

--       /--
--       Componentwise clamping of components.

--       Panics in debug if for any axis `min` > `max`, `min` is NaN, or `max` is NaN.
--       -/
--       @[inline]
--       def clamp (min max v : $v2Ty) : $v2Ty :=
--         ⟨$sClamp min.x max.x v.x, $sClamp min.y max.y v.y⟩

--       /-- Componentwise sign (does not return zeros). -/
--       @[inline]
--       def sign (v : $v2Ty) : $v2Ty :=
--         ⟨$sSign v.x, $sSign v.y⟩

--       /-- Vector length. -/
--       @[inline]
--       def length (v : $v2Ty) : $sTy :=
--         $sSqrt <| lengthSqr v

--       /-- Distance between two points represented by vectors from any third point. -/
--       @[inline]
--       def distance (a b : $v2Ty) : $sTy :=
--         length (a - b)

--       /--
--       Normalizes vector to the length of `1`.

--       Returns `none` if the resulting vector is not finite.
--       -/
--       @[inline]
--       def normalize? (v : $v2Ty) : Option $v2Ty :=
--         let v' := v * (1 / v.length)
--         if v'.any <| not ∘ $sIsFinite
--           then none
--           else some v'

--       /--
--       Normalizes vector to the length of `1`.

--       Panics in debug if any component of `v/|v|` is not finite.
--       -/
--       @[inline]
--       def normalize (v : $v2Ty) : $v2Ty :=
--         let v' := v * (1 / v.length)
--         debug_assert! v'.any <| not ∘ $sIsFinite
--         v'

--       /-- Checks whether the length of `v` is 1. -/
--       @[inline]
--       def isNormalized (maxSqrDelta : $sTy := 2e-4) (v : $v2Ty) : Bool :=
--         $sAbs (v.lengthSqr - 1) <= maxSqrDelta

--       /--
--       Returns angle between positive X axis and the ray defined by vector `v` and origin `(0, 0)`.

--       Panics in debug if the length of `v` is zero.
--       -/
--       @[inline]
--       def angle (v : $v2Ty) : $sTy :=
--         debug_assert! v.length > 0
--         $sAtan2 v.y v.x

--       /-- Angle between two vectors (counterclockwise if Y is up and X is right). -/
--       @[inline]
--       def angleBetween (a b : $v2Ty) : $sTy :=
--         $sAtan2 (a.x * b.y - a.y * b.x) (dot a b)

--       /-- Angle between positive X axis and a line from point `a` to `b`. -/
--       @[inline]
--       def lineAngle (a b : $v2Ty) : $sTy :=
--         angle (b - a)

--       /--
--       Projection of `a` onto `b`.

--       Panics in debug if `1/|b|²` is not finite.
--       -/
--       @[inline]
--       def projectOnto (a b : $v2Ty) : $v2Ty :=
--         let invBSqrLen := 1 / b.lengthSqr
--         debug_assert! $sIsFinite invBSqrLen
--         b * (dot a b) * invBSqrLen

--       /--
--       Projection of `a` onto `b`.

--       Panics in debug if `b` is not normalized.
--       -/
--       @[inline]
--       def projectOntoNormalized (a b : $v2Ty) : $v2Ty :=
--         debug_assert! b.isNormalized
--         b * (dot a b)

--       /--
--       Rejection of `a` from `b`.

--       Rejection is the part of `a` that is missing from its projection
--       (`a = rejection + projection`).

--       Panics in debug if `1/|b|²` is not finite.
--       -/
--       @[inline]
--       def rejectFrom (a b : $v2Ty) : $v2Ty :=
--         a - projectOnto a b

--       /--
--       Rejection of `a` from `b`.

--       Rejection is the part of `a` that is missing from its projection
--       (`a = rejection + projection`).

--       Panics in debug if `b` is not normalized.
--       -/
--       @[inline]
--       def rejectFromNormalized (a b : $v2Ty) : $v2Ty :=
--         a - projectOntoNormalized a b

--       /--
--       Performs a linear interpolation between `start` and `end` based on `t`.

--       When `t` is `0`, the result will be `start`.
--       When `t` is `1`, the result will be `end`.

--       When `value` is outside of the range, the result is linearly extrapolated.

--       Returns `NaN` if `value`, `start` or `end` is NaN (for each axis).
--       -/
--       @[inline]
--       def lerp (start «end» : $v2Ty) (t : $sTy) : $v2Ty :=
--         start + t * («end» - start)

--       /--
--       Reflect `v` across a line with a `normal`.

--       Panics in debug if `normal` is not normalized.
--       -/
--       @[inline]
--       def reflectAlongNormal (normal v : $v2Ty) : $v2Ty :=
--         debug_assert! normal.isNormalized
--         v - (2 * dot v normal) * normal

--       /--
--       Reflect `v` across a line with a perpendicular `perp`.

--       Panics in debug if `2/|perp|²` is not finite.
--       -/
--       @[inline]
--       def reflectAlong (perp v : $v2Ty) : $v2Ty :=
--         let k := 2 / perp.lengthSqr
--         debug_assert! $sIsFinite k
--         v - k * dot v perp * perp

--       /--
--       Reflect `v` across a line with a `normal`.

--       Assumes `normal` is normalized.
--       -/
--       @[inline]
--       def reflectAlong' (normal v : $v2Ty) : $v2Ty :=
--         v - (2 * dot v normal) * normal

--       /--
--       Reflect `v` across a `line`.

--       Panics in debug if `line` is not normalized.
--       -/
--       @[inline]
--       def reflectAcrossNormal (line v : $v2Ty) : $v2Ty :=
--         debug_assert! line.isNormalized
--         2 * dot v line * line - v

--       /--
--       Reflect `v` across a `line`.

--       Panics in debug if `2/|line|²` is not finite.
--       -/
--       @[inline]
--       def reflectAcross (line v : $v2Ty) : $v2Ty :=
--         let k := 2 / line.lengthSqr
--         debug_assert! $sIsFinite k
--         k * dot v line * line - v

--       /--
--       Reflect `v` across a `line`.

--       Assumes `line` is normalized.
--       -/
--       @[inline]
--       def reflectAcross' (line v : $v2Ty) : $v2Ty :=
--         2 * dot v line * line - v

--       /-- Rotate `v` by `angle`. -/
--       @[inline]
--       def rotate (angle : $sTy) (v : $v2Ty) : $v2Ty :=
--         let cos := angle.cos
--         let sin := angle.sin
--         ⟨v.x * cos - v.y * sin, v.x * sin + v.y * cos⟩

--       /--
--       Move `v` towards `target`.

--       Panics in debug if `maxDistance` is negative.
--       -/
--       @[inline]
--       def moveTowards (maxDistance : $sTy) (target v : $v2Ty) : $v2Ty :=
--         debug_assert! maxDistance >= 0
--         let delta := target - v
--         let distanceSqr := delta.lengthSqr
--         if distanceSqr <= maxDistance * maxDistance
--           then target
--           else v + delta * (maxDistance / distanceSqr.sqrt)

--       /--
--       Compute the direction of a refracted ray where
--       * `v`: direction of the incoming ray
--       * `n`: normal vector of the interface of two optical media
--       * `r`: the ratio of the refractive index of the medium from where the ray comes
--         to the refractive index of the medium on the other side of the surface

--       Panics in debug if either `v` or `n` is not normalized.
--       -/
--       @[inline]
--       def refract (r : $sTy) (n v : $v2Ty) : $v2Ty :=
--         debug_assert! n.isNormalized && v.isNormalized
--         let «v∙n» := dot v n
--         let d := 1 - r * r * (1 - «v∙n» * «v∙n»)
--         if d >= 0
--           then (v * r) - (n * (r * «v∙n» + d.sqrt))
--           else .zero

--       /--
--       Checks whether absolute difference between corresponding
--       component values is less than or equal to `maxDifference`.
--       -/
--       @[inline]
--       def almostEqual (maxDifference : $sTy) (a b : $v2Ty) : Bool :=
--         (a - b).all <| (· <= maxDifference) ∘ $sAbs

--       /--
--       Changes vector length to be between `min` and `max`.

--       Panics in debug if either `min` or `max` is negative, or if `min > max`.
--       -/
--       @[inline]
--       def clampLength (min max : $sTy) (v : $v2Ty) : $v2Ty :=
--         debug_assert! min >= 0 && max >= 0 && min <= max
--         let lenSqr := lengthSqr v
--         if lenSqr < min * min then
--           v * (min / lenSqr.sqrt)
--         else if lenSqr > max * max then
--           v * (max / lenSqr.sqrt)
--         else
--           v

--       /--
--       Changes vector length to be not less than `min`.

--       Panics in debug if `min` is negative.
--       -/
--       @[inline]
--       def clampLengthMin (min : $sTy) (v : $v2Ty) : $v2Ty :=
--         debug_assert! min >= 0
--         let lenSqr := lengthSqr v
--         if lenSqr < min * min
--           then v * (min / lenSqr.sqrt)
--           else v

--       /--
--       Changes vector length to be not greater than `max`.

--       Panics in debug if `max` is negative.
--       -/
--       @[inline]
--       def clampLengthMax (max : $sTy) (v : $v2Ty) : $v2Ty :=
--         debug_assert! max >= 0
--         let lenSqr := lengthSqr v
--         if lenSqr > max * max
--           then v * (max / lenSqr.sqrt)
--           else v

--       /-- Returns vector with the direction of `v` and length of `target`. -/
--       @[inline]
--       def resizeAs (target v : $v2Ty) : $v2Ty :=
--         v * (target.lengthSqr / v.lengthSqr).sqrt

--       /--
--       Rotates `v` towards `target` up to `maxRotation` radians.

--       Panics in debug if `maxRotation` is negative.
--       -/
--       @[inline]
--       def rotateTowards (maxRotation : $sTy) (target v : $v2Ty) : $v2Ty :=
--         debug_assert! maxRotation >= 0
--         let angle := v.angleBetween target
--         let angleAbs := angle.abs
--         dbg_trace angleAbs
--         if angleAbs <= maxRotation
--           then resizeAs v target
--           else v.rotate <| if angle < 0 then -maxRotation else maxRotation

--       end $v2Ty
--     )

-- run_cmd
--   Meta.forEachScalar Meta.integers fun cx => do
--     let v2Ty := cx.structure "Vector2"
--     let sTy := cx.scalarType
--     Lean.Elab.Command.elabCommand <| ← `(
--       namespace $v2Ty

--       deriving instance DecidableEq for $v2Ty

--       /-- Componentwise bitwise `and`. -/
--       @[inline]
--       def and (a b : $v2Ty) : $v2Ty :=
--         ⟨a.x &&& b.x, a.y &&& b.y⟩

--       /-- Componentwise bitwise `or`. -/
--       @[inline]
--       def or (a b : $v2Ty) : $v2Ty :=
--         ⟨a.x ||| b.x, a.y ||| b.y⟩

--       /-- Componentwise bitwise `xor`. -/
--       @[inline]
--       def xor (a b : $v2Ty) : $v2Ty :=
--         ⟨a.x ^^^ b.x, a.y ^^^ b.y⟩

--       /-- Componentwise bitwise `complement` of a vector. -/
--       @[inline]
--       def complement (a : $v2Ty) : $v2Ty :=
--         ⟨~~~a.x, ~~~a.y⟩

--       @[inline] instance : AndOp $v2Ty := ⟨and⟩
--       @[inline] instance : OrOp $v2Ty := ⟨or⟩
--       @[inline] instance : XorOp $v2Ty := ⟨xor⟩
--       @[inline] instance : Complement $v2Ty := ⟨complement⟩

--       /-- Componentwise clamping of components. -/
--       @[inline]
--       def clamp (min max v : $v2Ty) : $v2Ty :=
--         ⟨Max.max min.x (Min.min v.x max.x), Max.max min.y (Min.min v.y max.y)⟩

--       /-- Componentwise modulo. -/
--       @[inline]
--       def mod (a b : $v2Ty) : $v2Ty :=
--         ⟨a.x % b.x, a.y % b.y⟩

--       @[inline] instance : Mod $v2Ty := ⟨mod⟩
--       @[inline] instance : HMod $v2Ty $sTy $v2Ty := ⟨fun v s => ⟨v.x % s, v.y % s⟩⟩
--       @[inline] instance : HMod $sTy $v2Ty $v2Ty := ⟨fun s v => ⟨s % v.x, s % v.y⟩⟩

--       end $v2Ty
--     )

-- run_cmd
--   Meta.forEachScalar Meta.signedIntegers fun cx => do
--     let v2Ty := cx.structure "Vector2"
--     Lean.Elab.Command.elabCommand <| ← `(
--       namespace $v2Ty

--       /-- Componentwise sign (does not return zeros). -/
--       @[inline]
--       def sign (v : $v2Ty) : $v2Ty :=
--         ⟨cond (v.x < 0) (-1) 1, cond (v.y < 0) (-1) 1⟩

--       end $v2Ty
--     )

-- run_cmd
--   Meta.forEachScalar Meta.signed fun cx => do
--     let v2Ty := cx.structure "Vector2"
--     let sTy := cx.scalarType
--     let sAbs := cx.scalarMember "abs"
--     Lean.Elab.Command.elabCommand <| ← `(
--       namespace $v2Ty

--       /-- Vector `v` rotated by 90 degrees counterclockwise (if Y is up and X is right). -/
--       @[inline]
--       def perpCCW (v : $v2Ty) : $v2Ty := ⟨-v.y, v.x⟩

--       /-- Vector `v` rotated by 90 degrees clockwise (if Y is up and X is right). -/
--       @[inline]
--       def perpCW (v : $v2Ty) : $v2Ty := ⟨v.y, -v.x⟩

--       /-- Computes absolute values of components. -/
--       @[inline]
--       def abs (v : $v2Ty) : $v2Ty :=
--         ⟨$sAbs v.x, $sAbs v.y⟩

--       /-- Squared distance between two points represented by vectors from any third point. -/
--       @[inline]
--       def distanceSqr (a b : $v2Ty) : $sTy :=
--         lengthSqr <| a - b

--       /--
--       Cross product of two 2D vectors extended to 3D by setting Z to 0.
--       Returns Z of the resulting vector. Its X and Y are 0.

--       Equal to the area of the parallelogram between the input vectors.
--       Sign represents direction of rotation from `a` to `b`
--       (negative means clockwise if Y is up and X is right).

--       Equal to `|a||b| sin θ` where `θ` is the angle between vectors.
--       -/
--       @[inline]
--       def cross (a b : $v2Ty) : $sTy :=
--         a.x * b.y - a.y * b.x

--       end $v2Ty
--     )

-- run_cmd
--   Meta.forEachScalar Meta.unsignedIntegers fun cx => do
--     let v2Ty := cx.structure "Vector2"
--     let sTy := cx.scalarType
--     Lean.Elab.Command.elabCommand <| ← `(
--       namespace $v2Ty

--       /-- Squared distance between two points represented by vectors from any third point. -/
--       @[inline]
--       def distanceSqr (a b : $v2Ty) : $sTy :=
--         let x := if a.x >= b.x then a.x - b.x else b.x - a.x
--         let y := if a.y >= b.y then a.y - b.y else b.y - a.y
--         x * x + y * y

--       end $v2Ty
--     )

-- run_cmd
--   Meta.forEachScalar Meta.numbers fun cx1 =>
--     let v2Ty1 := cx1.structure "Vector2"
--     Meta.forEachScalar Meta.numbers fun cx2 => do
--       let v2Ty2 := cx2.structure "Vector2"
--       if let some s1To2 ← Meta.scalarConvertFn? cx1 cx2 then
--         let toV2Ty2 := cx1.structureMember "Vector2" <| "to" ++ cx2.scalarPrefix
--         Lean.Elab.Command.elabCommand <| ← `(
--           @[inline]
--           def $toV2Ty2 (v : $v2Ty1) : $v2Ty2 :=
--             .mk ($s1To2 v.x) ($s1To2 v.y)
--         )
--         Lean.addDocStringCore (← Lean.resolveGlobalConstNoOverload toV2Ty2)
--           s!"Componentwise conversion to `{cx2.scalarTypeName}` scalar type using `{s1To2.getId}`"
--       if let some s2To1 ← Meta.scalarConvertFn? cx2 cx1 then
--         let ofV2Ty2 := cx1.structureMember "Vector2" <| "of" ++ cx2.scalarPrefix
--         Lean.Elab.Command.elabCommand <| ← `(
--           @[inline]
--           def $ofV2Ty2 (v : $v2Ty2) : $v2Ty1 :=
--             .mk ($s2To1 v.x) ($s2To1 v.y)
--         )
--         Lean.addDocStringCore (← Lean.resolveGlobalConstNoOverload ofV2Ty2)
--           s!"Componentwise conversion from `{cx2.scalarTypeName}` scalar type using `{s2To1.getId}`"

-- /-- Creates a vector from a scalar array. Panics if the array's size is less than 2. -/
-- @[inline]
-- def F64Vector2.ofFloatArray (a : FloatArray) : F64Vector2 :=
--   if h: a.size >= 2
--     then ⟨a[0], a[1]⟩
--     else panic! "array contains less than 2 values"

-- /-- Pushes vector components to a scalar array. -/
-- @[inline]
-- def F64Vector2.toFloatArray
--   (v : F64Vector2) (dst : FloatArray := by exact FloatArray.emptyWithCapacity 2) : FloatArray :=
--     dst.push v.x |>.push v.y
