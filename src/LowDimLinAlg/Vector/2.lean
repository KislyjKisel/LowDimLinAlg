module

public import LowDimLinAlg.Axis
public import LowDimLinAlg.Scalar

import LowDimLinAlg.Meta.ForEachScalar

@[expose] public section

set_option hygiene false

namespace LowDimLinAlg

structure BVector2 where
  /--
  Creates vector from bitwise representation where
  `x` is the first bit and `y` is the second.
  -/
  ofBits ::
  /--
  Bitwise representation of the vector where
  `x` is the first bit and `y` is the second.
  -/
  bits : UInt8
  /-- Only first two bits may be set. -/
  length2 : bits &&& 0b11 = bits
deriving DecidableEq

@[inline]
instance : Inhabited BVector2 :=
  ⟨{ bits := 0, length2 := by decide }⟩

/-- Creates vector from components. -/
@[inline]
def BVector2.mk (x y : Bool) : BVector2 :=
  let xBit : UInt8 := cond x 1 0
  let yBit : UInt8 := cond y 1 0
  .ofBits (xBit ||| yBit <<< 1) <| by
    cases x <;> cases y <;> decide

@[inline]
def BVector2.x (v : BVector2) : Bool :=
  v.bits &&& 0b001 != 0

@[inline]
def BVector2.y (v : BVector2) : Bool :=
  v.bits &&& 0b010 != 0

run_cmd
  Meta.forEachScalar Meta.numbers fun cx => do
    let sTy := cx.scalarType
    let v2Ty := cx.structure "Vector2"
    Lean.Elab.Command.elabCommand <| ← `(
      structure $v2Ty where
        x : $sTy
        y : $sTy
      deriving Repr, Inhabited

      namespace $v2Ty

      /-- All components set to 0. -/
      @[inline]
      def zero : $v2Ty := ⟨0, 0⟩

      /-- All components set to 1. -/
      @[inline]
      def one : $v2Ty := ⟨1, 1⟩

      /-- All components set to -1. -/
      @[inline]
      def negOne : $v2Ty := ⟨-1, -1⟩

      /-- A unit vector pointing along the positive X axis. -/
      @[inline]
      def unitX : $v2Ty := ⟨1, 0⟩

      /-- A unit vector pointing along the positive Y axis. -/
      @[inline]
      def unitY : $v2Ty := ⟨0, 1⟩

      /-- A unit vector pointing along the negative X axis. -/
      @[inline]
      def unitNegX : $v2Ty := ⟨-1, 0⟩

      /-- A unit vector pointing along the negative Y axis. -/
      @[inline]
      def unitNegY : $v2Ty := ⟨0, -1⟩

      /-- Creates a vector with results of applying `f` to each component. -/
      @[inline]
      def mapBool (f : $sTy → Bool) (v : $v2Ty) : BVector2 :=
        .mk (f v.x) (f v.y)

      /-- Componentwise addition (integers wrap on underflow and overflow). -/
      @[inline]
      def add (a b : $v2Ty) : $v2Ty :=
        ⟨a.x + b.x, a.y + b.y⟩

      /-- Componentwise subtraction (integers wrap on underflow and overflow). -/
      @[inline]
      def sub (a b : $v2Ty) : $v2Ty :=
        ⟨a.x - b.x, a.y - b.y⟩

      /-- Componentwise multiplication (integers wrap on underflow and overflow). -/
      @[inline]
      def mul (a b : $v2Ty) : $v2Ty :=
        ⟨a.x * b.x, a.y * b.y⟩

      /-- Componentwise division (integers wrap on underflow and overflow). -/
      @[inline]
      def div (a b : $v2Ty) : $v2Ty :=
        ⟨a.x / b.x, a.y / b.y⟩

      /-- Negation of a vector. -/
      @[inline]
      def neg (v : $v2Ty) : $v2Ty :=
        ⟨-v.x, -v.y⟩

      /-- Componentwise multiplication of a vector by a scalar (integers wrap on underflow and overflow). -/
      @[inline]
      def scale (s : $sTy) (v : $v2Ty) : $v2Ty :=
        ⟨v.x * s, v.y * s⟩

      @[inline] instance : Add $v2Ty := ⟨add⟩
      @[inline] instance : Sub $v2Ty := ⟨sub⟩
      @[inline] instance : Mul $v2Ty := ⟨mul⟩
      @[inline] instance : Div $v2Ty := ⟨div⟩
      @[inline] instance : Neg $v2Ty := ⟨neg⟩
      @[inline] instance : SMul $sTy $v2Ty := ⟨scale⟩

      @[inline] instance : HAdd $sTy $v2Ty $v2Ty := ⟨fun s v ↦ ⟨s + v.x, s + v.y⟩⟩
      @[inline] instance : HAdd $v2Ty $sTy $v2Ty := ⟨fun v s ↦ ⟨v.x + s, v.y + s⟩⟩
      @[inline] instance : HSub $sTy $v2Ty $v2Ty := ⟨fun s v ↦ ⟨s - v.x, s - v.y⟩⟩
      @[inline] instance : HSub $v2Ty $sTy $v2Ty := ⟨fun v s ↦ ⟨v.x - s, v.y - s⟩⟩
      @[inline] instance : HMul $v2Ty $sTy $v2Ty := ⟨fun v s ↦ v.scale s⟩
      @[inline] instance : HMul $sTy $v2Ty $v2Ty := ⟨scale⟩
      @[inline] instance : HDiv $v2Ty $sTy $v2Ty := ⟨fun v s ↦ v.scale (1 / s)⟩
      @[inline] instance : HDiv $sTy $v2Ty $v2Ty := ⟨fun s v ↦ ⟨s / v.x, s / v.y⟩⟩

      /-- Sum of components. -/
      @[inline]
      def sum (v : $v2Ty) : $sTy :=
        v.x + v.y

      /-- Product of components. -/
      @[inline]
      def product (v : $v2Ty) : $sTy :=
        v.x * v.y

      /-- Dot product of two vectors. -/
      @[inline]
      def dot (a b : $v2Ty) : $sTy :=
        a.x * b.x + a.y * b.y

      /-- Vector length squared. -/
      @[inline]
      def lengthSqr (v : $v2Ty) : $sTy :=
        dot v v

      end $v2Ty
    )

run_cmd
  Meta.forEachScalar Meta.scalars fun cx => do
    let sTy := cx.scalarType
    let v2Ty := cx.structure "Vector2"
    Lean.Elab.Command.elabCommand <| ← `(
      namespace $v2Ty
      /-- Converts a vector to a string of `(x y)` format.` -/
      @[inline]
      def toString (v : $v2Ty) : String :=
        s!"({v.x} {v.y})"

      @[inline]
      instance : ToString $v2Ty := ⟨toString⟩

      /-- Gets vector's component value. -/
      @[inline]
      def get (v : $v2Ty) : Axis2 → $sTy
      | .x => v.x
      | .y => v.y

      @[inline]
      instance : GetElem $v2Ty Axis2 $sTy (fun _ _ => True) where
        getElem := Function.curry <| Function.const _ ∘ get.uncurry

      @[inline]
      instance : GetElem $v2Ty Nat $sTy (fun _ i => i < 2) where
        getElem v
        | 0, _ => v.x
        | 1, _ => v.y

      /-- Sets vector's component value. -/
      @[inline]
      def set (v : $v2Ty) : Axis2 → $sTy → $v2Ty
      | .x, x => .mk x v.y
      | .y, y => .mk v.x y

      /-- Minimal component of a vector. -/
      def minValue (v : $v2Ty) : $sTy :=
        Min.min v.x v.y

      /-- Maximal component of a vector. -/
      def maxValue (v : $v2Ty) : $sTy :=
        Max.max v.x v.y

      /-- First minimal component axis. -/
      def minAxis (v : $v2Ty) : Axis2 :=
        if v.x <= v.y then .x else .y

      /-- First maximal component axis. -/
      def maxAxis (v : $v2Ty) : Axis2 :=
        if v.x >= v.y then .x else .y

      /-- Creates a vector with `y` set to `v.y`. -/
      @[inline]
      def withX (v : $v2Ty) (x : $sTy) : $v2Ty :=
        .mk x v.y

      /-- Creates a vector with `x` set to `v.x`. -/
      @[inline]
      def withY (v : $v2Ty) (y : $sTy) : $v2Ty :=
        .mk v.x y

      /-- Creates a vector with all elements set to `x`. -/
      @[inline]
      def splat (x : $sTy) : $v2Ty :=
        .mk x x

      /-- Creates a vector from an array. Panics if the list's length is less than 2. -/
      @[inline]
      def ofList (a : List $sTy) : $v2Ty :=
        if h: a.length >= 2
          then .mk a[0] a[1]
          else panic! "list contains less than two values"

      /-- Creates a vector from an array. Panics if the array's size is less than 2. -/
      @[inline]
      def ofArray (a : Array $sTy) : $v2Ty :=
        if h: a.size >= 2
          then .mk a[0] a[1]
          else panic! "array contains less than two values"

      /-- Creates a vector from a fixed length array. -/
      @[inline]
      def ofVector (v : Vector $sTy 2) : $v2Ty :=
        .mk v[0] v[1]

      /-- Creates a list from vector components. -/
      @[inline]
      def toList (v : $v2Ty) : List $sTy :=
        [v.x, v.y]

      /-- Pushes vector components to an array. -/
      @[inline]
      def toArray (v : $v2Ty) (dst : Array $sTy := by exact Array.emptyWithCapacity 2) : Array $sTy :=
        dst.push v.x |>.push v.y

      /-- Creates a fixed length array from vector components. -/
      @[inline]
      def toVector (v : $v2Ty) : Vector $sTy 2 :=
        Vector.emptyWithCapacity 2 |>.push v.x |>.push v.y

      /-- Creates a vector with elements from `v` modified by `f`. -/
      @[inline]
      def map (f : $sTy → $sTy) (v : $v2Ty) : $v2Ty :=
        .mk (f v.x) (f v.y)

      @[inline]
      def select (mask : BVector2) (true false : $v2Ty) : $v2Ty :=
        .mk (cond mask.x true.x false.x) (cond mask.y true.y false.y)

      /-- Componentwise minimum. -/
      @[inline]
      def min (a b : $v2Ty) : $v2Ty :=
        .mk (Min.min a.x b.x) (Min.min a.y b.y)

      /-- Componentwise maximum. -/
      @[inline]
      def max (a b : $v2Ty) : $v2Ty :=
        .mk (Max.max a.x b.x) (Max.max a.y b.y)

      /-- Componentwise "less than". -/
      @[inline]
      def lt' (a b : $v2Ty) : BVector2 :=
        .mk (a.x < b.x) (a.y < b.y)

      /-- Componentwise "less than or equal to". -/
      @[inline]
      def le' (a b : $v2Ty) : BVector2 :=
        .mk (a.x <= b.x) (a.y <= b.y)

      /-- Componentwise "greater than". -/
      @[inline]
      def gt' (a b : $v2Ty) : BVector2 :=
        .mk (a.x > b.x) (a.y > b.y)

      /-- Componentwise "greater than or equal to". -/
      @[inline]
      def ge' (a b : $v2Ty) : BVector2 :=
        .mk (a.x >= b.x) (a.y >= b.y)

      /-- Returns `true` if application of `f` to *any* of the components returns `true`. -/
      @[inline]
      def any (f : $sTy → Bool) (v : $v2Ty) : Bool :=
        f v.x || f v.y

      /-- Returns `true` if application of `f` to *each* component returns `true`. -/
      @[inline]
      def all (f : $sTy → Bool) (v : $v2Ty) : Bool :=
        f v.x && f v.y

      /-- Whether componentwise "less than" is true on all axes. -/
      @[inline]
      def lt (a b : $v2Ty) : Prop :=
        a.x < b.x ∧ a.y < b.y

      /-- Whether componentwise "less than or equal to" is true on all axes. -/
      @[inline]
      def le (a b : $v2Ty) : Prop :=
        a.x <= b.x ∧ a.y <= b.y

      @[inline] instance : LT $v2Ty := ⟨lt⟩
      @[inline] instance : LE $v2Ty := ⟨le⟩

      @[inline]
      instance : DecidableLT $v2Ty := fun a b => by
        unfold LT.lt instLT lt
        infer_instance

      @[inline]
      instance : DecidableLE $v2Ty := fun a b => by
        unfold LE.le instLE le
        infer_instance

      end $v2Ty
    )

run_cmd
  Meta.forEachScalar Meta.floats fun cx => do
    let sTy := cx.scalarType
    let v2Ty := cx.structure "Vector2"
    let sInf := cx.scalarExtMember "inf"
    let sNegInf := cx.scalarExtMember "negInf"
    let sClamp := cx.scalarExtMember "clamp"
    let sSign := cx.scalarExtMember "sign"
    let sSqrt := cx.scalarMember "sqrt"
    let sIsFinite := cx.scalarMember "isFinite"
    let sAtan2 := cx.scalarMember "atan2"
    let sAbs := cx.scalarMember "abs"
    Lean.Elab.Command.elabCommand <| ← `(
      namespace $v2Ty

      deriving instance BEq for $v2Ty

      /-- All components set to NaN. -/
      @[inline]
      def nan : $v2Ty := splat (0 / 0)

      /-- All components set to positive infinity. -/
      @[inline]
      def inf : $v2Ty := splat $sInf

      /-- All components set to negative infinity. -/
      @[inline]
      def negInf : $v2Ty := splat $sNegInf

      /--
      Creates a unit vector from `angle`.

      Angle is counterclockwise if Y is up and X is down.
      -/
      @[inline]
      def fromAngle (angle : $sTy) : $v2Ty :=
        ⟨angle.cos, angle.sin⟩

      /--
      Creates a vector from `length` and `angle`.

      Angle is counterclockwise if Y is up and X is down.
      -/
      @[inline]
      def fromLengthAngle (length angle : $sTy) : $v2Ty :=
        length * fromAngle angle

      /-- Component-wise clamping of components. -/
      @[inline]
      def clamp (min max v : $v2Ty) : $v2Ty :=
        ⟨$sClamp min.x max.x v.x, $sClamp min.y max.y v.y⟩

      /-- Component-wise sign (does not return zeros). -/
      @[inline]
      def sign (v : $v2Ty) : $v2Ty :=
        ⟨$sSign v.x, $sSign v.y⟩

      /-- Vector length. -/
      @[inline]
      def length (v : $v2Ty) : $sTy :=
        $sSqrt <| lengthSqr v

      /-- Distance between two points represented by vectors from any third point. -/
      @[inline]
      def distance (a b : $v2Ty) : $sTy :=
        length (a - b)

      /--
      Normalizes vector to the length of `1`.

      Returns `none` if the resulting vector is not finite.
      -/
      @[inline]
      def normalize? (v : $v2Ty) : Option $v2Ty :=
        let v' := v * (1 / v.length)
        if v'.any <| not ∘ $sIsFinite
          then none
          else some v'

      /--
      Normalizes vector to the length of `1`.

      Panics in debug if any of `v/|v|` components is not finite.
      -/
      @[inline]
      def normalize (v : $v2Ty) : $v2Ty :=
        let v' := v * (1 / v.length)
        debug_assert! v'.any <| not ∘ $sIsFinite
        v'

      /-- Checks whether the length of `v` is 1. -/
      @[inline]
      def isNormalized (maxSqrDelta : $sTy := 2e-4) (v : $v2Ty) : Bool :=
        $sAbs (v.lengthSqr - 1) <= maxSqrDelta

      /--
      Returns angle between positive X axis and the ray defined by vector `v` and origin `(0, 0)`.

      Panics in debug if the length of `v` is zero.
      -/
      @[inline]
      def angle (v : $v2Ty) : $sTy :=
        debug_assert! v.length > 0
        $sAtan2 v.y v.x

      /-- Angle between two vectors (counterclockwise if Y is up and X is right). -/
      @[inline]
      def angleBetween (a b : $v2Ty) : $sTy :=
        $sAtan2 (a.x * b.y - a.y * b.x) (dot a b)

      /-- Angle between positive X axis and a line from point `a` to `b`. -/
      @[inline]
      def lineAngle (a b : $v2Ty) : $sTy :=
        angle (b - a)

      /--
      Projection of `a` onto `b`.

      Panics in debug if `1/|b|²` is not finite.
      -/
      @[inline]
      def projectOnto (a b : $v2Ty) : $v2Ty :=
        let invBSqrLen := 1 / b.lengthSqr
        debug_assert! $sIsFinite invBSqrLen
        b * (dot a b) * invBSqrLen

      /--
      Projection of `a` onto `b`.

      Panics in debug if `b` is not normalized.
      -/
      @[inline]
      def projectOntoNormalized (a b : $v2Ty) : $v2Ty :=
        debug_assert! b.isNormalized
        b * (dot a b)

      /--
      Rejection of `a` from `b`.

      Rejection is the part of `a` that is missing from its projection
      (`a = rejection + projection`).

      Panics in debug if `1/|b|²` is not finite.
      -/
      @[inline]
      def rejectFrom (a b : $v2Ty) : $v2Ty :=
        a - projectOnto a b

      /--
      Rejection of `a` from `b`.

      Rejection is the part of `a` that is missing from its projection
      (`a = rejection + projection`).

      Panics in debug if `b` is not normalized.
      -/
      @[inline]
      def rejectFromNormalized (a b : $v2Ty) : $v2Ty :=
        a - projectOntoNormalized a b

      /--
      Performs a linear interpolation between `start` and `end` based on `t`.

      When `t` is `0`, the result will be `start`.
      When `t` is `1`, the result will be `end`.

      When `value` is outside of the range, the result is linearly extrapolated.

      Returns `NaN` if `value`, `start` or `end` is NaN (for each axis).
      -/
      @[inline]
      def lerp (start «end» : $v2Ty) (t : $sTy) : $v2Ty :=
        start + t * («end» - start)

      /--
      Reflect `v` across a line with a `normal`.

      Panics in debug if `normal` is not normalized.
      -/
      @[inline]
      def reflectAlongNormal (normal v : $v2Ty) : $v2Ty :=
        debug_assert! normal.isNormalized
        v - (2 * dot v normal) * normal

      /--
      Reflect `v` across a line with a perpendicular `perp`.

      Panics in debug if `2/|perp|²` is not finite.
      -/
      @[inline]
      def reflectAlong (perp v : $v2Ty) : $v2Ty :=
        let k := 2 / perp.lengthSqr
        debug_assert! $sIsFinite k
        v - k * dot v perp * perp

      /--
      Reflect `v` across a line with a `normal`.

      Assumes `normal` is normalized.
      -/
      @[inline]
      def reflectAlong' (normal v : $v2Ty) : $v2Ty :=
        v - (2 * dot v normal) * normal

      /--
      Reflect `v` across a `line`.

      Panics in debug if `line` is not normalized.
      -/
      @[inline]
      def reflectAcrossNormal (line v : $v2Ty) : $v2Ty :=
        debug_assert! line.isNormalized
        2 * dot v line * line - v

      /--
      Reflect `v` across a `line`.

      Panics in debug if `2/|line|²` is not finite.
      -/
      @[inline]
      def reflectAcross (line v : $v2Ty) : $v2Ty :=
        let k := 2 / line.lengthSqr
        debug_assert! $sIsFinite k
        k * dot v line * line - v

      /--
      Reflect `v` across a `line`.

      Assumes `line` is normalized.
      -/
      @[inline]
      def reflectAcross' (line v : $v2Ty) : $v2Ty :=
        2 * dot v line * line - v

      /-- Rotate `v` by `angle`. -/
      @[inline]
      def rotate (angle : $sTy) (v : $v2Ty) : $v2Ty :=
        let cos := angle.cos
        let sin := angle.sin
        ⟨v.x * cos - v.y * sin, v.x * sin + v.y * cos⟩

      /--
      Move `v` towards `target`.

      Panics in debug if `maxDistance` is negative.
      -/
      @[inline]
      def moveTowards (maxDistance : $sTy) (target v : $v2Ty) : $v2Ty :=
        debug_assert! maxDistance >= 0
        let delta := target - v
        let distanceSqr := delta.lengthSqr
        if distanceSqr <= maxDistance * maxDistance
          then target
          else v + delta * (maxDistance / distanceSqr.sqrt)

      /--
      Compute the direction of a refracted ray where
      * `v`: direction of the incoming ray
      * `n`: normal vector of the interface of two optical media
      * `r`: the ratio of the refractive index of the medium from where the ray comes
        to the refractive index of the medium on the other side of the surface

      Panics in debug if either `v` or `n` is not normalized.
      -/
      @[inline]
      def refract (r : $sTy) (n v : $v2Ty) : $v2Ty :=
        debug_assert! n.isNormalized && v.isNormalized
        let «v∙n» := dot v n
        let d := 1 - r * r * (1 - «v∙n» * «v∙n»)
        if d >= 0
          then (v * r) - (n * (r * «v∙n» + d.sqrt))
          else .zero

      /--
      Checks whether absolute difference between corresponding
      component values is less than or equal to `maxDifference`.
      -/
      @[inline]
      def almostEqual (maxDifference : $sTy) (a b : $v2Ty) : Bool :=
        (a - b).all <| (· <= maxDifference) ∘ $sAbs

      /--
      Changes vector length to be between `min` and `max`.

      Panics in debug if either `min` or `max` is negative, or if `min > max`.
      -/
      @[inline]
      def clampLength (min max : $sTy) (v : $v2Ty) : $v2Ty :=
        debug_assert! min >= 0 && max >= 0 && min <= max
        let lenSqr := lengthSqr v
        if lenSqr < min * min then
          v * (min / lenSqr.sqrt)
        else if lenSqr > max * max then
          v * (max / lenSqr.sqrt)
        else
          v

      /--
      Changes vector length to be not less than `min`.

      Panics in debug if `min` is negative.
      -/
      @[inline]
      def clampLengthMin (min : $sTy) (v : $v2Ty) : $v2Ty :=
        debug_assert! min >= 0
        let lenSqr := lengthSqr v
        if lenSqr < min * min
          then v * (min / lenSqr.sqrt)
          else v

      /--
      Changes vector length to be not greater than `max`.

      Panics in debug if `max` is negative.
      -/
      @[inline]
      def clampLengthMax (max : $sTy) (v : $v2Ty) : $v2Ty :=
        debug_assert! max >= 0
        let lenSqr := lengthSqr v
        if lenSqr > max * max
          then v * (max / lenSqr.sqrt)
          else v

      /-- Returns vector with the direction of `v` and length of `target`. -/
      @[inline]
      def resizeAs (target v : $v2Ty) : $v2Ty :=
        v * (target.lengthSqr / v.lengthSqr).sqrt

      /--
      Rotates `v` towards `target` up to `maxRotation` radians.

      Panics in debug if `maxRotation` is negative.
      -/
      @[inline]
      def rotateTowards (maxRotation : $sTy) (target v : $v2Ty) : $v2Ty :=
        debug_assert! maxRotation >= 0
        let angle := v.angleBetween target
        let angleAbs := angle.abs
        dbg_trace angleAbs
        if angleAbs <= maxRotation
          then resizeAs v target
          else v.rotate <| if angle < 0 then -maxRotation else maxRotation

      end $v2Ty
    )

run_cmd
  Meta.forEachScalar Meta.integers fun cx => do
    let v2Ty := cx.structure "Vector2"
    Lean.Elab.Command.elabCommand <| ← `(
      namespace $v2Ty

      deriving instance DecidableEq for $v2Ty

      /-- Componentwise bitwise `and`. -/
      @[inline]
      def and (a b : $v2Ty) : $v2Ty :=
        ⟨a.x &&& b.x, a.y &&& b.y⟩

      /-- Componentwise bitwise `or`. -/
      @[inline]
      def or (a b : $v2Ty) : $v2Ty :=
        ⟨a.x ||| b.x, a.y ||| b.y⟩

      /-- Componentwise bitwise `xor`. -/
      @[inline]
      def xor (a b : $v2Ty) : $v2Ty :=
        ⟨a.x ^^^ b.x, a.y ^^^ b.y⟩

      /-- Componentwise bitwise `complement` of a vector. -/
      @[inline]
      def complement (a : $v2Ty) : $v2Ty :=
        ⟨~~~a.x, ~~~a.y⟩

      @[inline] instance : AndOp $v2Ty := ⟨and⟩
      @[inline] instance : OrOp $v2Ty := ⟨or⟩
      @[inline] instance : XorOp $v2Ty := ⟨xor⟩
      @[inline] instance : Complement $v2Ty := ⟨complement⟩

      /-- Component-wise clamping of components. -/
      @[inline]
      def clamp (min max v : $v2Ty) : $v2Ty :=
        ⟨Max.max min.x (Min.min v.x max.x), Max.max min.y (Min.min v.y max.y)⟩

      end $v2Ty
    )

run_cmd
  Meta.forEachScalar Meta.signedIntegers fun cx => do
    let v2Ty := cx.structure "Vector2"
    Lean.Elab.Command.elabCommand <| ← `(
      namespace $v2Ty

      /-- Component-wise sign (does not return zeros). -/
      @[inline]
      def sign (v : $v2Ty) : $v2Ty :=
        ⟨cond (v.x < 0) (-1) 1, cond (v.y < 0) (-1) 1⟩

      end $v2Ty
    )

run_cmd
  Meta.forEachScalar Meta.signed fun cx => do
    let v2Ty := cx.structure "Vector2"
    let sTy := cx.scalarType
    let sAbs := cx.scalarMember "abs"
    Lean.Elab.Command.elabCommand <| ← `(
      namespace $v2Ty

      /-- Vector `v` rotated by 90 degrees counterclockwise (if Y is up and X is right). -/
      @[inline]
      def perpCCW (v : $v2Ty) : $v2Ty := ⟨-v.y, v.x⟩

      /-- Vector `v` rotated by 90 degrees clockwise (if Y is up and X is right). -/
      @[inline]
      def perpCW (v : $v2Ty) : $v2Ty := ⟨v.y, -v.x⟩

      /-- Computes absolute values of components. -/
      @[inline]
      def abs (v : $v2Ty) : $v2Ty :=
        ⟨$sAbs v.x, $sAbs v.y⟩

      /-- Squared distance between two points represented by vectors from any third point. -/
      @[inline]
      def distanceSqr (a b : $v2Ty) : $sTy :=
        lengthSqr <| a - b

      /--
      Cross product of two 2D vectors extended to 3D by setting Z to 0.
      Returns Z of the resulting vector. Its X and Y are 0.

      Equal to the area of the parallelogram between the input vectors.
      Sign represents direction of rotation from `a` to `b`
      (negative means clockwise if Y is up and X is right).

      Equal to `|a||b| sin θ` where `θ` is the angle between vectors.
      -/
      @[inline]
      def cross (a b : $v2Ty) : $sTy :=
        a.x * b.y - a.y * b.x

      end $v2Ty
    )

run_cmd
  Meta.forEachScalar Meta.unsignedIntegers fun cx => do
    let v2Ty := cx.structure "Vector2"
    let sTy := cx.scalarType
    Lean.Elab.Command.elabCommand <| ← `(
      namespace $v2Ty

      /-- Squared distance between two points represented by vectors from any third point. -/
      @[inline]
      def distanceSqr (a b : $v2Ty) : $sTy :=
        let x := if a.x >= b.x then a.x - b.x else b.x - a.x
        let y := if a.y >= b.y then a.y - b.y else b.y - a.y
        x * x + y * y

      end $v2Ty
    )

run_cmd
  Meta.forEachScalar Meta.numbers fun cx1 =>
    let v2Ty1 := cx1.structure "Vector2"
    Meta.forEachScalar Meta.numbers fun cx2 => do
      let v2Ty2 := cx2.structure "Vector2"
      if let some s1To2 ← Meta.scalarConvertFn? cx1 cx2 then
        let toV2Ty2 := cx1.structureMember "Vector2" <| "to" ++ cx2.scalarPrefix
        Lean.Elab.Command.elabCommand <| ← `(
          @[inline]
          def $toV2Ty2 (v : $v2Ty1) : $v2Ty2 :=
            .mk ($s1To2 v.x) ($s1To2 v.y)
        )
        Lean.addDocStringCore (← Lean.resolveGlobalConstNoOverload toV2Ty2)
          s!"Componentwise conversion to `{cx2.scalarTypeName}` scalar type using `{s1To2.getId}`"
      if let some s2To1 ← Meta.scalarConvertFn? cx2 cx1 then
        let ofV2Ty2 := cx1.structureMember "Vector2" <| "of" ++ cx2.scalarPrefix
        Lean.Elab.Command.elabCommand <| ← `(
          @[inline]
          def $ofV2Ty2 (v : $v2Ty2) : $v2Ty1 :=
            .mk ($s2To1 v.x) ($s2To1 v.y)
        )
        Lean.addDocStringCore (← Lean.resolveGlobalConstNoOverload ofV2Ty2)
          s!"Componentwise conversion from `{cx2.scalarTypeName}` scalar type using `{s2To1.getId}`"

/-- Creates a vector from a scalar array. Panics if the array's size is less than 2. -/
@[inline]
def F64Vector2.ofFloatArray (a : FloatArray) : F64Vector2 :=
  if h: a.size >= 2
    then ⟨a[0], a[1]⟩
    else panic! "array contains less than 2 values"

/-- Pushes vector components to a scalar array. -/
@[inline]
def F64Vector2.toFloatArray
  (v : F64Vector2) (dst : FloatArray := by exact FloatArray.emptyWithCapacity 2) : FloatArray :=
    dst.push v.x |>.push v.y

namespace BVector2

instance : Repr BVector2 where
  reprPrec v _ :=
    let fields : List Std.Format := [
      Std.Format.joinSep [
        "bits",
        ":=",
        "0b".append <| String.ofList <| (Nat.toDigits 2 v.bits.toNat).leftpad 2 '0'
      ] " ",
      Std.Format.joinSep ["length2", ":=", "by", "decide"] " ",
    ]
    Std.Format.bracket "{" (Std.Format.joinSep fields <| "," ++ Std.Format.line) "}"

/-- All components set to `false`. -/
@[inline]
protected def false : BVector2 :=
  .splat false

/-- All components set to `true`. -/
@[inline]
protected def true : BVector2 :=
  .splat true

/--
Creates vector from bitwise representation where
`x` is the first bit and `y` is the second.
Other bits are zeroed.
-/
@[inline]
def ofBits' (bits : UInt8) : BVector2 :=
  .ofBits (bits &&& 0b11) (by rw [UInt8.and_assoc, UInt8.and_self])

/-- Componentwise boolean `and`. -/
@[inline]
def and (a b : BVector2) : BVector2 :=
  .ofBits (a.bits &&& b.bits) <| by
    rw [UInt8.and_assoc, b.length2]

private
theorem toNat_length2 (v : BVector2) : v.bits.toNat &&& 0b11 = v.bits.toNat := by
  exact UInt8.toNat_inj.mpr v.length2

/-- Componentwise boolean `or`. -/
@[inline]
def or (a b : BVector2) : BVector2 :=
  .ofBits (a.bits ||| b.bits) <| by
    apply UInt8.eq_of_toFin_eq
    apply Fin.eq_of_val_eq
    show (a.bits.toNat ||| b.bits.toNat) &&& 3 = a.bits.toNat ||| b.bits.toNat
    rw [Nat.and_or_distrib_right, toNat_length2 a, toNat_length2 b]

/-- Componentwise boolean `xor`. -/
@[inline]
def xor (a b : BVector2) : BVector2 :=
  .ofBits (a.bits ^^^ b.bits) <| by
    apply UInt8.eq_of_toFin_eq
    apply Fin.eq_of_val_eq
    show (a.bits.toNat ^^^ b.bits.toNat) &&& 3 = a.bits.toNat ^^^ b.bits.toNat
    rw [Nat.and_xor_distrib_right, toNat_length2 a, toNat_length2 b]

/-- Componentwise boolean `not`. -/
@[inline]
def not (v : BVector2) : BVector2 :=
  .ofBits' v.bits.complement

@[inline]
instance : AndOp BVector2 := ⟨BVector2.and⟩

@[inline]
instance : OrOp BVector2 := ⟨BVector2.or⟩

@[inline]
instance : XorOp BVector2 := ⟨BVector2.xor⟩

@[inline]
instance : Complement BVector2 := ⟨BVector2.not⟩

end BVector2
