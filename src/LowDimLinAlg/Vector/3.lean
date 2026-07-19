module

public import LowDimLinAlg.Axis
public import LowDimLinAlg.Scalar
public import LowDimLinAlg.Vector.Boolean

import LowDimLinAlg.Meta.ForEachScalar

@[expose] public section

set_option hygiene false

namespace LowDimLinAlg

run_cmd
  Meta.forEachScalar Meta.numbers fun cx => do
    let sTy := cx.scalarType
    let v3Ty := cx.structure "Vector3"
    Lean.Elab.Command.elabCommand <| ← `(
      structure $v3Ty where
        x : $sTy
        y : $sTy
        z : $sTy
      deriving Repr, Inhabited

      namespace $v3Ty

      /-- All components set to 0. -/
      @[inline]
      def zero : $v3Ty := ⟨0, 0, 0⟩

      /-- All components set to 1. -/
      @[inline]
      def one : $v3Ty := ⟨1, 1, 1⟩

      /-- All components set to -1. -/
      @[inline]
      def negOne : $v3Ty := ⟨-1, -1, -1⟩

      /-- A unit vector pointing along the positive X axis. -/
      @[inline]
      def unitX : $v3Ty := ⟨1, 0, 0⟩

      /-- A unit vector pointing along the positive Y axis. -/
      @[inline]
      def unitY : $v3Ty := ⟨0, 1, 0⟩

      /-- A unit vector pointing along the positive Z axis. -/
      @[inline]
      def unitZ : $v3Ty := ⟨0, 0, 1⟩

      /-- A unit vector pointing along the negative X axis. -/
      @[inline]
      def unitNegX : $v3Ty := ⟨-1, 0, 0⟩

      /-- A unit vector pointing along the negative Y axis. -/
      @[inline]
      def unitNegY : $v3Ty := ⟨0, -1, 0⟩

      /-- A unit vector pointing along the negative Z axis. -/
      @[inline]
      def unitNegZ : $v3Ty := ⟨0, 0, -1⟩

      /-- Creates a vector with results of applying `f` to each component. -/
      @[inline]
      def mapBool (f : $sTy → Bool) (v : $v3Ty) : BVector3 :=
        .mk (f v.x) (f v.y) (f v.z)

      /-- Componentwise addition (integers wrap on underflow and overflow). -/
      @[inline]
      def add (a b : $v3Ty) : $v3Ty :=
        ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

      /-- Componentwise subtraction (integers wrap on underflow and overflow). -/
      @[inline]
      def sub (a b : $v3Ty) : $v3Ty :=
        ⟨a.x - b.x, a.y - b.y, a.z - b.z⟩

      /-- Componentwise multiplication (integers wrap on underflow and overflow). -/
      @[inline]
      def mul (a b : $v3Ty) : $v3Ty :=
        ⟨a.x * b.x, a.y * b.y, a.z * b.z⟩

      /-- Componentwise division (integers wrap on underflow and overflow). -/
      @[inline]
      def div (a b : $v3Ty) : $v3Ty :=
        ⟨a.x / b.x, a.y / b.y, a.z / b.z⟩

      @[inline] instance : Add $v3Ty := ⟨add⟩
      @[inline] instance : Sub $v3Ty := ⟨sub⟩
      @[inline] instance : Mul $v3Ty := ⟨mul⟩
      @[inline] instance : Div $v3Ty := ⟨div⟩

      @[inline] instance : HAdd $sTy $v3Ty $v3Ty := ⟨fun s v ↦ ⟨s + v.x, s + v.y, s + v.z⟩⟩
      @[inline] instance : HAdd $v3Ty $sTy $v3Ty := ⟨fun v s ↦ ⟨v.x + s, v.y + s, v.z + s⟩⟩
      @[inline] instance : HSub $sTy $v3Ty $v3Ty := ⟨fun s v ↦ ⟨s - v.x, s - v.y, s - v.z⟩⟩
      @[inline] instance : HSub $v3Ty $sTy $v3Ty := ⟨fun v s ↦ ⟨v.x - s, v.y - s, v.z - s⟩⟩
      @[inline] instance : HDiv $sTy $v3Ty $v3Ty := ⟨fun s v ↦ ⟨s / v.x, s / v.y, s / v.z⟩⟩

      /-- Sum of components. -/
      @[inline]
      def sum (v : $v3Ty) : $sTy :=
        v.x + v.y + v.z

      /-- Product of components. -/
      @[inline]
      def product (v : $v3Ty) : $sTy :=
        v.x * v.y * v.z

      /-- Dot product of two vectors. -/
      @[inline]
      def dot (a b : $v3Ty) : $sTy :=
        a.x * b.x + a.y * b.y + a.z * b.z

      /-- Vector length squared. -/
      @[inline]
      def lengthSqr (v : $v3Ty) : $sTy :=
        dot v v

      end $v3Ty
    )

run_cmd
  Meta.forEachScalar Meta.scalars fun cx => do
    let sTy := cx.scalarType
    let v3Ty := cx.structure "Vector3"
    Lean.Elab.Command.elabCommand <| ← `(
      namespace $v3Ty
      /-- Converts a vector to a string of `(x y z)` format.` -/
      @[inline]
      def toString (v : $v3Ty) : String :=
        s!"({v.x} {v.y} {v.z})"

      @[inline]
      instance : ToString $v3Ty := ⟨toString⟩

      /-- Gets vector's component value. -/
      @[inline]
      def get (v : $v3Ty) : Axis3 → $sTy
      | .x => v.x
      | .y => v.y
      | .z => v.z

      @[inline]
      instance : GetElem $v3Ty Axis3 $sTy (fun _ _ => True) where
        getElem := Function.curry <| Function.const _ ∘ get.uncurry

      @[inline]
      instance : GetElem $v3Ty Nat $sTy (fun _ i => i < 3) where
        getElem v
        | 0, _ => v.x
        | 1, _ => v.y
        | 2, _ => v.z

      /-- Sets vector's component value. -/
      @[inline]
      def set (v : $v3Ty) : Axis3 → $sTy → $v3Ty
      | .x, x => .mk x   v.y v.z
      | .y, y => .mk v.x y   v.z
      | .z, z => .mk v.x v.y z

      /-- Minimal component of a vector. -/
      def minValue (v : $v3Ty) : $sTy :=
        Min.min v.x <| Min.min v.y v.z

      /-- Maximal component of a vector. -/
      def maxValue (v : $v3Ty) : $sTy :=
        Max.max v.x <| Max.max v.y v.z

      /--
      First minimal component axis.

      Panics in debug if any of the components is NaN.
      -/
      def minAxis (v : $v3Ty) : Axis3 :=
        debug_assert! v.x.isNaN || v.y.isNaN || v.z.isNaN
        if v.x <= v.y && v.x <= v.z then
          .x
        else if v.y <= v.x && v.y <= v.z then
          .y
        else
          .z

      /--
      First maximal component axis.

      Panics in debug if any of the components is NaN.
      -/
      def maxAxis (v : $v3Ty) : Axis3 :=
        debug_assert! v.x.isNaN || v.y.isNaN || v.z.isNaN
        if v.x >= v.y && v.x >= v.z then
          .x
        else if v.y >= v.x && v.y >= v.z then
          .y
        else
          .z

      /-- Creates a vector `⟨x, v.y, v.z⟩`. -/
      @[inline]
      def withX (v : $v3Ty) (x : $sTy) : $v3Ty :=
        .mk x v.y v.z

      /-- Creates a vector `⟨v.x, y, v.z⟩`. -/
      @[inline]
      def withY (v : $v3Ty) (y : $sTy) : $v3Ty :=
        .mk v.x y v.z

      /-- Creates a vector `⟨v.x, v.y, z⟩`. -/
      @[inline]
      def withZ (v : $v3Ty) (z : $sTy) : $v3Ty :=
        .mk v.x v.y z

      /-- Creates a vector with all elements set to `x`. -/
      @[inline]
      def splat (x : $sTy) : $v3Ty :=
        .mk x x x

      /-- Creates a vector from an array. Panics if the list's length is less than 3. -/
      @[inline]
      def ofList (a : List $sTy) : $v3Ty :=
        if h: a.length >= 3
          then .mk a[0] a[1] a[2]
          else panic! "list contains less than 3 values"

      /-- Creates a vector from an array. Panics if the array's size is less than 3. -/
      @[inline]
      def ofArray (a : Array $sTy) : $v3Ty :=
        if h: a.size >= 3
          then .mk a[0] a[1] a[2]
          else panic! "array contains less than 3 values"

      /-- Creates a vector from a fixed length array. -/
      @[inline]
      def ofVector (v : Vector $sTy 3) : $v3Ty :=
        .mk v[0] v[1] v[2]

      /-- Creates a list from vector components. -/
      @[inline]
      def toList (v : $v3Ty) : List $sTy :=
        [v.x, v.y, v.z]

      /-- Pushes vector components to an array. -/
      @[inline]
      def toArray (v : $v3Ty) (dst : Array $sTy := by exact Array.emptyWithCapacity 3) : Array $sTy :=
        dst.push v.x |>.push v.y |>.push v.z

      /-- Creates a fixed length array from vector components. -/
      @[inline]
      def toVector (v : $v3Ty) : Vector $sTy 3 :=
        Vector.emptyWithCapacity 3 |>.push v.x |>.push v.y |>.push v.z

      /-- Creates a vector with elements from `v` modified by `f`. -/
      @[inline]
      def map (f : $sTy → $sTy) (v : $v3Ty) : $v3Ty :=
        .mk (f v.x) (f v.y) (f v.z)

      @[inline]
      def select (mask : BVector3) (true false : $v3Ty) : $v3Ty :=
        .mk (cond mask.x true.x false.x) (cond mask.y true.y false.y) (cond mask.z true.z false.z)

      /-- Componentwise minimum. -/
      @[inline]
      def min' (a b : $v3Ty) : $v3Ty :=
        .mk (Min.min a.x b.x) (Min.min a.y b.y) (Min.min a.z b.z)

      /-- Componentwise maximum. -/
      @[inline]
      def max' (a b : $v3Ty) : $v3Ty :=
        .mk (Max.max a.x b.x) (Max.max a.y b.y) (Max.max a.z b.z)

      /-- Componentwise "less than". -/
      @[inline]
      def lt' (a b : $v3Ty) : BVector3 :=
        .mk (a.x < b.x) (a.y < b.y) (a.z < b.z)

      /-- Componentwise "less than or equal to". -/
      @[inline]
      def le' (a b : $v3Ty) : BVector3 :=
        .mk (a.x <= b.x) (a.y <= b.y) (a.z <= b.z)

      /-- Componentwise "greater than". -/
      @[inline]
      def gt' (a b : $v3Ty) : BVector3 :=
        .mk (a.x > b.x) (a.y > b.y) (a.z > b.z)

      /-- Componentwise "greater than or equal to". -/
      @[inline]
      def ge' (a b : $v3Ty) : BVector3 :=
        .mk (a.x >= b.x) (a.y >= b.y) (a.z >= b.z)

      /-- Returns `true` if application of `f` to *any* of the components returns `true`. -/
      @[inline]
      def any (f : $sTy → Bool) (v : $v3Ty) : Bool :=
        f v.x || f v.y || f v.z

      /-- Returns `true` if application of `f` to *each* component returns `true`. -/
      @[inline]
      def all (f : $sTy → Bool) (v : $v3Ty) : Bool :=
        f v.x && f v.y && f v.z

      /-- Whether componentwise "less than" is true on all axes. -/
      @[inline]
      def lt (a b : $v3Ty) : Prop :=
        a.x < b.x ∧ a.y < b.y ∧ a.z < b.z

      /-- Whether componentwise "less than or equal to" is true on all axes. -/
      @[inline]
      def le (a b : $v3Ty) : Prop :=
        a.x <= b.x ∧ a.y <= b.y ∧ a.z <= b.z

      @[inline] instance : LT $v3Ty := ⟨lt⟩
      @[inline] instance : LE $v3Ty := ⟨le⟩

      @[inline]
      instance : DecidableLT $v3Ty := fun a b => by
        unfold LT.lt instLT lt
        infer_instance

      @[inline]
      instance : DecidableLE $v3Ty := fun a b => by
        unfold LE.le instLE le
        infer_instance

      end $v3Ty
    )

-- run_cmd
--   Meta.forEachScalar Meta.floats fun cx => do
--     let sTy := cx.scalarType
--     let v3Ty := cx.structure "Vector3"
--     let sInf := cx.scalarExtMember "inf"
--     let sNegInf := cx.scalarExtMember "negInf"
--     let sClamp := cx.scalarExtMember "clamp"
--     let sSign := cx.scalarExtMember "sign"
--     let sSqrt := cx.scalarMember "sqrt"
--     let sIsFinite := cx.scalarMember "isFinite"
--     let sAbs := cx.scalarMember "abs"
--     Lean.Elab.Command.elabCommand <| ← `(
--       namespace $v3Ty

--       deriving instance BEq for $v3Ty

--       /-- All components set to NaN. -/
--       @[inline]
--       def nan : $v3Ty := splat (0 / 0)

--       /-- All components set to positive infinity. -/
--       @[inline]
--       def inf : $v3Ty := splat $sInf

--       /-- All components set to negative infinity. -/
--       @[inline]
--       def negInf : $v3Ty := splat $sNegInf

--       /--
--       Componentwise clamping of components.

--       Panics in debug if for any axis `min` > `max`, `min` is NaN, or `max` is NaN.
--       -/
--       @[inline]
--       def clamp (min max v : $v3Ty) : $v3Ty :=
--         ⟨$sClamp min.x max.x v.x, $sClamp min.y max.y v.y, $sClamp min.z max.z v.z⟩

--       /-- Componentwise sign (does not return zeros). -/
--       @[inline]
--       def sign (v : $v3Ty) : $v3Ty :=
--         ⟨$sSign v.x, $sSign v.y, $sSign v.z⟩

--       /-- Vector length. -/
--       @[inline]
--       def length (v : $v3Ty) : $sTy :=
--         $sSqrt <| lengthSqr v

--       /-- Distance between two points represented by vectors from any third point. -/
--       @[inline]
--       def distance (a b : $v3Ty) : $sTy :=
--         length (a - b)

--       /--
--       Normalizes vector to the length of `1`.

--       Returns `none` if the resulting vector is not finite.
--       -/
--       @[inline]
--       def normalize? (v : $v3Ty) : Option $v3Ty :=
--         let v' := v * (1 / v.length)
--         if v'.any <| not ∘ $sIsFinite
--           then none
--           else some v'

--       /--
--       Normalizes vector to the length of `1`.

--       Panics in debug if any component of `v/|v|` is not finite.
--       -/
--       @[inline]
--       def normalize (v : $v3Ty) : $v3Ty :=
--         let v' := v * (1 / v.length)
--         debug_assert! v'.any <| not ∘ $sIsFinite
--         v'

--       /-- Checks whether the length of `v` is 1. -/
--       @[inline]
--       def isNormalized (maxSqrDelta : $sTy := 2e-4) (v : $v3Ty) : Bool :=
--         $sAbs (v.lengthSqr - 1) <= maxSqrDelta

--       /--
--       Projection of `a` onto `b`.

--       Panics in debug if `1/|b|²` is not finite.
--       -/
--       @[inline]
--       def projectOnto (a b : $v3Ty) : $v3Ty :=
--         let invBSqrLen := 1 / b.lengthSqr
--         debug_assert! $sIsFinite invBSqrLen
--         b * (dot a b) * invBSqrLen

--       /--
--       Projection of `a` onto `b`.

--       Panics in debug if `b` is not normalized.
--       -/
--       @[inline]
--       def projectOntoNormalized (a b : $v3Ty) : $v3Ty :=
--         debug_assert! b.isNormalized
--         b * (dot a b)

--       /--
--       Rejection of `a` from `b`.

--       Rejection is the part of `a` that is missing from its projection
--       (`a = rejection + projection`).

--       Panics in debug if `1/|b|²` is not finite.
--       -/
--       @[inline]
--       def rejectFrom (a b : $v3Ty) : $v3Ty :=
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

run_cmd
  Meta.forEachScalar Meta.integers fun cx => do
    let v3Ty := cx.structure "Vector3"
    let sTy := cx.scalarType
    Lean.Elab.Command.elabCommand <| ← `(
      namespace $v3Ty

      deriving instance DecidableEq for $v3Ty

      /-- Componentwise bitwise `and`. -/
      @[inline]
      def and (a b : $v3Ty) : $v3Ty :=
        ⟨a.x &&& b.x, a.y &&& b.y, a.z &&& b.z⟩

      /-- Componentwise bitwise `or`. -/
      @[inline]
      def or (a b : $v3Ty) : $v3Ty :=
        ⟨a.x ||| b.x, a.y ||| b.y, a.z ||| b.z⟩

      /-- Componentwise bitwise `xor`. -/
      @[inline]
      def xor (a b : $v3Ty) : $v3Ty :=
        ⟨a.x ^^^ b.x, a.y ^^^ b.y, a.z ^^^ b.z⟩

      /-- Componentwise bitwise `complement` of a vector. -/
      @[inline]
      def complement (a : $v3Ty) : $v3Ty :=
        ⟨~~~a.x, ~~~a.y, ~~~a.z⟩

      @[inline] instance : AndOp $v3Ty := ⟨and⟩
      @[inline] instance : OrOp $v3Ty := ⟨or⟩
      @[inline] instance : XorOp $v3Ty := ⟨xor⟩
      @[inline] instance : Complement $v3Ty := ⟨complement⟩

      /-- Componentwise clamping of components. -/
      @[inline]
      def clamp (min max v : $v3Ty) : $v3Ty :=
        ⟨Max.max min.x (Min.min v.x max.x), Max.max min.y (Min.min v.y max.y), Max.max min.z (Min.min v.z max.z)⟩

      /-- Componentwise modulo. -/
      @[inline]
      def mod (a b : $v3Ty) : $v3Ty :=
        ⟨a.x % b.x, a.y % b.y, a.z % b.z⟩

      @[inline] instance : Mod $v3Ty := ⟨mod⟩
      @[inline] instance : HMod $v3Ty $sTy $v3Ty := ⟨fun v s => ⟨v.x % s, v.y % s, v.z % s⟩⟩
      @[inline] instance : HMod $sTy $v3Ty $v3Ty := ⟨fun s v => ⟨s % v.x, s % v.y, s % v.z⟩⟩

      end $v3Ty
    )

run_cmd
  Meta.forEachScalar Meta.signedIntegers fun cx => do
    let v3Ty := cx.structure "Vector3"
    Lean.Elab.Command.elabCommand <| ← `(
      namespace $v3Ty

      /-- Componentwise sign (does not return zeros). -/
      @[inline]
      def sign (v : $v3Ty) : $v3Ty :=
        ⟨cond (v.x < 0) (-1) 1, cond (v.y < 0) (-1) 1, cond (v.z < 0) (-1) 1⟩

      end $v3Ty
    )

run_cmd
  Meta.forEachScalar Meta.signed fun cx => do
    let v3Ty := cx.structure "Vector3"
    let sTy := cx.scalarType
    let sAbs := cx.scalarMember "abs"
    Lean.Elab.Command.elabCommand <| ← `(
      namespace $v3Ty

      /-- Computes absolute values of components. -/
      @[inline]
      def abs (v : $v3Ty) : $v3Ty :=
        ⟨$sAbs v.x, $sAbs v.y, $sAbs v.z⟩

      /-- Squared distance between two points represented by vectors from any third point. -/
      @[inline]
      def distanceSqr (a b : $v3Ty) : $sTy :=
        lengthSqr <| a - b

      /--
      `|a||b|sin(θ)n`

      The cross product is defined as a vector that is orthogonal to both `a` and `b`,
      with a direction given by the right-hand rule ("forward" × "left" = "up")
      and a magnitude equal to the area of the parallelogram with the vectors for sides.
      -/
      @[inline]
      def cross (a b : $v3Ty) : $v3Ty :=
        ⟨a.y * b.z - a.z * b.y, a.z * b.x - a.x * b.z, a.x * b.y - a.y * b.x⟩

      end $v3Ty
    )

run_cmd
  Meta.forEachScalar Meta.unsignedIntegers fun cx => do
    let v3Ty := cx.structure "Vector3"
    let sTy := cx.scalarType
    Lean.Elab.Command.elabCommand <| ← `(
      namespace $v3Ty

      /-- Squared distance between two points represented by vectors from any third point. -/
      @[inline]
      def distanceSqr (a b : $v3Ty) : $sTy :=
        let x := if a.x >= b.x then a.x - b.x else b.x - a.x
        let y := if a.y >= b.y then a.y - b.y else b.y - a.y
        let y := if a.z >= b.z then a.z - b.z else b.z - a.z
        x * x + y * y + y * y

      end $v3Ty
    )

run_cmd
  Meta.forEachScalar Meta.numbers fun cx1 =>
    let v3Ty1 := cx1.structure "Vector3"
    Meta.forEachScalar Meta.numbers fun cx2 => do
      let v3Ty2 := cx2.structure "Vector3"
      if let some s1To2 ← Meta.scalarConvertFn? cx1 cx2 then
        let toV3Ty2 := cx1.structureMember "Vector3" <| "to" ++ cx2.scalarPrefix
        Lean.Elab.Command.elabCommand <| ← `(
          @[inline]
          def $toV3Ty2 (v : $v3Ty1) : $v3Ty2 :=
            .mk ($s1To2 v.x) ($s1To2 v.y) ($s1To2 v.z)
        )
        Lean.addDocStringCore (← Lean.resolveGlobalConstNoOverload toV3Ty2)
          s!"Componentwise conversion to `{cx2.scalarTypeName}` scalar type using `{s1To2.getId}`"
      if let some s2To1 ← Meta.scalarConvertFn? cx2 cx1 then
        let ofV3Ty2 := cx1.structureMember "Vector3" <| "of" ++ cx2.scalarPrefix
        Lean.Elab.Command.elabCommand <| ← `(
          @[inline]
          def $ofV3Ty2 (v : $v3Ty2) : $v3Ty1 :=
            .mk ($s2To1 v.x) ($s2To1 v.y) ($s2To1 v.z)
        )
        Lean.addDocStringCore (← Lean.resolveGlobalConstNoOverload ofV3Ty2)
          s!"Componentwise conversion from `{cx2.scalarTypeName}` scalar type using `{s2To1.getId}`"

/--
Creates a vector from a scalar array.

Panics if the array's size is less than 3.
-/
@[inline]
def F64Vector3.ofFloatArray (a : FloatArray) : F64Vector3 :=
  if h: a.size >= 3
    then ⟨a[0], a[1], a[2]⟩
    else panic! "array contains less than 3 values"

/-- Pushes vector components to a scalar array. -/
@[inline]
def F64Vector3.toFloatArray
  (v : F64Vector3) (dst : FloatArray := by exact FloatArray.emptyWithCapacity 3) : FloatArray :=
    dst.push v.x |>.push v.y |>.push v.z
