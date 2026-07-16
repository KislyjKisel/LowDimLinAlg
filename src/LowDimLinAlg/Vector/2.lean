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
    let sTy := cx.scalarTypeIdent
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

      @[inline]
      def dot (a b : $v2Ty) : $sTy :=
        a.x * b.x + a.y * b.y

      end $v2Ty
    )

run_cmd
  Meta.forEachScalar Meta.scalars fun cx => do
    let sTy := cx.scalarTypeIdent
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
      def min' (v : $v2Ty) : $sTy :=
        Min.min v.x v.y

      /-- Maximal component of a vector. -/
      def max' (v : $v2Ty) : $sTy :=
        Max.max v.x v.y

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
      def lt (a b : $v2Ty) : BVector2 :=
        .mk (a.x < b.x) (a.y < b.y)

      /-- Componentwise "less than or equal to". -/
      @[inline]
      def le (a b : $v2Ty) : BVector2 :=
        .mk (a.x <= b.x) (a.y <= b.y)

      /-- Componentwise "greater than". -/
      @[inline]
      def gt (a b : $v2Ty) : BVector2 :=
        .mk (a.x > b.x) (a.y > b.y)

      /-- Componentwise "greater than or equal to". -/
      @[inline]
      def ge (a b : $v2Ty) : BVector2 :=
        .mk (a.x >= b.x) (a.y >= b.y)

      @[inline] instance : Min $v2Ty := ⟨min⟩
      @[inline] instance : Max $v2Ty := ⟨max⟩

      end $v2Ty
    )

run_cmd
  Meta.forEachScalar Meta.floats fun cx => do
    let sInf := cx.scalarMember "inf"
    let sNegInf := cx.scalarMember "negInf"
    let v2Ty := cx.structure "Vector2"
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
