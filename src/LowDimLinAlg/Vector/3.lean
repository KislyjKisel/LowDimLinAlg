module

public import LowDimLinAlg.Axis
public import LowDimLinAlg.Scalar

import LowDimLinAlg.Meta.ForEachScalar

@[expose] public section

set_option hygiene false

namespace LowDimLinAlg

structure BVector3 where
  /--
  Creates vector from bitwise representation where
  `x` is the first bit, `y` - the second, `z` - the third.
  -/
  ofBits ::
  /--
  Bitwise representation of the vector where
  `x` is the first bit, `y` - the second, `z` - the third.
  -/
  bits : UInt8
  /-- Only the first 3 bits may be set. -/
  length3 : bits &&& 0b111 = bits
deriving DecidableEq

@[inline]
instance : Inhabited BVector3 :=
  ⟨{ bits := 0, length3 := by decide }⟩

/-- Creates vector from components. -/
@[inline]
def BVector3.mk (x y z : Bool) : BVector3 :=
  let xBit : UInt8 := cond x 1 0
  let yBit : UInt8 := cond y 1 0
  let zBit : UInt8 := cond z 1 0
  .ofBits (xBit ||| yBit <<< 1 ||| zBit <<< 2) <| by
    cases x <;> cases y <;> cases z <;> decide

@[inline]
def BVector3.x (v : BVector3) : Bool :=
  v.bits &&& 0b001 != 0

@[inline]
def BVector3.y (v : BVector3) : Bool :=
  v.bits &&& 0b010 != 0

@[inline]
def BVector3.z (v : BVector3) : Bool :=
  v.bits &&& 0b100 != 0

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

      /-- Negation of a vector. -/
      @[inline]
      def neg (v : $v3Ty) : $v3Ty :=
        ⟨-v.x, -v.y, -v.z⟩

      /-- Componentwise multiplication of a vector by a scalar (integers wrap on underflow and overflow). -/
      @[inline]
      def scale (s : $sTy) (v : $v3Ty) : $v3Ty :=
        ⟨v.x * s, v.y * s, v.z * s⟩

      @[inline] instance : Add $v3Ty := ⟨add⟩
      @[inline] instance : Sub $v3Ty := ⟨sub⟩
      @[inline] instance : Mul $v3Ty := ⟨mul⟩
      @[inline] instance : Div $v3Ty := ⟨div⟩
      @[inline] instance : Neg $v3Ty := ⟨neg⟩
      @[inline] instance : SMul $sTy $v3Ty := ⟨scale⟩

      @[inline] instance : HAdd $sTy $v3Ty $v3Ty := ⟨fun s v ↦ ⟨s + v.x, s + v.y, s + v.z⟩⟩
      @[inline] instance : HAdd $v3Ty $sTy $v3Ty := ⟨fun v s ↦ ⟨v.x + s, v.y + s, v.z + s⟩⟩
      @[inline] instance : HSub $sTy $v3Ty $v3Ty := ⟨fun s v ↦ ⟨s - v.x, s - v.y, s - v.z⟩⟩
      @[inline] instance : HSub $v3Ty $sTy $v3Ty := ⟨fun v s ↦ ⟨v.x - s, v.y - s, v.z - s⟩⟩
      @[inline] instance : HMul $v3Ty $sTy $v3Ty := ⟨fun v s ↦ v.scale s⟩
      @[inline] instance : HMul $sTy $v3Ty $v3Ty := ⟨scale⟩
      @[inline] instance : HDiv $v3Ty $sTy $v3Ty := ⟨fun v s ↦ v.scale (1 / s)⟩
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
