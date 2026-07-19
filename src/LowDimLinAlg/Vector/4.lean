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
    let v4Ty := cx.structure "Vector4"
    Lean.Elab.Command.elabCommand <| ← `(
      structure $v4Ty where
        x : $sTy
        y : $sTy
        z : $sTy
        w : $sTy
      deriving Repr, Inhabited

      namespace $v4Ty

      /-- All components set to 0. -/
      @[inline]
      def zero : $v4Ty := ⟨0, 0, 0, 0⟩

      /-- All components set to 1. -/
      @[inline]
      def one : $v4Ty := ⟨1, 1, 1, 1⟩

      /-- All components set to -1. -/
      @[inline]
      def negOne : $v4Ty := ⟨-1, -1, -1, -1⟩

      /-- A unit vector pointing along the positive X axis. -/
      @[inline]
      def unitX : $v4Ty := ⟨1, 0, 0, 0⟩

      /-- A unit vector pointing along the positive Y axis. -/
      @[inline]
      def unitY : $v4Ty := ⟨0, 1, 0, 0⟩

      /-- A unit vector pointing along the positive Z axis. -/
      @[inline]
      def unitZ : $v4Ty := ⟨0, 0, 1, 0⟩

      /-- A unit vector pointing along the positive W axis. -/
      @[inline]
      def unitW : $v4Ty := ⟨0, 0, 0, 1⟩

      /-- A unit vector pointing along the negative X axis. -/
      @[inline]
      def unitNegX : $v4Ty := ⟨-1, 0, 0, 0⟩

      /-- A unit vector pointing along the negative Y axis. -/
      @[inline]
      def unitNegY : $v4Ty := ⟨0, -1, 0, 0⟩

      /-- A unit vector pointing along the negative Z axis. -/
      @[inline]
      def unitNegZ : $v4Ty := ⟨0, 0, -1, 0⟩

      /-- A unit vector pointing along the negative Z axis. -/
      @[inline]
      def unitNegW : $v4Ty := ⟨0, 0, 0, -1⟩

      /-- Creates a vector with results of applying `f` to each component. -/
      @[inline]
      def mapBool (f : $sTy → Bool) (v : $v4Ty) : BVector4 :=
        .mk (f v.x) (f v.y) (f v.z) (f v.w)

      /-- Componentwise addition (integers wrap on underflow and overflow). -/
      @[inline]
      def add (a b : $v4Ty) : $v4Ty :=
        ⟨a.x + b.x, a.y + b.y, a.z + b.z, a.w + b.w⟩

      /-- Componentwise subtraction (integers wrap on underflow and overflow). -/
      @[inline]
      def sub (a b : $v4Ty) : $v4Ty :=
        ⟨a.x - b.x, a.y - b.y, a.z - b.z, a.w - b.w⟩

      /-- Componentwise multiplication (integers wrap on underflow and overflow). -/
      @[inline]
      def mul (a b : $v4Ty) : $v4Ty :=
        ⟨a.x * b.x, a.y * b.y, a.z * b.z, a.w * b.w⟩

      /-- Componentwise division (integers wrap on underflow and overflow). -/
      @[inline]
      def div (a b : $v4Ty) : $v4Ty :=
        ⟨a.x / b.x, a.y / b.y, a.z / b.z, a.w / b.w⟩

      /-- Negation of a vector. -/
      @[inline]
      def neg (v : $v4Ty) : $v4Ty :=
        ⟨-v.x, -v.y, -v.z, -v.w⟩

      /-- Componentwise multiplication of a vector by a scalar (integers wrap on underflow and overflow). -/
      @[inline]
      def scale (s : $sTy) (v : $v4Ty) : $v4Ty :=
        ⟨v.x * s, v.y * s, v.z * s, v.w * s⟩

      @[inline] instance : Add $v4Ty := ⟨add⟩
      @[inline] instance : Sub $v4Ty := ⟨sub⟩
      @[inline] instance : Mul $v4Ty := ⟨mul⟩
      @[inline] instance : Div $v4Ty := ⟨div⟩
      @[inline] instance : Neg $v4Ty := ⟨neg⟩
      @[inline] instance : SMul $sTy $v4Ty := ⟨scale⟩

      @[inline] instance : HAdd $sTy $v4Ty $v4Ty := ⟨fun s v ↦ ⟨s + v.x, s + v.y, s + v.z, s + v.w⟩⟩
      @[inline] instance : HAdd $v4Ty $sTy $v4Ty := ⟨fun v s ↦ ⟨v.x + s, v.y + s, v.z + s, v.w + s⟩⟩
      @[inline] instance : HSub $sTy $v4Ty $v4Ty := ⟨fun s v ↦ ⟨s - v.x, s - v.y, s - v.z, s - v.w⟩⟩
      @[inline] instance : HSub $v4Ty $sTy $v4Ty := ⟨fun v s ↦ ⟨v.x - s, v.y - s, v.z - s, v.w - s⟩⟩
      @[inline] instance : HMul $v4Ty $sTy $v4Ty := ⟨fun v s ↦ v.scale s⟩
      @[inline] instance : HMul $sTy $v4Ty $v4Ty := ⟨scale⟩
      @[inline] instance : HDiv $v4Ty $sTy $v4Ty := ⟨fun v s ↦ v.scale (1 / s)⟩
      @[inline] instance : HDiv $sTy $v4Ty $v4Ty := ⟨fun s v ↦ ⟨s / v.x, s / v.y, s / v.z, s / v.w⟩⟩

      /-- Sum of components. -/
      @[inline]
      def sum (v : $v4Ty) : $sTy :=
        v.x + v.y + v.z + v.w

      /-- Product of components. -/
      @[inline]
      def product (v : $v4Ty) : $sTy :=
        v.x * v.y * v.z * v.w

      /-- Dot product of two vectors. -/
      @[inline]
      def dot (a b : $v4Ty) : $sTy :=
        a.x * b.x + a.y * b.y + a.z * b.z + a.w * b.w

      /-- Vector length squared. -/
      @[inline]
      def lengthSqr (v : $v4Ty) : $sTy :=
        dot v v

      end $v4Ty
    )
