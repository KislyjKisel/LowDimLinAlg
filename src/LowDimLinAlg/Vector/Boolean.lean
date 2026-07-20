module

public import LowDimLinAlg.Vector.Types

import LowDimLinAlg.Internal.Dimensionalities

@[expose] public section

set_option hygiene false

namespace LowDimLinAlg

open Internal

run_cmd
  for dims in dimensionalities 2 4 do
    let bvName := Lean.Name.mkSimple <| "BVector" ++ toString dims.size
    let bvTy := Lean.mkIdent bvName
    let bvMask := Lean.Syntax.mkNatLit <| (1 <<< dims.size) - 1
    let dimsSizeLit := Lean.Syntax.mkNatLit dims.size
    Lean.Elab.Command.elabCommand <| ← `(
      @[inline]
      instance : Inhabited $bvTy :=
        ⟨{ bits := 0, and_mask_eq_self := by decide }⟩

      namespace $bvTy
    )
    for dim in dims do
      let accessor := Lean.mkIdent <| .mkSimple <| toString dim.char
      let mask := Lean.Syntax.mkNatLit <| 1 <<< dim.index
      Lean.Elab.Command.elabCommand <| ← `(
        @[inline]
        def $accessor (v : $bvTy) : Bool :=
          v.bits &&& $mask != 0
      )
    Lean.Elab.Command.elabCommand <| ← `(
      instance : Repr BVector2 where
        reprPrec v _ :=
          let fields : List Std.Format := [
            Std.Format.joinSep [
              "bits",
              ":=",
              "0b".append <| String.ofList <| (Nat.toDigits 2 v.bits.toNat).leftpad $dimsSizeLit '0'
            ] " ",
            Std.Format.joinSep ["length2", ":=", "by", "decide"] " ",
          ]
          Std.Format.bracket "{" (Std.Format.joinSep fields <| "," ++ Std.Format.line) "}"

      /--
      Creates vector from bitwise representation
      where bits that don't represent any component values are zeroed.
      -/
      @[inline]
      def ofBits' (bits : UInt8) : $bvTy :=
        .ofBits (bits &&& $bvMask) (by rw [UInt8.and_assoc, UInt8.and_self])

      /-- Componentwise boolean `and`. -/
      @[inline]
      def and (a b : BVector2) : BVector2 :=
        .ofBits (a.bits &&& b.bits) <| by
          rw [UInt8.and_assoc, b.and_mask_eq_self]

      private
      theorem toNat_and_mask_eq_self (v : $bvTy) : v.bits.toNat &&& $bvMask = v.bits.toNat := by
        exact UInt8.toNat_inj.mpr v.and_mask_eq_self

      /-- Componentwise boolean `or`. -/
      @[inline]
      def or (a b : $bvTy) : $bvTy :=
        .ofBits (a.bits ||| b.bits) <| by
          apply UInt8.eq_of_toFin_eq
          apply Fin.eq_of_val_eq
          show (a.bits.toNat ||| b.bits.toNat) &&& $bvMask = a.bits.toNat ||| b.bits.toNat
          rw [Nat.and_or_distrib_right, toNat_and_mask_eq_self a, toNat_and_mask_eq_self b]

      /-- Componentwise boolean `xor`. -/
      @[inline]
      def xor (a b : $bvTy) : $bvTy :=
        .ofBits (a.bits ^^^ b.bits) <| by
          apply UInt8.eq_of_toFin_eq
          apply Fin.eq_of_val_eq
          show (a.bits.toNat ^^^ b.bits.toNat) &&& $bvMask = a.bits.toNat ^^^ b.bits.toNat
          rw [Nat.and_xor_distrib_right, toNat_and_mask_eq_self a, toNat_and_mask_eq_self b]

      /-- Componentwise boolean `not`. -/
      @[inline]
      def not (v : $bvTy) : $bvTy :=
        .ofBits' v.bits.complement

      @[inline]
      instance : AndOp BVector2 := ⟨BVector2.and⟩

      @[inline]
      instance : OrOp BVector2 := ⟨BVector2.or⟩

      @[inline]
      instance : XorOp BVector2 := ⟨BVector2.xor⟩

      @[inline]
      instance : Complement BVector2 := ⟨BVector2.not⟩

      end $bvTy
    )

/-- Creates vector from components. -/
@[inline]
def BVector2.mk (x y : Bool) : BVector2 :=
  let xBit : UInt8 := cond x 1 0
  let yBit : UInt8 := cond y 1 0
  .ofBits (xBit ||| yBit <<< 1) <| by
    cases x <;> cases y <;> decide

/-- Creates vector from components. -/
@[inline]
def BVector3.mk (x y z : Bool) : BVector3 :=
  let xBit : UInt8 := cond x 1 0
  let yBit : UInt8 := cond y 1 0
  let zBit : UInt8 := cond z 1 0
  .ofBits (xBit ||| yBit <<< 1 ||| zBit <<< 2) <| by
    cases x <;> cases y <;> cases z <;> decide

/-- Creates vector from components. -/
@[inline]
def BVector4.mk (x y z w : Bool) : BVector4 :=
  let xBit : UInt8 := cond x 1 0
  let yBit : UInt8 := cond y 1 0
  let zBit : UInt8 := cond z 1 0
  let wBit : UInt8 := cond w 1 0
  .ofBits (xBit ||| yBit <<< 1 ||| zBit <<< 2 ||| wBit <<< 3) <| by
    cases x <;> cases y <;> cases z <;> cases w <;> decide
