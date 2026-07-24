module

public import LowDimLinAlg.Vector.Types

import LowDimLinAlg.Internal.Dimensionalities
import LowDimLinAlg.Internal.Syntax

@[expose] public section

set_option hygiene false

namespace LowDimLinAlg

open Internal

run_cmd
  for dims in dimensionalities do
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
    let mkAxes := dims.map fun dim =>
      Prod.mk dim <| Lean.mkIdent <| .mkSimple <| dim.str ++ "Bit"
    let mkTactic : Lean.TSyntax `tactic ←
      dims.foldrM
        (fun dim r => `(tactic| cases $dim.ident:ident <;> $r))
        (← `(tactic| decide))
    Lean.Elab.Command.elabCommand <| ← `(
      /-- Creates a vector from components. -/
      @[inline]
      def mk ($(dims.map fun dim => dim.ident)* : Bool) : $bvTy :=
        $(← mkAxes.foldrM
            (fun (dim, v) r => lets v (app ``cond #[dim.ident, lit1, lit0]) r)
            (app `ofBits #[
              foldBinopL mkAxes ``OrOp.or (fun (dim, v) => if dim.index == 0 then v else app ``ShiftLeft.shiftLeft #[v, Lean.Syntax.mkNatLit dim.index]),
              ← `(by $mkTactic:tactic),
            ])
        )

      instance : Repr $bvTy where
        reprPrec v _ :=
          let fields : List Std.Format := [
            Std.Format.joinSep [
              "bits",
              ":=",
              "0b".append <| String.ofList <| (Nat.toDigits 2 v.bits.toNat).leftpad $dimsSizeLit '0'
            ] " ",
            Std.Format.joinSep ["and_mask_eq_self", ":=", "by", "decide"] " ",
          ]
          Std.Format.bracket "{" (Std.Format.joinSep fields <| "," ++ Std.Format.line) "}"

      /--
      Creates vector from bitwise representation
      where bits that don't represent any component values are zeroed.
      -/
      @[inline]
      def ofBitsMasked (bits : UInt8) : $bvTy :=
        .ofBits (bits &&& $bvMask) (by rw [UInt8.and_assoc, UInt8.and_self])

      /-- Componentwise boolean `and`. -/
      @[inline]
      def and (a b : $bvTy) : $bvTy :=
        .ofBits (a.bits &&& b.bits) <| by
          rw [UInt8.and_assoc, b.and_mask_eq_self]

      private
      theorem toNat_and_mask_eq_self (v : $bvTy) : v.bits.toNat &&& $bvMask = v.bits.toNat := by
        exact UInt8.toNat_inj.mpr v.and_mask_eq_self

      /-- Componentwise boolean `or`. -/
      @[inline]
      def or (a b : $bvTy) : $bvTy :=
        .ofBits (a.bits ||| b.bits) <| by
          apply UInt8.toNat_inj.mp
          show (a.bits.toNat ||| b.bits.toNat) &&& $bvMask = a.bits.toNat ||| b.bits.toNat
          rw [Nat.and_or_distrib_right, toNat_and_mask_eq_self a, toNat_and_mask_eq_self b]

      /-- Componentwise boolean `xor`. -/
      @[inline]
      def xor (a b : $bvTy) : $bvTy :=
        .ofBits (a.bits ^^^ b.bits) <| by
          apply UInt8.toNat_inj.mp
          show (a.bits.toNat ^^^ b.bits.toNat) &&& $bvMask = a.bits.toNat ^^^ b.bits.toNat
          rw [Nat.and_xor_distrib_right, toNat_and_mask_eq_self a, toNat_and_mask_eq_self b]

      /-- Componentwise boolean `not`. -/
      @[inline]
      def not (v : $bvTy) : $bvTy :=
        .ofBitsMasked v.bits.complement

      @[inline]
      instance : AndOp $bvTy := ⟨and⟩

      @[inline]
      instance : OrOp $bvTy := ⟨or⟩

      @[inline]
      instance : XorOp $bvTy := ⟨xor⟩

      @[inline]
      instance : Complement $bvTy := ⟨not⟩

      end $bvTy
    )
