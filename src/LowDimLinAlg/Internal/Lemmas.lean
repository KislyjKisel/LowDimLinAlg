module

import all Init.Data.FloatArray.Basic

public section

namespace LowDimLinAlg.Lemmas

theorem spanIndex
  (size span index : Nat)
  (offset : USize)
  (size_le : size ≤ USize.size)
  (le_size : offset.toNat + span ≤ size)
  (index_lt : index < span) :
    (offset + OfNat.ofNat index).toNat < size := by
      have h1 : index < USize.size := by
        apply Nat.lt_of_lt_of_le index_lt
        apply Nat.le_trans _ (Nat.le_trans le_size size_le)
        apply Nat.le_add_left
      have h2 : offset.toNat + index < size := by
        apply Nat.lt_of_lt_of_le _ le_size
        apply Nat.add_lt_add_left index_lt
      rewrite [
        USize.toNat_add,
        USize.toNat_ofNat,
        Nat.mod_eq_of_lt h1,
        Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h2 size_le),
      ]
      exact h2

theorem spanIndexNat
  (size span offset : Nat)
  (size_le : size ≤ USize.size)
  (le_size : offset + span ≤ size) :
    offset.toUSize.toNat + span ≤ size := by
      rewrite [
        Nat.toUSize_eq,
        USize.toNat_ofNat',
      ]
      cases Nat.eq_zero_or_pos span
      case inl h =>
        apply Nat.le_trans _ le_size
        rewrite [h, Nat.add_zero, Nat.add_zero]
        apply Nat.mod_le
      case inr =>
        rewrite [Nat.mod_eq_of_lt]
        exact le_size
        apply Nat.lt_of_lt_of_le _ (Nat.le_trans le_size size_le)
        apply Nat.lt_add_of_pos_right
        assumption

theorem FloatArray_size_uset (a : FloatArray) (i x h) : (a.uset i x h).size = a.size := by
  rw [
    FloatArray.uset,
    FloatArray.size,
    Array.size_uset,
    FloatArray.size,
  ]
