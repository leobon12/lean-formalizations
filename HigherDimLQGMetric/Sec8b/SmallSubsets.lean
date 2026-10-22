import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! A finite counting bound for sets of size at most `k`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace HigherDimLQGMetric

open Classical

/-- The number of subsets of a finite universe of cardinality at most `k`
is polynomial of degree `k` in the size of the universe. The harmless factor
`k+1` is independent of the lattice scale. -/
theorem s7b_card_small_subsets_le {α : Type*} [DecidableEq α]
    (U : Finset α) (S : Finset (Finset α)) (k : ℕ)
    (hS : ∀ t ∈ S, t ⊆ U ∧ t.card ≤ k) :
    S.card ≤ (k + 1) * (U.card + 1) ^ k := by
  have hsub : S ⊆ (Finset.range (k + 1)).biUnion
      (fun i => U.powersetCard i) := by
    intro t ht
    obtain ⟨hU, hk⟩ := hS t ht
    exact Finset.mem_biUnion.mpr
      ⟨t.card, Finset.mem_range.mpr (Nat.lt_succ_of_le hk),
        Finset.mem_powersetCard.mpr ⟨hU, rfl⟩⟩
  calc
    S.card ≤ ((Finset.range (k + 1)).biUnion
        (fun i => U.powersetCard i)).card := Finset.card_le_card hsub
    _ ≤ ∑ i ∈ Finset.range (k + 1), (U.powersetCard i).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _i ∈ Finset.range (k + 1), (U.card + 1) ^ k := by
      apply Finset.sum_le_sum
      intro i hi
      have hik : i ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
      calc
        (U.powersetCard i).card = U.card.choose i :=
          Finset.card_powersetCard i U
        _ ≤ U.card ^ i := Nat.choose_le_pow _ _
        _ ≤ (U.card + 1) ^ i :=
          (pow_le_pow_left₀ (Nat.zero_le _)
            (Nat.le_succ _) i)
        _ ≤ (U.card + 1) ^ k :=
          pow_le_pow_right₀ (Nat.succ_le_succ (Nat.zero_le _)) hik
    _ = (k + 1) * (U.card + 1) ^ k := by simp

end HigherDimLQGMetric
