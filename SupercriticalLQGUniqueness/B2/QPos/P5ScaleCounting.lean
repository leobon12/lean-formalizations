import Mathlib.Data.Finset.Card
import Mathlib.Tactic

 



set_option autoImplicit false
noncomputable section

namespace SupercriticalLQGUniqueness.B2.QPos

theorem many_good_scales_intersection {α : Type*} [DecidableEq α]
    (F A B : Finset α) (K : ℕ)
    (hA : A ⊆ F) (hB : B ⊆ F)
    (hF : 2 * F.card ≤ K)
    (hAc : 3 * K ≤ 8 * A.card)
    (hBc : 3 * K ≤ 8 * B.card) :
    K ≤ 4 * (A ∩ B).card := by
  have hu : (A ∪ B).card ≤ F.card :=
    Finset.card_le_card (Finset.union_subset hA hB)
  have hcount := Finset.card_union_add_card_inter A B
  omega

theorem many_good_scales_nonempty {α : Type*} [DecidableEq α]
    (F A B : Finset α) (K : ℕ)
    (hK : 0 < K) (hA : A ⊆ F) (hB : B ⊆ F)
    (hF : 2 * F.card ≤ K)
    (hAc : 3 * K ≤ 8 * A.card)
    (hBc : 3 * K ≤ 8 * B.card) :
    (A ∩ B).Nonempty := by
  have h := many_good_scales_intersection F A B K hA hB hF hAc hBc
  by_contra hn
  have hzero : (A ∩ B).card = 0 := Finset.card_eq_zero.mpr
    (Finset.not_nonempty_iff_eq_empty.mp hn)
  omega

end SupercriticalLQGUniqueness.B2.QPos
