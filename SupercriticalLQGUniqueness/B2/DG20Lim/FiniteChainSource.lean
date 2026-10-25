import SupercriticalLQGUniqueness.B2.DG20Lim.CircleChainSep
import SupercriticalLQGUniqueness.B2.DG20Lim.FiniteChainGlobal

 

set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

 

theorem finiteCircleDist_chain
    (D : LQGMetric.ContMetric) (hD : D.IsLength)
    (k : ℕ) (O : Fin (k + 1) → RatCircle)
    (hdisj : ∀ i j : Fin (k + 1), i ≠ j →
      Disjoint (O i).toSet (O j).toSet)
    (hsep : ∀ j : ℕ, (hj : 0 < j) → (hjk : j < k) →
      Disconnects (O ⟨j, by omega⟩).toSet
        (O ⟨j - 1, by omega⟩).toSet
        (O ⟨j + 1, by omega⟩).toSet) :
    (∑ j : Fin k,
      LQGMetric.Blueprint.setDist D
        (O ⟨j.val, by omega⟩).toSet
        (O ⟨j.val + 1, by omega⟩).toSet) ≤
      LQGMetric.Blueprint.setDist D
        (O ⟨0, by omega⟩).toSet (O ⟨k, by omega⟩).toSet := by
  let O' : ℕ → RatCircle := fun j => O ⟨min j k, by omega⟩
  have hO' (j : ℕ) (hj : j ≤ k) : O' j = O ⟨j, by omega⟩ := by
    simp [O', Nat.min_eq_left hj]
  have hglobal := circle_chain_global_separator k O hdisj hsep
  have hsep' : ∀ j, 0 < j → j < k →
      Disconnects (O' j).toSet (O' 0).toSet (O' (j + 1)).toSet := by
    intro j hj hjk
    simpa only [hO' j (by omega), hO' 0 (by omega),
      hO' (j + 1) (by omega)] using hglobal j hj hjk
  have hchain := finiteCircleDist_chain_of_global_sep D hD O' k hsep'
  calc
    _ = ∑ j ∈ Finset.range k,
        LQGMetric.Blueprint.setDist D (O' j).toSet (O' (j + 1)).toSet := by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro j hj
      have hjk : j < k := Finset.mem_range.mp hj
      simp [hjk, hO' j (by omega), hO' (j + 1) (by omega)]
    _ ≤ _ := by simpa [hO'] using hchain

end SupercriticalLQGUniqueness.B2.DG20Lim
