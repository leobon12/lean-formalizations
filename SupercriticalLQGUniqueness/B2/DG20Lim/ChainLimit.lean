import SupercriticalLQGUniqueness.B2.DG20Lim.ChainOne

 

set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

 



theorem RData.chain_le_DfromR_of_endpoint_separators (R : RData)
    (k : ℕ) (hk : 0 < k) (O : Fin (k + 1) → RatCircle)
    (z w : ℂ) (hzw : z ≠ w)
    (hdisj : ∀ i j : Fin (k + 1), i ≠ j →
      Disjoint (O i).toSet (O j).toSet)
    (hsep : ∀ j : ℕ, (hj : 0 < j) → (hjk : j < k) →
      Disconnects (O ⟨j, by omega⟩).toSet
        (O ⟨j - 1, by omega⟩).toSet
        (O ⟨j + 1, by omega⟩).toSet)
    (hz : (O ⟨0, by omega⟩).DisconnectsPoint z (O ⟨k, by omega⟩))
    (hw : (O ⟨k, by omega⟩).DisconnectsPoint w (O ⟨0, by omega⟩)) :
    (∑ j : Fin k, R.across (O ⟨j.val, by omega⟩)
      (O ⟨j.val + 1, by omega⟩)) ≤ R.DfromR z w := by
  have hne : (⟨0, by omega⟩ : Fin (k + 1)) ≠ ⟨k, by omega⟩ := by
    intro h
    have heq := congrArg Fin.val h
    simp at heq
    omega
  exact (R.chain_lower k O hdisj hsep).trans
    (R.across_le_DfromR_of_two_circle_chain
      (O ⟨0, by omega⟩) (O ⟨k, by omega⟩) z w hzw
      (hdisj _ _ hne) hz hw)

end SupercriticalLQGUniqueness.B2.DG20Lim
