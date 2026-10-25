import SupercriticalLQGUniqueness.B2.DG20Lim.RightEndpoint

 


set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem RData.chain_le_DfromR_of_adjacent (R : RData)
    (k : ℕ) (hk : 0 < k) (O : Fin (k + 1) → RatCircle)
    (z w : ℂ) (hzw : z ≠ w)
    (hdisj : ∀ i j : Fin (k + 1), i ≠ j →
      Disjoint (O i).toSet (O j).toSet)
    (hsep : ∀ j : ℕ, (hj : 0 < j) → (hjk : j < k) →
      Disconnects (O ⟨j, by omega⟩).toSet
        (O ⟨j - 1, by omega⟩).toSet
        (O ⟨j + 1, by omega⟩).toSet)
    (hz : (O ⟨0, by omega⟩).DisconnectsPoint z
      (O ⟨1, by omega⟩))
    (hw : (O ⟨k, by omega⟩).DisconnectsPoint w
      (O ⟨k - 1, by omega⟩)) :
    (∑ j : Fin k, R.across (O ⟨j.val, by omega⟩)
      (O ⟨j.val + 1, by omega⟩)) ≤ R.DfromR z w := by
  have hz' := left_endpoint_disconnects_chain k hk O z hdisj hsep hz
  have hw' := right_endpoint_disconnects_chain k hk O w hdisj hsep hw
  exact R.chain_le_DfromR_of_endpoint_separators k hk O z w hzw
    hdisj hsep hz' hw'

end SupercriticalLQGUniqueness.B2.DG20Lim
