import HigherDimLQGMetric.Amplify.BackTransfer

/-! Reuse the trial-event measurability and law API for the returned bounds. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- The full-field bounds (15) are precisely a trial event with twice the
oscillation parameter. -/
theorem amplify_backEvent_iff_trial
    (D Dt : DistRd d → ContMetric d) (ξ Q cs c1 ℓ δ s : ℝ)
    (w : Rd d) (H : DistRd d) :
    AmplifyBackEvent (D H) (Dt H) ξ Q cs c1 ℓ δ s w H ↔
      H ∈ TrialEvent D Dt ξ Q cs c1 ℓ (2 * δ) s w := by
  have e₁ : -ξ * (2 * δ) = -2 * ξ * δ := by ring
  have e₂ : ξ * (2 * δ) = 2 * ξ * δ := by ring
  have e₄ : 2 * ξ * (2 * δ) = 4 * ξ * δ := by ring
  simp only [AmplifyBackEvent, TrialEvent, e₁, e₂, e₄, Set.mem_ofPred_eq]

end HigherDimLQGMetric
