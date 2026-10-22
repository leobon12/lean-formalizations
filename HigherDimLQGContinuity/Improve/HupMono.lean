import HigherDimLQGContinuity.Core.Interfaces

/-!
# Monotonicity of the upper witness threshold
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

open HigherDimLQGMetric

/-- A stricter upper-witness threshold gives a smaller event. -/
theorem q11_hup_antitone {d : ℕ}
    {D E : DistRd d → ContMetric d} {b b' : ℝ}
    (hbb' : b ≤ b') : Hup D E b' ⊆ Hup D E b := by
  intro H hH
  obtain ⟨γ, hγ, hgap⟩ := hH
  refine ⟨γ, hγ, ?_⟩
  have hmul : ENNReal.ofReal b * (rho D H).internal (annA d) (γ 0) (γ 1) ≤
      ENNReal.ofReal b' * (rho D H).internal (annA d) (γ 0) (γ 1) := by
    gcongr
  exact lt_of_le_of_lt hmul hgap

end HigherDimLQGContinuity
