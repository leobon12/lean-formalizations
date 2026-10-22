import HigherDimLQGMetric.DGZ.NondegShape

/-! The unit distance must cross every sufficiently small centered box shell. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set

namespace HigherDimLQGMetric.DGZ

open HigherDimLFPP HigherDimLFPP.Perc
open HigherDimLFPP.DGZ (cbox obox)

variable {d : ℕ}

theorem nd_across_le_lfppDistance (hd0 : 0 < d) {ξ : ℝ} {φ : Rd d → ℝ}
    (hφ : Continuous φ) {r : ℝ} (hr : 0 < r) (hr1 : 2 * r ≤ 1) :
    acrossDist ξ φ 0 (2 * r) r ≤ lfppDistance d ξ φ := by
  have h0 : (0 : Rd d) ∈ cbox 0 r := by
    intro i
    simp [hr.le]
  have he : e₁ d ∉ obox (0 : Rd d) (2 * r) := by
    intro he
    have hh := he ⟨0, hd0⟩
    simp [PiLp.zero_apply, e₁_ofLp] at hh
    linarith
  rw [lfppDistance_eq_lfppDistOn]
  exact acrossDist_le_lfppDistOn hφ (by linarith) h0 he (pcwJoined_cube d)

end HigherDimLQGMetric.DGZ
