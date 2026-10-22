import HigherDimLQGMetric.LfppTight.CrossBddCont

/-! Packet L6a target A8: crossing at every center and scale. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

theorem l6b_cross (hL1e : L1e_law) :
    ∀ (d : ℕ) (ξ : ℝ) (κ : Rd d → ℝ), L6b_cross d ξ κ := by
  intro d ξ κ hB2
  obtain ⟨Q, hDGZ, hAdapter⟩ := hB2
  intro Ω _ P _ h hh p hp C hC
  exact l6a_cross_bddCont_direct hL1e hDGZ hAdapter P h hh hp hC

end HigherDimLQGMetric
