import InteractingSLE.Spec.Sec7.SideHeightGeom

/-!
# Theorem 2.4: the a.s. initial driving point

The deterministic initial-value theorem is already landed in `SideHeightGeom`.
This file only specializes it to an a.s. generating family.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec2.T24Bridge

/-- A.s. generating curves from zero force the a.s. initial condition on their drivers. -/
theorem ae_driver_zero {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {W : ℝ≥0 → Ω → ℝ} {η : ℝ≥0 → Ω → ℂ}
    (hgen : ∀ᵐ ω ∂P, Continuous (W · ω) ∧ IsGeneratingTrace (W · ω) ⊤ (η · ω)) :
    ∀ᵐ ω ∂P, W 0 ω = 0 :=
  hgen.mono fun _ h => Sec7.SideHeight.w_zero_of_isGeneratingTrace h.2 ENNReal.zero_lt_top

end InteractingSLE.Sec2.T24Bridge
