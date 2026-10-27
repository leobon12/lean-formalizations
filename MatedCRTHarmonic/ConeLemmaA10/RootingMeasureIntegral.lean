import MatedCRTHarmonic.GMS4.Prop410Rooting

/-!
# Integration against the normalized rooting measure

This file gives the exact Bochner-integral normalization used to pass from Lebesgue
integration on the open unit disk to the uniform rooting probability measure.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric

namespace MatedCRTHarmonic.ConeLemmaA10

open MatedCRTHarmonic.GMS4.GMSA

/-- Integration against normalized Lebesgue measure on the open unit disk is Lebesgue
integration over that disk multiplied by `π⁻¹`. -/
theorem integral_normalizedLebesgueOnRootingDisk (G : ℂ → ℝ) :
    ∫ z, G z ∂normalizedLebesgueOnRootingDisk =
      Real.pi⁻¹ * ∫ z in ball (0 : ℂ) 1, G z ∂volume := by
  rw [normalizedLebesgueOnRootingDisk, integral_smul_measure]
  simp [rootingDisk, ENNReal.toReal_ofReal (by positivity : 0 ≤ Real.pi⁻¹)]

end MatedCRTHarmonic.ConeLemmaA10

