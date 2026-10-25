import Mathlib.MeasureTheory.Integral.MeanInequalities




 


set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate

theorem lintegral_mul_rpow_le_holder
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f g : Ω → ENNReal) (hf : AEMeasurable f μ) (hg : AEMeasurable g μ)
    (p q : ℝ) (hp : 0 < p) (hq : 1 < q) :
    (∫⁻ ω, (f ω * g ω) ^ p ∂μ) ≤
      (∫⁻ ω, (f ω ^ p) ^ (q / (q - 1)) ∂μ) ^ (1 / (q / (q - 1))) *
        (∫⁻ ω, (g ω ^ p) ^ q ∂μ) ^ (1 / q) := by
  have hc : (q / (q - 1)).HolderConjugate q :=
    (Real.HolderConjugate.conjExponent hq).symm
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hc
    (hf.pow_const p) (hg.pow_const p)
  simpa only [Pi.mul_apply, ENNReal.mul_rpow_of_nonneg _ _ hp.le] using h


end SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate
