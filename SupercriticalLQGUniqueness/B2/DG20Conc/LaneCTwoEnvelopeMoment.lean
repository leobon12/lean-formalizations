import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCConcaveMoment

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

theorem laneC_lintegral_two_rpow_mul_le
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {A B : Ω → ℝ≥0∞}
    (hA : Measurable A) (hB : Measurable B)
    {t : ℝ} (ht : 0 < t) (ht2 : 2 * t < 1) :
    (∫⁻ ω, A ω ^ t * B ω ^ t ∂P) ≤
      (∫⁻ ω, A ω ∂P) ^ t * (∫⁻ ω, B ω ∂P) ^ t := by
  have ht1 : t < 1 := by linarith
  let u : ℝ := t / (1 - t)
  have hu : 0 < u := div_pos ht (by linarith)
  have hu1 : u < 1 := (div_lt_one (by linarith)).2 (by linarith)
  have hconj : (1 / t).HolderConjugate (1 / (1 - t)) := by
    apply Real.holderConjugate_iff.mpr
    constructor
    · exact (one_lt_div ht).2 ht1
    · have htn : t ≠ 0 := ht.ne'
      have h1tn : 1 - t ≠ 0 := by linarith
      field_simp
      ring
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq P hconj
    (f := fun ω => A ω ^ t) (g := fun ω => B ω ^ t)
    (hA.pow_const t).aemeasurable (hB.pow_const t).aemeasurable
  have hJ := laneC_lintegral_rpow_le_rpow_lintegral P hB hu hu1
  have hAeq (ω : Ω) : (A ω ^ t) ^ (1 / t) = A ω := by
    rw [← ENNReal.rpow_mul, mul_one_div_cancel ht.ne', ENNReal.rpow_one]
  have hBeq (ω : Ω) : (B ω ^ t) ^ (1 / (1 - t)) = B ω ^ u := by
    rw [← ENNReal.rpow_mul]
    congr 1
    dsimp [u]
    ring
  have hpow : 1 / (1 / t) = t := by field_simp
  have hpow' : 1 / (1 / (1 - t)) = 1 - t := by
    have : 1 - t ≠ 0 := by linarith
    field_simp
  have hH' : (∫⁻ ω, A ω ^ t * B ω ^ t ∂P) ≤
      (∫⁻ ω, A ω ∂P) ^ t *
        (∫⁻ ω, B ω ^ u ∂P) ^ (1 - t) := by
    simpa only [Pi.mul_apply, hAeq, hBeq, hpow, hpow'] using hH
  calc
    _ ≤ (∫⁻ ω, A ω ∂P) ^ t *
        (∫⁻ ω, B ω ^ u ∂P) ^ (1 - t) := hH'
    _ ≤ (∫⁻ ω, A ω ∂P) ^ t *
        ((∫⁻ ω, B ω ∂P) ^ u) ^ (1 - t) :=
      mul_le_mul_of_nonneg_left
        (ENNReal.rpow_le_rpow hJ (by linarith)) bot_le
    _ = _ := by
      rw [← ENNReal.rpow_mul]
      have heq : u * (1 - t) = t := by
        dsimp [u]
        have hne : 1 - t ≠ 0 := by linarith
        exact div_mul_cancel₀ t hne
      rw [heq]

 

theorem laneC_conditional_two_envelope_moment
    {Ω : Type*} {m : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (hm : m ≤ mΩ)
    {U V : Ω → ℝ≥0∞} (hU : Measurable U) (hV : Measurable V)
    {t : ℝ} (ht : 0 < t) (ht2 : 2 * t < 1) :
    (∫⁻ ω,
      (∫⁻ x, U x ∂(condExpKernel P m ω)) ^ t *
        (∫⁻ x, V x ∂(condExpKernel P m ω)) ^ t ∂P) ≤
      (∫⁻ x, U x ∂P) ^ t * (∫⁻ x, V x ∂P) ^ t := by
  have hUm : Measurable (fun ω => ∫⁻ x, U x ∂(condExpKernel P m ω)) :=
    (hU.lintegral_kernel).mono hm le_rfl
  have hVm : Measurable (fun ω => ∫⁻ x, V x ∂(condExpKernel P m ω)) :=
    (hV.lintegral_kernel).mono hm le_rfl
  simpa only [laneC_conditional_lintegral_mean P hm hU,
    laneC_conditional_lintegral_mean P hm hV] using
    laneC_lintegral_two_rpow_mul_le P hUm hVm ht ht2

end SupercriticalLQGUniqueness.B2.DG20Conc
