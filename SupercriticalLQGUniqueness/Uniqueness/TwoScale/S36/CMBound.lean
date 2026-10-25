import LQGMetric.Field.CameronMartin




 












set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36

open LQGMetric

section GFF

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}

lemma cmDensity_pos (φ : TestC) (ξ : TestC0 → ℝ) : 0 < cmDensity φ ξ := Real.exp_pos _

lemma isProbabilityMeasure_lawPair0 (hh : IsWholePlaneGFF h P) :
    IsProbabilityMeasure (lawPair0 h P) := by
  have := hh.gaussian.isProbabilityMeasure
  exact (Measure.isProbabilityMeasure_map_iff (measurable_pair0_comp hh).aemeasurable).mpr this


 
theorem integral_cmDensity_sq (hh : IsWholePlaneGFF h P) (φ : TestC) :
    Integrable (fun ξ => cmDensity φ ξ ^ 2) (lawPair0 h P) ∧
      ∫ ξ, cmDensity φ ξ ^ 2 ∂(lawPair0 h P) = Real.exp (gradEnergy φ) := by
  have hmeas : ∀ ψ : TestC0, Measurable ((pairProc h) ψ) := fun ψ =>
    (measurable_evalDist ψ.1).comp hh.measurable
  obtain ⟨hi, he⟩ := QuantumZipper.CameronMartin.integral_tiltDensity_sq (gaussian_pairProc hh) hmeas
    (centered_pairProc hh) (Finsupp.single (cmTest0 φ) 1)
  have hp : Measurable fun ω => pair0 (h ω) := measurable_pair0_comp hh
  have hF : Measurable fun ξ => cmDensity φ ξ ^ 2 := (measurable_cmDensity φ).pow_const 2
  simp_rw [tiltDensity_cm hh] at hi he
  rw [covNorm_cm hh] at he
  refine ⟨(integrable_map_measure hF.aestronglyMeasurable hp.aemeasurable).mpr hi, ?_⟩
  rw [lawPair0, integral_map hp.aemeasurable hF.aestronglyMeasurable]
  exact he

 
theorem lawPair0_addFun_le_sqrt (hh : IsWholePlaneGFF h P) (φ : TestC) {A : Set (TestC0 → ℝ)}
    (hA : MeasurableSet A) :
    lawPair0 (fun ω => addFun (h ω) (testCont φ)) P A ≤
      (lawPair0 h P A * ENNReal.ofReal (Real.exp (gradEnergy φ))) ^ (1 / 2 : ℝ) := by
  set μ := lawPair0 h P
  set g : (TestC0 → ℝ) → ℝ≥0∞ := fun ξ => ENNReal.ofReal (cmDensity φ ξ)
  have hg : Measurable g := ENNReal.measurable_ofReal.comp (measurable_cmDensity φ)
  obtain ⟨hi, he⟩ := integral_cmDensity_sq hh φ
  have hg2 : ∫⁻ ξ, g ξ ^ (2 : ℝ) ∂μ = ENNReal.ofReal (Real.exp (gradEnergy φ)) := by
    rw [← he, ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun ξ => sq_nonneg _)]
    refine lintegral_congr fun ξ => ?_
    simp only [g, ENNReal.rpow_two]
    rw [ENNReal.ofReal_pow (cmDensity_pos φ ξ).le]
  have hind : ∫⁻ ξ, (A.indicator (1 : (TestC0 → ℝ) → ℝ≥0∞) ξ) ^ (2 : ℝ) ∂μ = μ A := by
    rw [← lintegral_indicator_one hA]
    refine lintegral_congr fun ξ => ?_
    by_cases hξ : ξ ∈ A <;> simp [hξ]
  have hHolder := ENNReal.lintegral_mul_le_Lp_mul_Lq μ Real.HolderConjugate.two_two
    ((measurable_one.indicator hA).aemeasurable) hg.aemeasurable
  rw [hind, hg2] at hHolder
  rw [lawPair0_addFun_eq_withDensity hh, withDensity_apply _ hA,
    ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  calc ∫⁻ ξ in A, g ξ ∂μ = ∫⁻ ξ, (A.indicator (1 : (TestC0 → ℝ) → ℝ≥0∞) * g) ξ ∂μ := by
        rw [← lintegral_indicator hA]
        refine lintegral_congr fun ξ => ?_
        by_cases hξ : ξ ∈ A <;> simp [hξ]
    _ ≤ _ := hHolder


 
theorem measureReal_lawPair0_addFun_le_sqrt (hh : IsWholePlaneGFF h P) (φ : TestC)
    {A : Set (TestC0 → ℝ)} (hA : MeasurableSet A) :
    (lawPair0 (fun ω => addFun (h ω) (testCont φ)) P).real A ≤
      Real.sqrt ((lawPair0 h P).real A * Real.exp (gradEnergy φ)) := by
  have := isProbabilityMeasure_lawPair0 hh
  have key := lawPair0_addFun_le_sqrt hh φ hA
  have hfin : (lawPair0 h P A * ENNReal.ofReal (Real.exp (gradEnergy φ))) ^ (1 / 2 : ℝ) ≠ ∞ :=
    ENNReal.rpow_ne_top_of_nonneg (by norm_num)
      (ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top)
  have := ENNReal.toReal_mono hfin key
  rw [← ENNReal.toReal_rpow, ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le,
    ← Real.sqrt_eq_rpow] at this
  exact this

end GFF

end SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36
