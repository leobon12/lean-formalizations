import SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate.LayercakeBridge
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals




 


set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate

def tailDom (p q R₀ C t : ℝ) : ℝ :=
  if t ≤ R₀ then t ^ (p - 1) else C * t ^ (p - q - 1)

private theorem tailDom_integrableOn
    {p q R₀ C : ℝ} (hp : 0 < p) (hpq : p < q) (hR₀ : 0 < R₀) :
    IntegrableOn (tailDom p q R₀ C) (Ioi (0 : ℝ)) := by
  rw [← Ioc_union_Ioi_eq_Ioi hR₀.le, integrableOn_union]
  constructor
  · apply (integrableOn_Ioc_iff_integrableOn_Ioo).2
    have hlo : IntegrableOn (fun t : ℝ => t ^ (p - 1)) (Ioo 0 R₀) :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff hR₀).2 (by linarith)
    apply hlo.congr_fun _ measurableSet_Ioo
    intro t ht
    simp [tailDom, ht.2.le]
  · have hhi : IntegrableOn (fun t : ℝ => C * t ^ (p - q - 1)) (Ioi R₀) :=
      (integrableOn_Ioi_rpow_of_lt (by linarith) hR₀).const_mul C
    apply hhi.congr_fun _ measurableSet_Ioi
    intro t ht
    change R₀ < t at ht
    simp [tailDom, not_le.mpr ht]

theorem tailDom_lintegral_ne_top
    {p q R₀ C : ℝ} (hp : 0 < p) (hpq : p < q) (hR₀ : 0 < R₀)
    (hC : 0 ≤ C) :
    (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (tailDom p q R₀ C t)) ≠ ∞ := by
  have hmeas : Measurable (tailDom p q R₀ C) := by
    unfold tailDom
    exact Measurable.ite measurableSet_Iic (by fun_prop) (by fun_prop)
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] tailDom p q R₀ C := by
    filter_upwards [self_mem_ae_restrict
      (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))] with t ht
    have ht0 : 0 ≤ t := ht.le
    by_cases htR : t ≤ R₀
    · simp [tailDom, htR, Real.rpow_nonneg ht0]
    · simp [tailDom, htR, mul_nonneg hC (Real.rpow_nonneg ht0 _)]
  exact (lintegral_ofReal_ne_top_iff_integrable
    hmeas.aestronglyMeasurable hnonneg).2 (tailDom_integrableOn hp hpq hR₀)

theorem tail_lintegral_le_dominating
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → ℝ≥0∞)
    {p q R₀ C : ℝ} (hC : 0 < C)
    (htail : ∀ R : ℝ, R₀ ≤ R →
      μ {ω | ENNReal.ofReal R < X ω} ≤ ENNReal.ofReal (C * R ^ (-q))) :
    (∫⁻ t in Ioi (0 : ℝ),
      μ {ω | ENNReal.ofReal t < X ω} * ENNReal.ofReal (t ^ (p - 1))) ≤
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (tailDom p q R₀ C t) := by
  apply lintegral_mono_ae
  filter_upwards [self_mem_ae_restrict (measurableSet_Ioi : MeasurableSet (Ioi (0 : ℝ)))]
    with t ht
  have ht0 : 0 < t := ht
  by_cases htR : t ≤ R₀
  · have hμ : μ {ω | ENNReal.ofReal t < X ω} ≤ 1 := by
      simpa only [measure_univ] using measure_mono (μ := μ) (show {ω : Ω | ENNReal.ofReal t < X ω} ⊆ Set.univ from Set.subset_univ _)
    calc
      μ {ω | ENNReal.ofReal t < X ω} * ENNReal.ofReal (t ^ (p - 1))
          ≤ 1 * ENNReal.ofReal (t ^ (p - 1)) := mul_le_mul' hμ le_rfl
      _ = ENNReal.ofReal (tailDom p q R₀ C t) := by simp [tailDom, htR]
  · have htR' : R₀ ≤ t := le_of_lt (lt_of_not_ge htR)
    calc
      μ {ω | ENNReal.ofReal t < X ω} * ENNReal.ofReal (t ^ (p - 1))
          ≤ ENNReal.ofReal (C * t ^ (-q)) * ENNReal.ofReal (t ^ (p - 1)) :=
            mul_le_mul' (htail t htR') le_rfl
      _ = ENNReal.ofReal (tailDom p q R₀ C t) := by
        rw [← ENNReal.ofReal_mul (mul_nonneg hC.le (Real.rpow_nonneg ht0.le _))]
        congr 1
        have hexp : -q + (p - 1) = p - q - 1 := by ring
        simp [tailDom, htR]
        rw [mul_assoc, ← Real.rpow_add ht0, hexp]

theorem lintegral_rpow_le_of_power_tail
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → ℝ≥0∞)
    (hX : AEMeasurable X μ) (hfin : ∀ᵐ ω ∂μ, X ω < ∞)
    {p q R₀ C : ℝ} (hp : 0 < p) (hC : 0 < C)
    (htail : ∀ R : ℝ, R₀ ≤ R →
      μ {ω | ENNReal.ofReal R < X ω} ≤ ENNReal.ofReal (C * R ^ (-q))) :
    (∫⁻ ω, X ω ^ p ∂μ) ≤
      ENNReal.ofReal p *
        (∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (tailDom p q R₀ C t)) := by
  rw [lintegral_rpow_eq_tail_lintegral μ X hX hfin p hp]
  exact mul_le_mul' le_rfl
    (tail_lintegral_le_dominating μ X hC htail)

theorem lintegral_rpow_lt_top_of_power_tail
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (X : Ω → ℝ≥0∞)
    (hX : AEMeasurable X μ) (hfin : ∀ᵐ ω ∂μ, X ω < ∞)
    {p q R₀ C : ℝ} (hp : 0 < p) (hpq : p < q)
    (hR₀ : 1 ≤ R₀) (hC : 0 < C)
    (htail : ∀ R : ℝ, R₀ ≤ R →
      μ {ω | ENNReal.ofReal R < X ω} ≤ ENNReal.ofReal (C * R ^ (-q))) :
    (∫⁻ ω, X ω ^ p ∂μ) < ∞ := by
  apply lt_of_le_of_lt
    (lintegral_rpow_le_of_power_tail μ X hX hfin hp hC htail)
  exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    (tailDom_lintegral_ne_top hp hpq (lt_of_lt_of_le zero_lt_one hR₀) hC.le).lt_top


end SupercriticalLQGUniqueness.Uniqueness.Objects.BoundaryUnionRate
