import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.OneScale.Smoothing




set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.OneScale

open LQGMetric (DistC addConst circleAvg)

private theorem ennreal_mul_le_mul_iff (k x y : ℝ≥0∞)
    (hk0 : k ≠ 0) (hkTop : k ≠ ∞) :
    k * x ≤ k * y ↔ x ≤ y := by
  constructor
  · intro h
    have hh : (k⁻¹ * k) * x ≤ (k⁻¹ * k) * y := by
      calc
        (k⁻¹ * k) * x = (k * x) * k⁻¹ := by ac_rfl
        _ ≤ (k * y) * k⁻¹ := mul_le_mul_left h _
        _ = (k⁻¹ * k) * y := by ac_rfl
    simpa only [ENNReal.inv_mul_cancel hk0 hkTop, one_mul] using hh
  · intro h
    simpa only [mul_comm k] using (mul_le_mul_left h k)

private theorem threshold_shift (ξ Q A t u : ℝ) (r : Ioi (0 : ℝ)) :
    ENNReal.ofReal (A * (r : ℝ) ^ (ξ * Q) * Real.exp (ξ * (u + t))) =
      ENNReal.ofReal (Real.exp (ξ * t)) *
        ENNReal.ofReal (A * (r : ℝ) ^ (ξ * Q) * Real.exp (ξ * u)) := by
  have hpos : 0 ≤ Real.exp (ξ * t) := (Real.exp_pos _).le
  rw [← ENNReal.ofReal_mul hpos]
  congr 1
  rw [mul_add, Real.exp_add]
  ring

 
theorem pairedRawEvent_shift_ae {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : LQGMetric.IsWholePlaneGFF h P)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ)
    (D D' : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D')
    (z : ℂ) (r : Ioi (0 : ℝ)) (A : ℝ) (c : Ω → ℝ) :
    ∀ᵐ ω ∂P,
      (addConst (h ω) (c ω) ∈ pairedRawEvent ξ Q D D' z r A ↔
       h ω ∈ pairedRawEvent ξ Q D D' z r A) := by
  have hplus : LQGMetric.IsGFFPlusCont h P :=
    LQGMetric.GM.Tight.isGFFPlusCont_of_wp hh
  filter_upwards [Positivity.Witnesses.ae_annulus_addConst_eq_mul P h hplus ξ Q D hD c,
    Positivity.Witnesses.ae_annulus_addConst_eq_mul P h hplus ξ Q D' hD' c,
    LQGMetric.CircleAvg.ae_circleAvg_addConst hh z r.2] with ω hw hw' hca
  let k : ℝ≥0∞ := ENNReal.ofReal (Real.exp ((ξ : ℝ) * c ω))
  have hk0 : k ≠ 0 := (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'
  have hkTop : k ≠ ∞ := ENNReal.ofReal_ne_top
  have hca' : circleAvg (addConst (h ω) (c ω)) r z =
      circleAvg (h ω) r z + c ω := hca (c ω)
  have hlo := threshold_shift (ξ : ℝ) Q A⁻¹ (c ω) (circleAvg (h ω) r z) r
  have hhi := threshold_shift (ξ : ℝ) Q A (c ω) (circleAvg (h ω) r z) r
  simp only [pairedRawEvent, Set.mem_setOf_eq]
  rw [hca', hlo, hhi, (hw (crossingAt z r)).1,
    (hw' (separatorAt z r)).2]
  exact and_congr (ennreal_mul_le_mul_iff k _ _ hk0 hkTop)
    (ennreal_mul_le_mul_iff k _ _ hk0 hkTop)


end SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.OneScale
