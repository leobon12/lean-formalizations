import SupercriticalLQGUniqueness.B2.DG20Lim.LocalizedGoodIteration
import SupercriticalLQGUniqueness.B2.DG20Lim.LocalizedGoodProbability

 

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal
open LQGMetric LQGMetric.LFPP LQGMetric.Blueprint

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem measure_localizedGoodEvent_ge_of_bad_le
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (ξ : ℝ) (ε : Ioi (0 : ℝ))
    (x y r : ℚ) (hr : 0 < r) (C : ℝ≥0∞)
    (p η : ℝ) (hp : 0 ≤ p) (hη : 0 ≤ η) (hpe : p + η ≤ 1)
    (hbad : P {ω | C * finiteCircleCoords
        (lfppContMetric ξ
          (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property (h ω))
          (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property (h ω)).continuous)
        (centeredInnerCircle x y r hr, centeredOuterCircle x y r hr) <
        finiteAroundCoords
        (lfppContMetric ξ
          (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property (h ω))
          (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property (h ω)).continuous)
        (centeredRatAnnulus x y r hr)} ≤ ENNReal.ofReal η) :
    ENNReal.ofReal p ≤ P (localizedGoodEvent h ξ ε x y r hr C) := by
  let G := localizedGoodEvent h ξ ε x y r hr C
  have hGc : Gᶜ = {ω | C * finiteCircleCoords
        (lfppContMetric ξ
          (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property (h ω))
          (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property (h ω)).continuous)
        (centeredInnerCircle x y r hr, centeredOuterCircle x y r hr) <
        finiteAroundCoords
        (lfppContMetric ξ
          (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property (h ω))
          (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property (h ω)).continuous)
        (centeredRatAnnulus x y r hr)} := by
    ext ω
    simp only [G, localizedGoodEvent, mem_compl_iff, mem_setOf_eq, not_le]
  have hGn : NullMeasurableSet Gᶜ P := by
    rw [hGc]
    exact nullMeasurableSet_finite_bad_ratio (fun ω => lfppContMetric ξ
      (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property (h ω))
      (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property (h ω)).continuous)
      (measurable_local_lfpp_metric hh ξ ε).aemeasurable
      (centeredRatAnnulus x y r hr) C
  have hmass : P Gᶜ + P G = 1 := by
    simpa only [compl_compl, measure_univ] using (measure_add_measure_compl₀ hGn)
  have hpsum : ENNReal.ofReal p + ENNReal.ofReal η ≤ 1 := by
    rw [← ENNReal.ofReal_add hp hη]
    exact ENNReal.ofReal_le_one.2 hpe
  have hbad' : P Gᶜ ≤ ENNReal.ofReal η := by simpa only [hGc] using hbad
  have hle : P Gᶜ + ENNReal.ofReal p ≤ P Gᶜ + P G := by
    calc
      P Gᶜ + ENNReal.ofReal p = ENNReal.ofReal p + P Gᶜ := add_comm ..
      _ ≤ ENNReal.ofReal p + ENNReal.ofReal η := add_le_add_right hbad' _
      _ ≤ 1 := hpsum
      _ = P Gᶜ + P G := hmass.symm
  exact ENNReal.le_of_add_le_add_left (measure_ne_top P Gᶜ) hle

end SupercriticalLQGUniqueness.B2.DG20Lim
