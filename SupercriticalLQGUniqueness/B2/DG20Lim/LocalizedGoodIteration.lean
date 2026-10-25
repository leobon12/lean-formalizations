import SupercriticalLQGUniqueness.B2.DG20Lim.RationalGeoRad64

 

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal
open LQGMetric LQGMetric.LFPP LQGMetric.Blueprint

namespace SupercriticalLQGUniqueness.B2.DG20Lim

def localizedGoodEvent {Ω : Type} (h : Ω → DistC) (ξ : ℝ)
    (ε : Ioi (0 : ℝ)) (x y r : ℚ) (hr : 0 < r) (C : ℝ≥0∞) : Set Ω :=
  {ω | finiteAroundCoords
    (lfppContMetric ξ
      (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property (h ω))
      (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property (h ω)).continuous)
    (centeredRatAnnulus x y r hr) ≤
    C * finiteCircleCoords
    (lfppContMetric ξ
      (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property (h ω))
      (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property (h ω)).continuous)
    (centeredInnerCircle x y r hr, centeredOuterCircle x y r hr)}

theorem aeEventIn_localizedGoodEvent_lm
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (ξ : ℝ) (ε : Ioi (0 : ℝ))
    (x y r : ℚ) (hr : 0 < r)
    (hεr : Real.sqrt (ε : ℝ) < (r : ℝ) / 4)
    (C : ℝ≥0∞) :
    AEEventIn P (fieldSigma
      (fun ω => addConst (h ω)
        (-circleAvg (h ω) (16 * (r : ℝ)) (Complex.mk (x : ℝ) (y : ℝ))))
      (annulus (Complex.mk (x : ℝ) (y : ℝ))
        ((1 / 64 : ℝ) * (16 * (r : ℝ)))
        ((1 / 2 : ℝ) * (16 * (r : ℝ)))))
      (localizedGoodEvent h ξ ε x y r hr C) := by
  rw [← widerCenteredAnnulus_eq_lm_annulus x y r]
  obtain ⟨E, hE, hEq⟩ := exists_measurable_localized_good_ratio_centered
    P h hh ξ ε x y r hr hεr C (16 * (r : ℝ))
    (Complex.mk (x : ℝ) (y : ℝ))
  exact ⟨E, hE, by simpa only [localizedGoodEvent] using hEq.symm⟩

 
theorem localized_good_iteration64 (a : ℝ) (ha : 0 < a) :
    ∃ p c : ℝ, 0 < p ∧ p < 1 ∧ 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
        (ξ : ℝ) (ε : Ioi (0 : ℝ)) (x y r₀ : ℚ) (hr₀ : 0 < r₀)
        (S : Finset ℕ) (hS : S.Nonempty) (C : ℝ≥0∞),
          (∀ i ∈ S, Real.sqrt (ε : ℝ) < (ratRad64 r₀ i : ℝ) / 4) →
          (∀ i ∈ S, ENNReal.ofReal p ≤
            P (localizedGoodEvent h ξ ε x y (ratRad64 r₀ i) (ratRad64_pos hr₀ i) C)) →
          P {ω | ∀ i ∈ S,
            ω ∉ localizedGoodEvent h ξ ε x y (ratRad64 r₀ i)
              (ratRad64_pos hr₀ i) C} ≤
            ENNReal.ofReal (c * Real.exp (-a * S.card)) := by
  obtain ⟨p, c, hp0, hp1, hc0, hLM⟩ := annulus_iteration_finset64 a ha
  refine ⟨p, c, hp0, hp1, hc0, ?_⟩
  intro Ω _ P _ h hh ξ ε x y r₀ hr₀ S hS C hscale hprob
  let E : ℕ → Set Ω := fun i =>
    localizedGoodEvent h ξ ε x y (ratRad64 r₀ i) (ratRad64_pos hr₀ i) C
  have hloc : ∀ i ∈ S, AEEventIn P
      (fieldSigma (fun ω => addConst (h ω)
        (-circleAvg (h ω) (geoRad64 (16 * (r₀ : ℝ)) i)
          (Complex.mk (x : ℝ) (y : ℝ))))
        (annulus (Complex.mk (x : ℝ) (y : ℝ))
          (1 / 64 * geoRad64 (16 * (r₀ : ℝ)) i)
          (1 / 2 * geoRad64 (16 * (r₀ : ℝ)) i))) (E i) := by
    intro i hi
    rw [geoRad64_eq_ratRad64]
    exact aeEventIn_localizedGoodEvent_lm P h hh ξ ε x y
      (ratRad64 r₀ i) (ratRad64_pos hr₀ i) (hscale i hi) C
  have hρ₀ : 0 < 16 * (r₀ : ℝ) :=
    mul_pos (by norm_num) (Rat.cast_pos.mpr hr₀)
  exact hLM P h hh.1 (Complex.mk (x : ℝ) (y : ℝ))
    (16 * (r₀ : ℝ)) hρ₀ S hS E hloc hprob

end SupercriticalLQGUniqueness.B2.DG20Lim
