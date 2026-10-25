import SupercriticalLQGUniqueness.B2.DG20Lim.R32UnitAnnulusCoords
import SupercriticalLQGUniqueness.B2.DG20Lim.R32UnitGoodAnnulusRatio
import SupercriticalLQGUniqueness.B2.DG20Lim.R32ScaledGoodAnnulusRatio
import SupercriticalLQGUniqueness.B2.DG20Lim.R32TranslatedGoodAnnulusRatio
import SupercriticalLQGUniqueness.B2.DG20Lim.R32UniformGoodAnnulusRatio
import SupercriticalLQGUniqueness.B2.DG20Lim.R32RationalAnnulusAffine
import SupercriticalLQGUniqueness.B2.DG20Lim.R32RationalGoodAnnulusRatio
import SupercriticalLQGUniqueness.B2.DG20Lim.R32LocalizedRatAnnulusLocality
import SupercriticalLQGUniqueness.B2.DG20Lim.R32RationalGoodSequence
import SupercriticalLQGUniqueness.B2.DG20Lim.R32GoodAnnulusCoupledLimit
import SupercriticalLQGUniqueness.B2.DG20Lim.R32LocalizedMollifierSigma
import SupercriticalLQGUniqueness.B2.DG20Lim.R32RationalAnnulusBuffer
import SupercriticalLQGUniqueness.B2.DG20Lim.R32LocalizedGoodCostCompare
import SupercriticalLQGUniqueness.B2.DG20Lim.R32LocalizedGoodHeatCompare
import SupercriticalLQGUniqueness.B2.DG20Lim.R32LocalizedGoodEventualCompare
import SupercriticalLQGUniqueness.B2.DG20Lim.R32LocalizedGoodSequenceTransfer
import SupercriticalLQGUniqueness.B2.DG20Lim.R32FullHeatGoodSequence
import SupercriticalLQGUniqueness.B2.DG20Lim.R32LocalizedGoodProbability
import SupercriticalLQGUniqueness.B2.DG20Lim.R32WiderAnnulusSupport
import SupercriticalLQGUniqueness.B2.DG20Lim.R32LocalizedGoodCostsLocal
import SupercriticalLQGUniqueness.B2.DG20Lim.R32LocalizedGoodEventLocal
import SupercriticalLQGUniqueness.B2.DG20Lim.R32LocalizedGoodEventCentered
import SupercriticalLQGUniqueness.B2.DG20Lim.R32LocalizedGoodRepresentative
import SupercriticalLQGUniqueness.B2.DG20Lim.R32LocalizedLMAnnulus
import SupercriticalLQGUniqueness.B2.DG20Lim.RationalGeoRad64

 



set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal
open LQGMetric LQGMetric.LFPP LQGMetric.Blueprint

namespace SupercriticalLQGUniqueness.B2.DG20Lim

def localizedGoodEventR32 {Ω : Type} (h : Ω → DistC) (ξ : ℝ)
    (ε : Ioi (0 : ℝ)) (x y r : ℚ) (hr : 0 < r) (C : ℝ≥0∞) : Set Ω :=
  {ω | finiteAroundCoords
    (lfppContMetric ξ
      (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property (h ω))
      (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property (h ω)).continuous)
    (centeredRatAnnulusR32 x y r hr) ≤
    C * finiteCircleCoords
    (lfppContMetric ξ
      (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property (h ω))
      (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property (h ω)).continuous)
    (centeredInnerCircleR32 x y r hr, centeredOuterCircleR32 x y r hr)}

theorem aeEventIn_localizedGoodEvent_lmR32
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
      (localizedGoodEventR32 h ξ ε x y r hr C) := by
  rw [← widerCenteredAnnulus_eq_lm_annulusR32 x y r]
  obtain ⟨E, hE, hEq⟩ := exists_measurable_localized_good_ratio_centeredR32
    P h hh ξ ε x y r hr hεr C (16 * (r : ℝ))
    (Complex.mk (x : ℝ) (y : ℝ))
  exact ⟨E, hE, by simpa only [localizedGoodEventR32] using hEq.symm⟩

 
theorem localized_good_iteration64R32 (a : ℝ) (ha : 0 < a) :
    ∃ p c : ℝ, 0 < p ∧ p < 1 ∧ 0 < c ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
        (ξ : ℝ) (ε : Ioi (0 : ℝ)) (x y r₀ : ℚ) (hr₀ : 0 < r₀)
        (S : Finset ℕ) (hS : S.Nonempty) (C : ℝ≥0∞),
          (∀ i ∈ S, Real.sqrt (ε : ℝ) < (ratRad64 r₀ i : ℝ) / 4) →
          (∀ i ∈ S, ENNReal.ofReal p ≤
            P (localizedGoodEventR32 h ξ ε x y (ratRad64 r₀ i) (ratRad64_pos hr₀ i) C)) →
          P {ω | ∀ i ∈ S,
            ω ∉ localizedGoodEventR32 h ξ ε x y (ratRad64 r₀ i)
              (ratRad64_pos hr₀ i) C} ≤
            ENNReal.ofReal (c * Real.exp (-a * S.card)) := by
  obtain ⟨p, c, hp0, hp1, hc0, hLM⟩ := annulus_iteration_finset64 a ha
  refine ⟨p, c, hp0, hp1, hc0, ?_⟩
  intro Ω _ P _ h hh ξ ε x y r₀ hr₀ S hS C hscale hprob
  let E : ℕ → Set Ω := fun i =>
    localizedGoodEventR32 h ξ ε x y (ratRad64 r₀ i) (ratRad64_pos hr₀ i) C
  have hloc : ∀ i ∈ S, AEEventIn P
      (fieldSigma (fun ω => addConst (h ω)
        (-circleAvg (h ω) (geoRad64 (16 * (r₀ : ℝ)) i)
          (Complex.mk (x : ℝ) (y : ℝ))))
        (annulus (Complex.mk (x : ℝ) (y : ℝ))
          (1 / 64 * geoRad64 (16 * (r₀ : ℝ)) i)
          (1 / 2 * geoRad64 (16 * (r₀ : ℝ)) i))) (E i) := by
    intro i hi
    rw [geoRad64_eq_ratRad64]
    exact aeEventIn_localizedGoodEvent_lmR32 P h hh ξ ε x y
      (ratRad64 r₀ i) (ratRad64_pos hr₀ i) (hscale i hi) C
  have hρ₀ : 0 < 16 * (r₀ : ℝ) :=
    mul_pos (by norm_num) (Rat.cast_pos.mpr hr₀)
  exact hLM P h hh.1 (Complex.mk (x : ℝ) (y : ℝ))
    (16 * (r₀ : ℝ)) hρ₀ S hS E hloc hprob

end SupercriticalLQGUniqueness.B2.DG20Lim
