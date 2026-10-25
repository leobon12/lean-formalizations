import SupercriticalLQGUniqueness.B2.DG20Lim.R32LocalizedGoodCostsLocal
import LQGMetric.Meas.LocalEvent

 



set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal
open LQGMetric LQGMetric.LFPP LQGMetric.Blueprint

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem aeEventIn_localized_bad_ratioR32
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (Y : Ω → DistC) (hY : Measurable Y)
    (ξ : ℝ) (ε : Ioi (0 : ℝ))
    (x y r : ℚ) (hr : 0 < r)
    (hεr : Real.sqrt (ε : ℝ) < (r : ℝ) / 4)
    (C : ℝ≥0∞) :
    AEEventIn P (fieldSigma Y (widerCenteredAnnulusR32 x y r))
      {ω | C * finiteCircleCoords
        (lfppContMetric ξ
          (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property (Y ω))
          (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property (Y ω)).continuous)
        (centeredInnerCircleR32 x y r hr, centeredOuterCircleR32 x y r hr) <
        finiteAroundCoords
        (lfppContMetric ξ
          (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property (Y ω))
          (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property (Y ω)).continuous)
        (centeredRatAnnulusR32 x y r hr)} := by
  let U := widerCenteredAnnulusR32 x y r
  let A := centeredRatAnnulusR32 x y r hr
  let D : DistC → ContMetric := fun g => lfppContMetric ξ
    (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property g)
    (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property g).continuous
  let B : Set DistC := {g | C * finiteCircleCoords (D g)
    (A.inner, A.outer) < finiteAroundCoords (D g) A}
  have hD : Measurable D := by
    have hM : Measurable (fun φ : C(ℂ, ℝ) => lfppContMetric ξ φ φ.continuous) := by
      convert (measurable_normalizedContLFPP ξ
        (⟨1, by norm_num⟩ : Ioi (0 : ℝ))) using 1
      funext φ
      exact (normalizedContLFPP_one ξ φ).symm
    exact hM.comp (LQGMetric.DFGPS.L217.measurable_locMollifyC
      (ε : ℝ) ε.property)
  letI : IsProbabilityMeasure (P.map Y) :=
    (Measure.isProbabilityMeasure_map_iff hY.aemeasurable).2 inferInstance
  have hB : NullMeasurableSet B (P.map Y) :=
    nullMeasurableSet_finite_bad_ratio D hD.aemeasurable A C
  let R : DistC → (LQGMetric.CoordJ → ℝ) :=
    fun g => pairJ U (restrictTo U g)
  have hR : Measurable R := (measurable_pairJ U).comp (measurable_restrictTo U)
  have hV : Measurable[fieldSigma Y U] (fun ω => R (Y ω)) :=
    (measurable_pairJ U).comp (Measurable.of_comap_le le_rfl)
  have hVR : ∀ᵐ ω ∂P, R (Y ω) = R (Y ω) :=
    Filter.Eventually.of_forall fun _ => rfl
  have hsat : ∀ g ∈ (Set.univ : Set DistC), ∀ g' ∈ (Set.univ : Set DistC),
      R g = R g' → g ∈ B → g' ∈ B := by
    intro g _ g' _ he hb
    have he' : restrictTo U g = restrictTo U g' :=
      (injective_pairJ U) he
    obtain ⟨ha, hc⟩ := localized_annulus_costs_eq_of_restrictTo_eqR32
      ξ ε x y r hr hεr he'
    have hi : A.inner = centeredInnerCircleR32 x y r hr := rfl
    have ho : A.outer = centeredOuterCircleR32 x y r hr := rfl
    have hb' : C * setDist (lfppContMetric ξ
        (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property g)
        (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property g).continuous)
        (centeredInnerCircleR32 x y r hr).toSet
        (centeredOuterCircleR32 x y r hr).toSet <
      (lfppContMetric ξ
        (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property g)
        (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property g).continuous).aroundDist
        (centeredRatAnnulusR32 x y r hr).toSet
        (centeredInnerCircleR32 x y r hr).toSet
        (centeredOuterCircleR32 x y r hr).toSet := by
      simpa [B, finiteCircleCoords, finiteAroundCoords, D, A, hi, ho] using hb
    rw [ha, hc] at hb'
    simpa [B, finiteCircleCoords, finiteAroundCoords, D, A, hi, ho] using hb'
  have hloc := LQGMetric.LocalEvent.aeEventIn_of_saturated
    hY hR hV hVR MeasurableSet.univ hB
    (Filter.Eventually.of_forall fun _ => Set.mem_univ _) hsat
  have hi : A.inner = centeredInnerCircleR32 x y r hr := rfl
  have ho : A.outer = centeredOuterCircleR32 x y r hr := rfl
  simpa [B, D, A, U, finiteCircleCoords, finiteAroundCoords, hi, ho] using hloc

end SupercriticalLQGUniqueness.B2.DG20Lim
