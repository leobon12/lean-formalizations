import SupercriticalLQGUniqueness.B2.DG20Lim.R32LocalizedGoodEventCentered

 



set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal
open LQGMetric LQGMetric.LFPP LQGMetric.Blueprint

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem exists_measurable_localized_good_ratio_centeredR32
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (ξ : ℝ) (ε : Ioi (0 : ℝ))
    (x y r : ℚ) (hr : 0 < r)
    (hεr : Real.sqrt (ε : ℝ) < (r : ℝ) / 4)
    (C : ℝ≥0∞) (R : ℝ) (z : ℂ) :
    ∃ E : Set Ω,
      MeasurableSet[fieldSigma
        (fun ω => addConst (h ω) (-circleAvg (h ω) R z))
        (widerCenteredAnnulusR32 x y r)] E ∧
      E =ᵐ[P] {ω | finiteAroundCoords
        (lfppContMetric ξ
          (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property (h ω))
          (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property (h ω)).continuous)
        (centeredRatAnnulusR32 x y r hr) ≤
        C * finiteCircleCoords
        (lfppContMetric ξ
          (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property (h ω))
          (LQGMetric.DFGPS.L217.locMollifyC (ε : ℝ) ε.property (h ω)).continuous)
        (centeredInnerCircleR32 x y r hr, centeredOuterCircleR32 x y r hr)} := by
  obtain ⟨B, hB, hEq⟩ :=
    aeEventIn_localized_bad_ratio_centeredR32 P h hh ξ ε x y r hr hεr C R z
  refine ⟨Bᶜ, hB.compl, ?_⟩
  filter_upwards [hEq] with ω hω
  simpa only [mem_compl_iff, mem_setOf_eq, not_lt] using (congrArg Not hω).symm

end SupercriticalLQGUniqueness.B2.DG20Lim
