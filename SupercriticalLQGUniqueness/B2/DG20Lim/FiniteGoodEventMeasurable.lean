import SupercriticalLQGUniqueness.B2.DG20Lim.FullHeatGoodSequence
import SupercriticalLQGUniqueness.B2.DG20Lim.LocalizedGoodSequenceTransfer

 

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal
open LQGMetric LQGMetric.LFPP LQGMetric.Blueprint

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem nullMeasurableSet_finite_bad_ratio
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] (D : Ω → ContMetric) (hD : AEMeasurable D P)
    (A : RatAnnulus) (C : ℝ≥0∞) :
    NullMeasurableSet {ω | C * setDist (D ω)
      A.inner.toSet A.outer.toSet <
      (D ω).aroundDist A.toSet A.inner.toSet A.outer.toSet} P := by
  have hR := aemeasurable_finiteRatCoords D hD
  have hAcross : AEMeasurable
      (fun ω => finiteCircleCoords (D ω) (A.inner, A.outer)) P := by
    exact ((measurable_pi_apply (A.inner, A.outer)).comp measurable_fst).comp_aemeasurable hR
  have hAround : AEMeasurable (fun ω => finiteAroundCoords (D ω) A) P := by
    exact ((measurable_pi_apply A).comp measurable_snd).comp_aemeasurable hR
  exact nullMeasurableSet_lt (aemeasurable_const.mul hAcross) hAround

theorem aemeasurable_full_heat_lfpp_metric
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (ξ : ℝ) (e : Ioi (0 : ℝ)) (X : Ω → C(ℂ, ℝ))
    (hX : IsHeatSmoothing P h e X) :
    AEMeasurable (fun ω => lfppContMetric ξ (X ω) (X ω).continuous) P := by
  have hN := aemeasurable_normalizedContLFPP_heat_version
    P h hh e (⟨1, by norm_num⟩ : Ioi (0 : ℝ)) ξ X hX
  simpa only [normalizedContLFPP_one] using hN

end SupercriticalLQGUniqueness.B2.DG20Lim
