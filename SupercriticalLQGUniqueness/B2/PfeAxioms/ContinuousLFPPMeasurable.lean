import SupercriticalLQGUniqueness.B2.PfeAxioms.HeatVersionMeasurable
import SupercriticalLQGUniqueness.B2.LscTop.LFPP

 

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 
theorem measurable_rescaledLFPPMap (ξ : ℝ) (a : Set.Ioi (0 : ℝ)) :
    Measurable (B2.LscTop.rescaledLFPPMap ξ a) := by
  apply ContinuousMap.measurable_iff_eval.mpr
  intro q
  exact continuous_coe_ennreal_ereal.measurable.comp
    ((B2.LscTop.measurable_lfppDistance_comp
      (X := id) (fun z => (continuous_eval_const z).measurable) ξ q).const_mul _)

 

theorem aemeasurable_rescaledLFPPMap_heat_version
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (δ : Set.Ioi (0 : ℝ)) (a : Set.Ioi (0 : ℝ)) (ξ : ℝ)
    (X : Ω → C(ℂ, ℝ))
    (hX : IsHeatSmoothing P h δ X) :
    AEMeasurable (fun ω => B2.LscTop.rescaledLFPPMap ξ a (X ω)) P :=
  (measurable_rescaledLFPPMap ξ a).comp_aemeasurable
    (aemeasurable_heat_smoothing_version P h hh δ X hX)

end SupercriticalLQGUniqueness.B2.PfeAxioms
