import SupercriticalLQGUniqueness.B2.DG20Lim.LiftedCoupling
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCLFPPMetricMeas
import SupercriticalLQGUniqueness.B2.PfeAxioms.HeatVersionMeasurable
import SupercriticalLQGUniqueness.B2.LscTop.LFPP

 

set_option autoImplicit false
noncomputable section

open MeasureTheory
open LQGMetric LQGMetric.LFPP
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

 
def normalizedContLFPP (ξ : ℝ) (a : Set.Ioi (0 : ℝ))
    (φ : C(ℂ, ℝ)) : ContMetric :=
  (lfppContMetric ξ φ φ.continuous).smulPos (a : ℝ)⁻¹
    (inv_pos.mpr a.property)

theorem measurable_normalizedContLFPP (ξ : ℝ) (a : Set.Ioi (0 : ℝ)) :
    Measurable (normalizedContLFPP ξ a) := by
  have hLFPP : Measurable (fun φ : C(ℂ, ℝ) => lfppContMetric ξ φ φ.continuous) := by
    exact B2.DG20Conc.laneC_measurable_lfppContMetric
      (fun z (φ : C(ℂ, ℝ)) => φ z)
      (fun φ => φ.continuous)
      (fun z => (continuous_eval_const z).measurable) ξ
  have hScale : Measurable (fun D : ContMetric =>
      D.smulPos (a : ℝ)⁻¹ (inv_pos.mpr a.property)) := by
    apply Measurable.subtype_mk
    exact ((continuous_const_smul (a : ℝ)⁻¹).measurable.comp
      measurable_subtype_coe)
  exact hScale.comp hLFPP

theorem aemeasurable_normalizedContLFPP_heat_version
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (δ a : Set.Ioi (0 : ℝ)) (ξ : ℝ)
    (X : Ω → C(ℂ, ℝ))
    (hX : IsHeatSmoothing P h δ X) :
    AEMeasurable (fun ω => normalizedContLFPP ξ a (X ω)) P :=
  (measurable_normalizedContLFPP ξ a).comp_aemeasurable
    (B2.PfeAxioms.aemeasurable_heat_smoothing_version P h hh δ X hX)

theorem normalizedContLFPP_to_rescaledLFPP
    (ξ : ℝ) (a : Set.Ioi (0 : ℝ)) (φ : C(ℂ, ℝ)) (p : ℂ × ℂ) :
    ((ENNReal.ofReal ((normalizedContLFPP ξ a φ).1 p) : ℝ≥0∞) : EReal) =
      rescaledLFPP ξ a φ p := by
  rw [rescaledLFPP, normalizedContLFPP, ContMetric.smulPos_apply,
    lfppContMetric_apply, B2.LscTop.lfppDistance_eq_lfppD]
  rw [ENNReal.ofReal_mul (le_of_lt (inv_pos.mpr a.property))]
  rw [ENNReal.ofReal_toReal (LQGMetric.LFPP.lfppD_ne_top φ.continuous p.1 p.2)]

end SupercriticalLQGUniqueness.B2.DG20Lim
