import SupercriticalLQGUniqueness.B2.PfeWeyl.LFPPWeyl
import LQGMetric.Metric.WeylScaling
import LQGMetric.Metric.InternalLimitC

 






set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

theorem edist_lfppLSCMetric_eq_cont
    (ξ : ℝ) (φ : C(ℂ, ℝ)) (x y : ℂ) :
    edist ((lfppLSCMetric ξ φ).pt x) ((lfppLSCMetric ξ φ).pt y) =
      edist ((LQGMetric.LFPP.lfppContMetric ξ φ φ.continuous).pt x)
        ((LQGMetric.LFPP.lfppContMetric ξ φ φ.continuous).pt y) := by
  rw [LQGMetric.ContMetric.edist_pt]
  change lfppLSCMetric ξ φ (x, y) =
    ENNReal.ofReal ((LQGMetric.LFPP.lfppContMetric ξ φ φ.continuous).1 (x, y))
  rw [lfppLSCMetric_apply, B2.LscTop.lfppDistance_eq_lfppD,
    LQGMetric.LFPP.lfppContMetric_apply]
  exact (ENNReal.ofReal_toReal
    (LQGMetric.LFPP.lfppD_ne_top φ.continuous x y)).symm

private theorem unitSpeed_lfppLSCMetric_iff
    (ξ : ℝ) (φ : C(ℂ, ℝ)) (P : ℝ → ℂ) (L : ℝ) :
    HasUnitSpeedOn ((lfppLSCMetric ξ φ).pt ∘ P) (Icc 0 L) ↔
      HasUnitSpeedOn
        ((LQGMetric.LFPP.lfppContMetric ξ φ φ.continuous).pt ∘ P) (Icc 0 L) := by
  constructor
  · intro hu x hx y hy
    exact (LQGMetric.MetricGeometry.eVariationOn_eq_mul_of_edist
      (F := (LQGMetric.LFPP.lfppContMetric ξ φ φ.continuous).pt ∘ P)
      (G := (lfppLSCMetric ξ φ).pt ∘ P) (c := 1)
      (fun s t => by
        rw [one_mul]
        exact (edist_lfppLSCMetric_eq_cont ξ φ (P s) (P t)).symm)
      _).trans (by rw [one_mul]; exact hu hx hy)
  · intro hu x hx y hy
    exact (LQGMetric.MetricGeometry.eVariationOn_eq_mul_of_edist
      (F := (lfppLSCMetric ξ φ).pt ∘ P)
      (G := (LQGMetric.LFPP.lfppContMetric ξ φ φ.continuous).pt ∘ P) (c := 1)
      (fun s t => by
        rw [one_mul]
        exact edist_lfppLSCMetric_eq_cont ξ φ (P s) (P t))
      _).trans (by rw [one_mul]; exact hu hx hy)

 

theorem weylScale_lfppLSCMetric_eq_cont
    (ξ : ℝ) (φ ψ : C(ℂ, ℝ)) (z w : ℂ) :
    weylScale ξ ψ (lfppLSCMetric ξ φ) (z, w) =
      LQGMetric.weylScale ξ ψ
        (LQGMetric.LFPP.lfppContMetric ξ φ φ.continuous) z w := by
  apply le_antisymm
  · unfold LQGMetric.weylScale
    refine le_iInf fun L => le_iInf fun P => le_iInf fun hL =>
      le_iInf fun _ => le_iInf fun hu => le_iInf fun h0 => le_iInf fun h1 => ?_
    have hu' := (unitSpeed_lfppLSCMetric_iff ξ φ P L).2 hu
    exact iInf_le_of_le P <| iInf_le_of_le L <|
      iInf_le_of_le (show (lfppLSCMetric ξ φ).IsCurve P 0 L from
        ⟨hL, LQGMetric.MetricGeometry.continuousOn_of_hasUnitSpeedOn hu'⟩) <|
      iInf_le_of_le hu' <| iInf_le_of_le h0 <| iInf_le_of_le h1 le_rfl
  · unfold weylScale
    refine le_iInf fun P => le_iInf fun L => le_iInf fun hP =>
      le_iInf fun hu => le_iInf fun h0 => le_iInf fun h1 => ?_
    have hu' := (unitSpeed_lfppLSCMetric_iff ξ φ P L).1 hu
    exact iInf_le_of_le L <| iInf_le_of_le P <|
      iInf_le_of_le hP.1 <|
      iInf_le_of_le (LQGMetric.MetricGeometry.continuousOn_of_hasUnitSpeedOn hu') <|
      iInf_le_of_le hu' <| iInf_le_of_le h0 <| iInf_le_of_le h1 le_rfl

 

theorem lfppDistance_add_eq_lscWeylScale
    (ξ : ℝ) (φ ψ : C(ℂ, ℝ)) (p : ℂ × ℂ) :
    lfppDistance ξ (φ + ψ) p =
      weylScale ξ ψ (lfppLSCMetric ξ φ) p := by
  rw [lfppDistance_add_eq_weylScale,
    weylScale_lfppLSCMetric_eq_cont]

end SupercriticalLQGUniqueness.B2.PfeWeyl
