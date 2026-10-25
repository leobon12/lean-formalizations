import SupercriticalLQGUniqueness.B2.PfeAxioms.Section4FixedAnnulusTight

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal
open LQGMetric LQGMetric.CircleAvg
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem aemeasurable_annularV_costs_of_subseqLimit
    (ξ : Ioi (0 : ℝ))
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (ε : ℕ → Ioi (0 : ℝ))
    (D : DistC → LSCMetric) (hD : SubseqLimit ξ m ε D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ δ, IsHeatSmoothing P h δ (X δ))
    (c : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (a : Ioi (0 : ℝ) → Ω → ℝ)
    (ha : ∀ r, ∀ᵐ ω ∂P, IsCircleAverage (h ω) r 0 (a r ω))
    (A : EuclideanAnnulus) (r : Ioi (0 : ℝ)) :
    AEMeasurable (fun ω =>
      ENNReal.ofReal ((c r : ℝ)⁻¹ * Real.exp (-(ξ : ℝ) * a r ω)) *
        acrossDist (D (h ω)) (A.dilate r r.property)) P ∧
    AEMeasurable (fun ω =>
      ENNReal.ofReal ((c r : ℝ)⁻¹ * Real.exp (-(ξ : ℝ) * a r ω)) *
        aroundDist (D (h ω)) (A.dilate r r.property)) P := by
  have hDm := aemeasurable_limit_metric_normalized ξ m ε D hD P h hh X hX
  have hfac : Measurable (fun ω =>
      ENNReal.ofReal ((c r : ℝ)⁻¹ *
        Real.exp (-(ξ : ℝ) * circleAvg (h ω) r 0))) :=
    ENNReal.measurable_ofReal.comp (measurable_const.mul
      (Real.measurable_exp.comp
        (((LQGMetric.measurable_circleAvg_left r 0).comp hh.1.measurable).const_mul
          (-(ξ : ℝ)))))
  have hAv : ∀ᵐ ω ∂P, a r ω = circleAvg (h ω) r 0 :=
    (ha r).mono fun ω hω => (circleAvg_eq_of_tendsto hω).symm
  constructor
  · have hcost : AEMeasurable
        (fun ω => acrossDist (D (h ω)) (A.dilate r r.property)) P :=
      (measurable_acrossDist _).comp_aemeasurable hDm
    apply (hfac.aemeasurable.mul hcost).congr
    filter_upwards [hAv] with ω hω
    simp [Pi.mul_apply, hω]
  · have hcost : AEMeasurable
        (fun ω => aroundDist (D (h ω)) (A.dilate r r.property)) P :=
      (Uniqueness.TwoScale.S36.measurable_aroundDist_fixed _).comp_aemeasurable hDm
    apply (hfac.aemeasurable.mul hcost).congr
    filter_upwards [hAv] with ω hω
    simp [Pi.mul_apply, hω]

end SupercriticalLQGUniqueness.B2.PfeAxioms
