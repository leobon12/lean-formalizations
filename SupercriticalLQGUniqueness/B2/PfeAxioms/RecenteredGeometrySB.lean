import SupercriticalLQGUniqueness.B2.PfeAxioms.GeometryScale
import LQGMetric.Papers.DFGPS.T12P0

 



set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal
open LQGMetric
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem isGFFPlusBddCont_recentered
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {h : Ω → DistC} (hh : IsNormalizedWholePlaneGFF h P)
    (r : ℝ) (z : ℂ) :
    IsGFFPlusBddCont
      (fun ω => addConst (h ω) (-circleAvg (h ω) r z)) P := by
  have hc : Measurable (fun ω => -circleAvg (h ω) r z) :=
    ((LQGMetric.measurable_circleAvg_left r z).comp hh.1.measurable).neg
  exact LQGMetric.DFGPS.isGFFPlusBddCont_of_wp (hh.1.addConst hc)

theorem ae_euclideanControl_recentered_of_dg20LimitStrongSB
    [MeasurableSpace LSCFun] [BorelSpace LSCFun]
    (hStrong : Inputs.DG20LimitStrongSB)
    (hW3 : Inputs.BoundedWeylOnBaseEvent)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    (ε : ℕ → Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (D : DistC → LSCMetric) (hD : SubseqLimit ξ m ε D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (r : ℝ) (z : ℂ) :
    ∀ᵐ ω ∂P,
      ∀ u : ℂ, ∀ δ : ℝ, 0 < δ → ∃ η : ℝ, 0 < η ∧
        ∀ v : ℂ,
          D (addConst (h ω) (-circleAvg (h ω) r z)) (u, v) <
            ENNReal.ofReal η → dist u v < δ := by
  have hBase := limitEuclideanControl0_of_dg20LimitStrongSB hStrong
    ξ Q hQ m ε D hm hε hD P h hh
  have hScale := ae_addConst_eq_scale_of_dg20LimitStrongSB hStrong hW3
    ξ Q hQ m hm ε hε D hD P h hh
    (fun ω => -circleAvg (h ω) r z)
  filter_upwards [hBase, hScale] with ω hBω hSω
  exact euclideanControl_of_positive_scale (D (h ω))
    (D (addConst (h ω) (-circleAvg (h ω) r z)))
    (Real.exp ((ξ : ℝ) * -circleAvg (h ω) r z))
    (Real.exp_pos _) hSω hBω

end SupercriticalLQGUniqueness.B2.PfeAxioms
