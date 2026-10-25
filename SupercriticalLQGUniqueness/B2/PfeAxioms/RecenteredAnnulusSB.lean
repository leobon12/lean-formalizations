import SupercriticalLQGUniqueness.B2.PfeAxioms.RecenteredFiniteScale

 


set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal
open LQGMetric
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 


theorem ae_smallAnnulusCosts_recentered_of_dg20LimitStrongSB
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
    (X Y : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ δ, IsHeatSmoothing P h δ (X δ))
    (r : ℝ) (z : ℂ)
    (hY : ∀ δ, IsHeatSmoothing P
      (fun ω => addConst (h ω) (-circleAvg (h ω) r z)) δ (Y δ))
    (K V : Set ℂ)
    (hAnn : ∀ᵐ ω ∂P, PfeWeyl.SmallAnnulusCosts
      (fun k => PfeWeyl.normalizedLFPPMetric (ξ : ℝ)
        (m (ε k)) (X (ε k) ω)) (D (h ω)) K V) :
    ∀ᵐ ω ∂P, PfeWeyl.SmallAnnulusCosts
      (fun k => PfeWeyl.normalizedLFPPMetric (ξ : ℝ)
        (m (ε k)) (Y (ε k) ω))
      (D (addConst (h ω) (-circleAvg (h ω) r z))) K V := by
  have hMetric := ae_addConst_eq_scale_of_dg20LimitStrongSB hStrong hW3
    ξ Q hQ m hm ε hε D hD P h hh
    (fun ω => -circleAvg (h ω) r z)
  have hFinite := ae_recentered_finiteLFPP_scale
    (ξ : ℝ) m ε P h hh X Y hX r z hY
  filter_upwards [hAnn, hMetric, hFinite] with ω hA hDω hFω
  apply smallAnnulusCosts_of_positive_scale
    (fun k => PfeWeyl.normalizedLFPPMetric (ξ : ℝ)
      (m (ε k)) (X (ε k) ω))
    (fun k => PfeWeyl.normalizedLFPPMetric (ξ : ℝ)
      (m (ε k)) (Y (ε k) ω))
    (D (h ω)) (D (addConst (h ω) (-circleAvg (h ω) r z)))
    (Real.exp ((ξ : ℝ) * -circleAvg (h ω) r z))
    (Real.exp_pos _) hDω ?_ K V hA
  exact Filter.Eventually.of_forall (fun k p => hFω k p)

end SupercriticalLQGUniqueness.B2.PfeAxioms
