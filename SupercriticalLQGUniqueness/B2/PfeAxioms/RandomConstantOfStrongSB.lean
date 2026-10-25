import SupercriticalLQGUniqueness.B2.PfeAxioms.RandomBoundedWeyl
import SupercriticalLQGUniqueness.B2.PfeAxioms.GeometryTransferSB

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology LQGMetric
open scoped ENNReal
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 


theorem ae_addConst_eq_scale_of_dg20LimitStrongSB
    [MeasurableSpace LSCFun] [BorelSpace LSCFun]
    (hStrong : Inputs.DG20LimitStrongSB)
    (hW3 : Inputs.BoundedWeylOnBaseEvent)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    (ε : ℕ → Set.Ioi (0 : ℝ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (D : DistC → LSCMetric) (hD : SubseqLimit ξ m ε D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (c : Ω → ℝ) :
    ∀ᵐ ω ∂P, ∀ p : ℂ × ℂ,
      D (addConst (h ω) (c ω)) p =
        ENNReal.ofReal (Real.exp ((ξ : ℝ) * c ω)) * D (h ω) p := by
  have hLen := limitLengthSpace0_of_dg20LimitStrongSB hStrong
    ξ Q hQ m ε D hm hε hD P h hh
  exact ae_addConst_eq_scale_of_w3 hW3 ξ m ε D hD P h hh hLen c

end SupercriticalLQGUniqueness.B2.PfeAxioms
