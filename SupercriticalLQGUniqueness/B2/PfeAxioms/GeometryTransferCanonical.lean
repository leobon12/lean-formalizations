import SupercriticalLQGUniqueness.B2.PfeAxioms.GeometryTransferSB

 

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology LQGMetric
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem limitLengthSpace0_of_dg20LimitStrongSB_canonicalBorel
    (hStrong : Inputs.DG20LimitStrongSB) : Inputs.LimitLengthSpace0 := by
  letI : MeasurableSpace LSCFun := borel LSCFun
  letI : BorelSpace LSCFun := ⟨rfl⟩
  exact limitLengthSpace0_of_dg20LimitStrongSB hStrong

theorem limitEuclideanControl0_of_dg20LimitStrongSB_canonicalBorel
    (hStrong : Inputs.DG20LimitStrongSB) : Inputs.LimitEuclideanControl0 := by
  letI : MeasurableSpace LSCFun := borel LSCFun
  letI : BorelSpace LSCFun := ⟨rfl⟩
  exact limitEuclideanControl0_of_dg20LimitStrongSB hStrong

 


theorem ae_euclideanForget_continuous_of_dg20LimitStrongSB
    (hStrong : Inputs.DG20LimitStrongSB)
    (ξ : Set.Ioi (0 : ℝ))
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) (D : DistC → LSCMetric)
    (hm : ∀ δ, IsLFPPNormalizer ξ δ (m δ))
    (hε : Tendsto (fun n => (ε n : ℝ)) atTop (𝓝 0))
    (hD : SubseqLimit ξ m ε D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P) :
    ∀ᵐ ω ∂P, Continuous (B2.Median.Inputs.euclideanForget (D (h ω))) :=
  Inputs.ae_euclideanForget_continuous_of_inputs0_existsExponent
    (limitEuclideanControl0_of_dg20LimitStrongSB_canonicalBorel hStrong)
    ξ m ε D hm hε hD P h hh

end SupercriticalLQGUniqueness.B2.PfeAxioms
