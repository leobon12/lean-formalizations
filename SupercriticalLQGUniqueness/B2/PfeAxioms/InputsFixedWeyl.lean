import SupercriticalLQGUniqueness.B2.PfeAxioms.Inputs

 









set_option autoImplicit false
noncomputable section

open Filter Topology MeasureTheory
open LQGMetric (DistC addFun)

namespace SupercriticalLQGUniqueness.B2.PfeAxioms.Inputs

open SupercriticalLQGUniqueness.B2.Iface

 



def BoundedWeylOnBaseEvent : Prop :=
  ∀ (ξ : Set.Ioi (0 : ℝ))
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) (D : DistC → LSCMetric),
    SubseqLimit ξ m ε D →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistC),
      IsNormalizedWholePlaneGFF h P →
      ∀ᵐ ω ∂P, ∀ f : C(ℂ, ℝ),
        (∃ M : ℝ, ∀ z : ℂ, |f z| ≤ M) →
        weylScale (ξ : ℝ) f (D (h ω)) = (D (addFun (h ω) f)).1

end SupercriticalLQGUniqueness.B2.PfeAxioms.Inputs
