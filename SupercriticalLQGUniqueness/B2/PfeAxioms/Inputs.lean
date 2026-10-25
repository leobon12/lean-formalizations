import SupercriticalLQGUniqueness.B2.PfeAxioms.RadiusBall
import SupercriticalLQGUniqueness.B2.Iface.Statements

 








set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open LQGMetric (DistC)
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms.Inputs

open SupercriticalLQGUniqueness.B2.Iface

 





def LimitEuclideanControl : Prop :=
  ∀ (ξ : Set.Ioi (0 : ℝ))
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) (D : DistC → LSCMetric),
    SubseqLimit ξ m ε D →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistC),
      IsNormalizedWholePlaneGFF h P →
      ∀ᵐ ω ∂P, ∀ u : ℂ, ∀ δ : ℝ, 0 < δ →
        ∃ η : ℝ, 0 < η ∧
          ∀ v : ℂ, (D (h ω)).1 (u, v) < ENNReal.ofReal η → dist u v < δ

 




def LimitLengthSpace : Prop :=
  ∀ (ξ : Set.Ioi (0 : ℝ))
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) (D : DistC → LSCMetric),
    SubseqLimit ξ m ε D →
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistC),
      IsNormalizedWholePlaneGFF h P →
      ∀ᵐ ω ∂P, (D (h ω)).IsLengthSpace

 

theorem ae_finitePathsEuclideanContinuous_of_inputs
    (hInput : LimitEuclideanControl)
    (ξ : Set.Ioi (0 : ℝ))
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ)) (D : DistC → LSCMetric)
    (hD : SubseqLimit ξ m ε D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P) :
    ∀ᵐ ω ∂P, FinitePathsEuclideanContinuous (D (h ω)) := by
  filter_upwards [hInput ξ m ε D hD P h hh] with ω hω
  exact finitePathsEuclideanContinuous_of_control (D (h ω)) hω

end SupercriticalLQGUniqueness.B2.PfeAxioms.Inputs
