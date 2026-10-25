import SupercriticalLQGUniqueness.B2.PfeAxioms.InputsFixedWeyl

 

set_option autoImplicit false
noncomputable section

open MeasureTheory LQGMetric
open SupercriticalLQGUniqueness.B2.Iface

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 


theorem ae_weylScale_random_bounded_shift_of_input
    (hW3 : Inputs.BoundedWeylOnBaseEvent)
    (ξ : Set.Ioi (0 : ℝ))
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ))
    (D : DistC → LSCMetric)
    (hD : SubseqLimit ξ m ε D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (f : Ω → C(ℂ, ℝ))
    (hf : ∀ᵐ ω ∂P, ∃ M : ℝ, ∀ z : ℂ, |f ω z| ≤ M) :
    ∀ᵐ ω ∂P,
      weylScale (ξ : ℝ) (f ω) (D (h ω)) =
        (D (addFun (h ω) (f ω))).1 := by
  filter_upwards [hW3 ξ m ε D hD P h hh, hf] with ω hω hfw
  exact hω (f ω) hfw

 

theorem ae_addConst_eq_scale_of_w3
    (hW3 : Inputs.BoundedWeylOnBaseEvent)
    (ξ : Set.Ioi (0 : ℝ))
    (m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (ε : ℕ → Set.Ioi (0 : ℝ))
    (D : DistC → LSCMetric)
    (hD : SubseqLimit ξ m ε D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (hLen : ∀ᵐ ω ∂P, (D (h ω)).IsLengthSpace)
    (c : Ω → ℝ) :
    ∀ᵐ ω ∂P, ∀ p : ℂ × ℂ,
      D (addConst (h ω) (c ω)) p =
        ENNReal.ofReal (Real.exp ((ξ : ℝ) * c ω)) * D (h ω) p := by
  filter_upwards [hW3 ξ m ε D hD P h hh, hLen] with ω hW hL
  intro p
  have hConst := hW (ContinuousMap.const ℂ (c ω)) ⟨|c ω|, by intro z; rfl⟩
  exact (congrFun hConst p).symm.trans
    (weylScale_const (ξ : ℝ) (c ω) (D (h ω)) hL p)

end SupercriticalLQGUniqueness.B2.PfeAxioms
