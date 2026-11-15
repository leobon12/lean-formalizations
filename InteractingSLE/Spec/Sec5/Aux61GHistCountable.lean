/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61UnionKLocal
import InteractingSLE.Spec.Sec5.Aux61CovWire

/-! # Countably many captured future subevents suffice

Each captured subevent may use its own fibre-local cover. Their future
capture conditions need not themselves be measurable for the retained past.
The reflected reference avoidance is still the explicit R5 mathematical input.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter

namespace InteractingSLE.Sec5.Aux61GHist

universe u

/-- Apply reference avoidance to the countably many captured pieces of
an event. This avoids requiring a single history cover whose every piece
captures every sample of the original event. -/
theorem ae_not_of_countable_captured_localCovers
    {X : Type u} [MeasurableSpace X] {μ : Measure X} [IsFiniteMeasure μ]
    {ι : Type*} [Countable ι] {E : X → Prop} (C : ι → X → Prop)
    (hcaptured_cover : ∀ᵐ x ∂μ, E x → ∃ i, C i x)
    (hlocal : ∀ i, Aux61UnionK.HasFibreLocalCover μ (fun x => E x ∧ C i x))
    (hneg : Aux61Cov.R5NegStatement.{u}) : ∀ᵐ x ∂μ, ¬ E x := by
  have hnull : ∀ i, ∀ᵐ x ∂μ, ¬ (E x ∧ C i x) := by
    intro i
    exact Aux61Cov.ae_not_of_hasCovFibreCover
      (Aux61Cov.hasCovFibreCover_of_act
        (Aux61Act.hasActFibreCover_of_dy
          (Aux61UnionK.hasDyActFibreCover_of_localCover (hlocal i))))
      (Aux61Cov.isSettingAvoiding_refWin hneg)
  filter_upwards [ae_all_iff.2 hnull, hcaptured_cover] with x hx hc he
  obtain ⟨i, hi⟩ := hc he
  exact hx i ⟨he, hi⟩

end InteractingSLE.Sec5.Aux61GHist
