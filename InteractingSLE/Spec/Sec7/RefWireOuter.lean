/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.RefWireAux131Side
import InteractingSLE.Spec.Sec7.R7OuterConfig

/-!
# R.7 after constructing the outer arms

PROVE-REF-WIRE. The outer arms, their order and counterflow avoidance are supplied
by the landed configuration theorem. The missing outer-pocket construction is
stated separately, with its exact configuration hypothesis. It includes the
shared-side phase comparison; that mathematics is not inferred from arm order.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open LQGMetric (DistOn)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.RefWire

open R7Pocket R7Aux131 R7Outer

universe u

/-- Remaining outer-pocket construction from the already constructed four arms.
This is an explicit unproved input, including the traversal, stopped kernels,
canonical phase and determination. The arm configuration itself is proved. -/
def OuterPocketCompletion (κ rL rR : ℝ) : Prop :=
  ∃ c c' : ℝ, 0 ≤ c ∧ 0 ≤ c' ∧
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens)
      (W : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞)
      (αR βR βL αL : Ω → ℝ≥0 → ℂ) (ζαR ζβR ζβL ζαL : Ω → ℝ≥0∞),
      IsR7OuterConfig κ rL rR c c' P h W ζ αR βR βL αL ζαR ζβR ζβL ζαL →
        R7PocketStopStatement.{u} κ rL rR GoodR7

/-- The outer reference with the existence, regularity, order and avoidance
of its four incoming arms discharged by `exists_isR7OuterConfig`. -/
theorem r7PocketStopStatement_of_outer_completion
    (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{u}) {κ rL rR : ℝ}
    (hκ : 4 < κ) (hL : -2 < rL) (hR : -2 < rR) (hmax : κ / 2 - 4 < max rL rR)
    (hcomplete : OuterPocketCompletion.{u} κ rL rR) :
    R7PocketStopStatement.{u} κ rL rR GoodR7 := by
  obtain ⟨c, c', hc, hc', hcomplete⟩ := hcomplete
  obtain ⟨Ω, mΩ, hSB, P, hP, h, W, ζ, αR, βR, βL, αL, ζαR, ζβR, ζβL, ζαL, hc⟩ :=
    exists_isR7OuterConfig h411 h51 hκ hL hR hmax.le hc hc'
  exact hcomplete P h W ζ αR βR βL αL ζαR ζβR ζβL ζαL hc

/-- R.7 from the extremal two-seed references and the remaining outer-pocket
construction. The outer-arm existence input has been discharged. -/
theorem r7ReferenceStatement_of_extremal_outer_completion
    (h411 : Sec5.Cond44Ref.Prop411QStatement.{u})
    (h51 : Sec5.Cond44Ref.Prop51QStatement.{u})
    (h131 : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → -2 < rR →
      max rL rR = κ / 2 - 4 → R7PocketStopStatement.{u} κ rL rR GoodR7)
    (hout : ∀ κ : ℝ, 4 < κ → ∀ rL rR : ℝ, -2 < rL → -2 < rR →
      κ / 2 - 4 < max rL rR → OuterPocketCompletion.{u} κ rL rR) :
    R7.R7ReferenceStatement.{u} := by
  apply r7ReferenceStatement_of_r7PocketStop
  intro κ hκ rL rR hL hR hmax
  rcases hmax.lt_or_eq with hlt | heq
  · exact r7PocketStopStatement_of_outer_completion h411 h51 hκ hL hR hlt
      (hout κ hκ rL rR hL hR hlt)
  · exact h131 κ hκ rL rR hL hR heq.symm

end InteractingSLE.Sec7.RefWire
