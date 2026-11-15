/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop59StageLawProofTips
import InteractingSLE.Spec.Sec5.Prop513TargetInputs

/-!
# Proposition 5.9's root word satisfies the initial-word conditions

Packet PROVE-PROP59T4. Specification §5.2, proof of Proposition 5.9 (pp. 142–144): "Both possible first angles meet
the one-sided determinacy hypothesis of Lemma 5.6: `b + (π/2)χ ≥ λ` and `−a − (π/2)χ ≤ −λ`". At the root `0` the
first stage of the alternating construction (depth `0`, target band `I₋`, angle `+π/2`) runs the flow line of the
conditional field at angle `π/2` in chart Q, read in the counterflow chart: its word is PROVE-GLUECOND10's image word
`(jwL cL6 κ ρL; jwR cR6 κ ρR)` of the chart-Q flow word `(ρL; ρR)` at angle `π/2` (PROVE-PROP59T3, `isStageInit_jw`).

For a chart-Q boundary word with the extreme-angle heights (R56, `ExtremeHeights`: left heights `≤ −λ + πχ/2`, right
heights `≥ λ − πχ/2`), the flow word at angle `π/2` satisfies the bounds (4.4) (`Prop513Schedule.cond44_upper`), hence
its image word satisfies `IsStageInit`. Proposition 5.13's canonical word `Prop513Target.sourceWord` (Figure 5.1's
bounds) has these heights (`sourceWord_extreme`).

## Main results

* `rootρL`, `rootρR`: the root word of the alternating construction for a chart-Q word `c`;
* **`isStageInit_root`**: `IsStageInit` for the root word of every word with the extreme-angle heights;
* **`isStageInit_sourceWord`**: `IsStageInit` for the root word of Figure 5.1's canonical word;
* `hwL_root`, `hwR_root`: the stage-word conditions at every depth for that word.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped Real

namespace InteractingSLE.Sec5.Prop59System

open Prop59Stage CrossCond.Word49 Prop513Schedule Prop513Target Restart

/-- The number of left marks of the root word of the chart-Q word `c` (the flow word at angle `π/2` plus the left
junction). -/
abbrev rootNL (c : BoundaryWord) : ℕ := flowLineNL c.fn c.jumps 0 + 1

/-- The number of right marks of the root word. -/
abbrev rootNR (c : BoundaryWord) : ℕ := flowLineNR c.fn c.jumps 0 + 1

/-- **The left weights of the root word**: the chart-Q flow word of `c` at angle `π/2` followed by the left junction
weight `κ − 4 − Σρ_L` (R57). -/
def rootρL (κ : ℝ) (c : BoundaryWord) : Fin (rootNL c) → ℝ :=
  jwL cL6 κ (flowLineRhoL κ c.fn c.jumps 0 (π / 2))

/-- **The right weights of the root word**: the chart-Q flow word at angle `π/2` followed by the right junction weight
`κ/2 − 2 − Σρ_R` (R57). -/
def rootρR (κ : ℝ) (c : BoundaryWord) : Fin (rootNR c) → ℝ :=
  jwR cR6 κ (flowLineRhoR κ c.fn c.jumps 0 (π / 2))

theorem rootNL_pos (c : BoundaryWord) : 0 < rootNL c := Nat.succ_pos _

theorem rootNR_pos (c : BoundaryWord) : 0 < rootNR c := Nat.succ_pos _

/-- **The root word satisfies the initial-word conditions** for every chart-Q word with the extreme-angle heights. -/
theorem isStageInit_root {κ : ℝ} (hκ : 0 < κ) {c : BoundaryWord} (hc : ExtremeHeights κ c) :
    IsStageInit κ (rootρL κ c) (rootρR κ c) :=
  isStageInit_jw (cond44_upper hκ hc)

/-- **Proposition 5.13's root word satisfies the initial-word conditions**: the root word of Figure 5.1's canonical
chart-Q word. -/
theorem isStageInit_sourceWord {κ x₀ a b a' b' : ℝ} (hκ : 0 < κ) (hb : IsFig51Bounds κ a b a' b') :
    IsStageInit κ (rootρL κ (sourceWord (x₀ := x₀) hκ hb)) (rootρR κ (sourceWord (x₀ := x₀) hκ hb)) :=
  isStageInit_root hκ (sourceWord_extreme hκ hb)

/-- The leftward stage words of the root word at every even depth. -/
theorem hwL_root {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {c : BoundaryWord} (hc : ExtremeHeights κ c) :
    ∀ j, Even j → IsStageWordN κ (stageρL κ (rootρL κ c) j) (stageρR κ (rootρR κ c) j) :=
  hwL_of_isStageInit hκ hκ4 (isStageInit_root hκ hc)

/-- The rightward stage words of the root word at every odd depth. -/
theorem hwR_root {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) {c : BoundaryWord} (hc : ExtremeHeights κ c) :
    ∀ j, ¬ Even j → IsStageWordN κ (stageρR κ (rootρR κ c) j) (stageρL κ (rootρL κ c) j) :=
  hwR_of_isStageInit hκ hκ4 (isStageInit_root hκ hc)

end InteractingSLE.Sec5.Prop59System
