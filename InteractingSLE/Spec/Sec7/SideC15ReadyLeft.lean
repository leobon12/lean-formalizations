/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC15Left
import InteractingSLE.Spec.Sec7.SideC15ReadyBranch

/-!
# Ready pockets have the required side from the physical frontier facts

PROVE-SIDE-COLLAR2. Both readiness alternatives already supply the right
wall visits. Combine them with the outer left frontier's rational-time
avoidance to discharge the side premise of the initial source formula.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace InteractingSLE.Wire.Current.SideTest

open WangWu Sec7 Sec7.SideC15 Sec7.PocketCoord Sec7.PocketJordan Sec7.Lemma71I

variable {Ω : Type} [MeasurableSpace Ω]

/-- The original change pocket lies on the required side almost surely,
from the actual outer frontier and rational-time counterflow avoidance. -/
theorem ae_changePocket_subset_leftSideOf_of_ready
    {j : SideTest Ω} {d : WordObjects Ω} (hj : j.Ready d)
    (hβ : ∀ᵐ ω ∂d.measure, IsSimpleProper (d.outerWall ω))
    (hLβ : ∀ᵐ ω ∂d.measure, d.leftWall j.seed ω (StripSys.rt j.seed) =
      d.outerWall ω (StripSys.rt j.seed))
    (hη : ∀ ω, ContinuousOn (d.curve ω) (Ici 0))
    (hav : ∀ᵐ ω ∂d.measure, ∀ q : ℚ, 0 ≤ (q : ℝ) →
      negInv (d.curve ω q) ∉ leftSideOf (range (d.outerWall ω))) :
    ∀ᵐ ω ∂d.measure, ω ∈ j.event →
      changePocket (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed) ⊆
        leftSideOf (range (d.rightWall ω)) := by
  rcases hj with ⟨_, _, _, hG, _, hcfg, hcfgI, _, hAG, _, _, _, _⟩
  filter_upwards [hβ, hLβ, hav] with ω hβω hLβω havω hω
  have hωG : ω ∈ j.outerEvent := by
    cases hI : j.infinite <;> simp only [hI, Bool.false_eq_true, ↓reduceIte] at hAG <;>
      exact (hAG hω).1
  have h := (hG ω hωG).1
  have hVis : IsWallVisited (d.rightWall ω) (d.curve ω) := by
    cases hI : j.infinite
    · simp only [hI, Bool.false_eq_true, ↓reduceIte] at hAG
      exact (hcfg ω hωG (hAG hω).2).visR
    · simp only [hI, ↓reduceIte] at hAG
      have h0 : rightLo (d.rightWall ω) (d.leftWall j.seed ω) (StripSys.rt j.seed) = 0 :=
        le_antisymm (le_of_not_gt (hAG hω).2) h.changeCorner_props.1.1
      exact (hcfgI ω hωG h0).visR
  exact changePocket_subset_leftSideOf_of_cfAvoid h hβω hLβω hVis (hη ω) havω

end InteractingSLE.Wire.Current.SideTest
