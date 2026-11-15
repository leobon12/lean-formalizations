/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdpFlip
import InteractingSLE.Spec.Supplement.GW2WxMap

/-!
# The near structure (N3), step G3 at the root `0`: the root word's side forms

Packet PROVE-GW2-SDE (round 15). At the root `0` (the counterflow's target), when the counterflow at time `s` stays
off the target (`0 ∉ closure (invHull (rdrv r) s)`), ROOTX's reader of the root's chart image is `0`
(`GW2Wm.baseRead_eq_rootOff`, `rootOff 0 = 0`), so the root-`x` root word is the joint word itself:

* `shiftW_zero`, **`rootWordX_zero`**, `baseRead_zero`;
* **`rootForms_zero`**: the root word's left heights are `−λ′(1 + S) + πχ` and its right heights `λ′(1 + S) − πχ`, with
  `S > −2` (`GW2Sdp.jointWord_left/right_form`, given the counterflow word's prefix sums `> −2`, Lemma GW0) — the
  forms `hformL`, `hformR` of `GW2Sdp.nearStruct_stageWord'`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Finset
open scoped NNReal ENNReal
open QuantumZipper (chiC)

namespace InteractingSLE.Theorem14.GW2Sdp

open Restart Exist.Staged Exist.StagedLaw GW2JointKernel GW2TipSystem.RootH10

theorem shiftW_zero (c : BoundaryWord) : Exist.StagedLaw.BoundaryWord.shiftW 0 c = c := by
  refine Prod.ext rfl (Prod.ext (funext fun i => ?_) rfl)
  simp [Exist.StagedLaw.BoundaryWord.shiftW]

/-- **At the root `0` the reader of the root's chart image is `0`**, when the counterflow at `s` stays off the
target. -/
theorem baseRead_zero (s : ℝ≥0) (r : RecData) (hs : rtime r = s)
    (h0 : ((0 : ℝ) : ℂ) ∉ closure (Supp8.Q3Rel.invHull (rdrv r) s)) : GW2Rz.baseRead 0 s r = 0 := by
  rw [GW2Wm.baseRead_eq_rootOff 0 s r hs h0]
  simp [GW2Wm.rootOff]

/-- **At the root `0` the root word is the joint word.** -/
theorem rootWordX_zero (κ : ℝ) (c' : BoundaryWord) (s : ℝ≥0) (r : RecData) (h0 : GW2Rz.baseRead 0 s r = 0) :
    GW2Wm.rootWordX κ c' 0 s r = jointWordOfRec (specOffset κ) κ c' r := by
  unfold GW2Wm.rootWordX
  rw [h0, shiftW_zero]

variable {κ : ℝ}

/-- **The side forms of the root word at the root `0`** (given the counterflow word's prefix sums `> −2`). -/
theorem rootForms_zero (hκ : 0 < κ) (c' : BoundaryWord)
    (hadmL : ∀ i : Fin (flowLineNL c'.fn c'.jumps 0),
      -2 < ∑ l ∈ univ.filter (fun l => l ≤ i), flowLineRhoL (16 / κ) c'.fn c'.jumps 0 0 l)
    (hadmR : ∀ i : Fin (flowLineNR c'.fn c'.jumps 0),
      -2 < ∑ l ∈ univ.filter (fun l => l ≤ i), flowLineRhoR (16 / κ) c'.fn c'.jumps 0 0 l)
    (s : ℝ≥0) (r : RecData) (h0 : GW2Rz.baseRead 0 s r = 0) :
    (∀ h ∈ rootHeightsL (GW2Wm.rootWordX κ c' 0 s r), h ∈ oldLeftHeights κ ∨
      ∃ S : ℝ, -2 < S ∧ h = -sleLambda (16 / κ) * (1 + S) + Real.pi * chiC κ) ∧
    (∀ h ∈ rootHeightsR (GW2Wm.rootWordX κ c' 0 s r), h ∈ oldRightHeights κ ∨
      ∃ S : ℝ, -2 < S ∧ h = sleLambda (16 / κ) * (1 + S) - Real.pi * chiC κ) := by
  rw [rootWordX_zero κ c' s r h0]
  refine ⟨?_, ?_⟩
  · rintro _ ⟨y, hy, hyJ, rfl⟩
    exact Or.inr (jointWord_left_form hκ c' hadmR r hy hyJ)
  · rintro _ ⟨y, hy, hyJ, rfl⟩
    exact Or.inr (jointWord_right_form hκ c' hadmL r hy hyJ)

end InteractingSLE.Theorem14.GW2Sdp
