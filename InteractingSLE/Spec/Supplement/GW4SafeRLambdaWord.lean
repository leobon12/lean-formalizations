/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRLambdaAccess
import InteractingSLE.Spec.Supplement.GW4SafeREtaWord

/-! # GW4: ambient and component words on the exposed interval -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC)

namespace InteractingSLE.Theorem14.GW4Fix

open MartChar.RealFlow Sec7.R5Lift Sec7.PhaseSel Restart Supp8.Q3Stop

/-- An ambient exposed coordinate is off every force jump, including at
real physical landings. The finite force positions use their actual
geometric evolution from ordered initial positions. -/
theorem ambient_exposed_word {nL nR : ℕ} {κ : ℝ}
    {W : ℝ → ℝ} (hW : Continuous W) {s : ℝ} (hs : 0 ≤ s)
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j)
    {VL : Fin nL → ℝ} {VR : Fin nR → ℝ}
    (hVL : ∀ i, VL i = -rightImg (fun r => -W r) (-xL i) s)
    (hVR : ∀ j, VR j = rightImg W (xR j) s)
    {x' ξ : ℝ} (hx'0 : x' ≠ 0)
    (hx' : x' ∈ Ioo (-rightImg (fun r => -W r) 0 s - W s) (rightImg W 0 s - W s))
    (hSide : ξ < 0 ↔ x' < 0) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) :
    x' ∉ forceJumpSet (fun i => VL i - W s) (fun j => VR j - W s) ∧
      forceBoundaryData κ ρL ρR (fun i => VL i - W s) (fun j => VR j - W s) x' =
        if ξ < 0 then -(Real.pi / Real.sqrt κ) else Real.pi / Real.sqrt κ := by
  have hleft : ∀ i, VL i - W s < x' := by
    intro i
    rw [hVL i]
    have hm : rightImg (fun r => -W r) 0 s ≤ rightImg (fun r => -W r) (-xL i) s :=
      rightImg_mono_index hW.neg hs (neg_nonneg.2 (hxL i))
    exact (sub_le_sub_right (neg_le_neg hm) (W s)).trans_lt hx'.1
  have hright := (ambient_force_positions hW hs hxL hxR hVL hVR hx').2
  constructor
  · simp only [forceJumpSet, mem_insert_iff, mem_union, mem_range, not_or, not_exists]
    exact ⟨hx'0, fun i => (hleft i).ne, fun j => (hright j).ne'⟩
  · rw [forceBoundaryData_inner _ _ (fun _ i => (hleft i).le) (fun _ => hright)]
    simp only [hSide]

/-- The old exposed word and its lattice phase equal the actual current
component word, once the reflected boundary map identifies the side. -/
theorem component_phase_word_of_ambient {Ω : Type*} (k : ℝ) (c₀ : BoundaryWord)
    (X : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (R : ℝ≥0 → Ω → ℝ) (V : Ω → ℝ≥0∞)
    {ω : Ω} (hRc : Continuous (R · ω)) (hR0 : R 0 ω = 0) (q : ℝ≥0)
    {ξ : ℝ} (hξ : ξ ∈ Ioo
      (componentVL k c₀ X R V (componentSeedL k c₀) q ω - R q ω)
      (componentVR k c₀ X R V (componentSeedR k c₀) q ω - R q ω))
    {nL nR : ℕ} {W : ℝ → ℝ} (hW : Continuous W) {s : ℝ} (hs : 0 ≤ s)
    {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    (hxL : ∀ i, xL i ≤ 0) (hxR : ∀ j, 0 ≤ xR j)
    {VL : Fin nL → ℝ} {VR : Fin nR → ℝ}
    (hVL : ∀ i, VL i = -rightImg (fun r => -W r) (-xL i) s)
    (hVR : ∀ j, VR j = rightImg W (xR j) s)
    {x' : ℝ} (hx'0 : x' ≠ 0)
    (hx' : x' ∈ Ioo (-rightImg (fun r => -W r) 0 s - W s) (rightImg W 0 s - W s))
    (hSide : ξ < 0 ↔ x' < 0) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (δ : ℝ) :
    forceBoundaryData k ρL ρR (fun i => VL i - W s) (fun j => VR j - W s) x' + δ =
      phaseData k (typedRhoL (wordType k c₀)) (typedRhoR (wordType k c₀))
        (fun i => componentVL k c₀ X R V i q ω - R q ω)
        (fun j => componentVR k c₀ X R V j q ω - R q ω) δ ξ := by
  rw [(ambient_exposed_word hW hs hxL hxR hVL hVR hx'0 hx' hSide ρL ρR).2,
    component_phaseData_exposed k c₀ X R V hRc hR0 q δ hξ]

end InteractingSLE.Theorem14.GW4Fix
