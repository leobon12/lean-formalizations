/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2YhSeed

/-!
# B's stage chart at any launched stage: the seed facts

Packet PROVE-T14-SB2LIFT (round 33, D51 item 3). `Sx.stage_seed_facts` asks for a stage `n ≥ 1` (the stage then starts
at an arc mark). A root may be the walk's first piece (`relOff = 0`); there the chart is the identity:

* `stage_seed_facts_zero`: the seed facts of the initial chart;
* **`stage_seed_all`**: the seed facts at every launched stage.

Deterministic.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Sx

open Sec7.PocketTraversal Sec7.Lemma71C Lk LuM GW1Bookkeep Exist Exist.Staged Exist.StagedLaw GW1Conn

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **The seed facts of the initial chart.** -/
theorem stage_seed_facts_zero {θ : ℝ} (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    (∀ y : ℝ, (y : ℂ) ∈ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D 0 →
      y ≤ stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D 0)) ∧
    ∃ (e : ℝ → ℝ) (gc : ℂ → ℂ) (Cc : ℝ),
      (∀ x : ℝ, stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D 0) < x →
        Tendsto (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D 0)).1 (𝓝[H] (x : ℂ))
          (𝓝 (e x : ℂ))) ∧
      Tendsto e (𝓝[>] (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D 0))) (𝓝 0) ∧
      (∀ q ∈ Hbar, Tendsto (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D 0)).2.1
        (𝓝[H] q) (𝓝 (gc q))) ∧
      ContinuousOn gc Hbar ∧ (∀ q ∈ Hbar, ‖gc q - q‖ ≤ Cc) ∧
      gc 0 = (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D 0) : ℂ) ∧
      (∀ y : ℝ, 0 < y → ∃ x : ℝ, stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D 0) < x ∧
        gc (y : ℂ) = x) ∧
      Tendsto (fun y : ℝ => (gc (y : ℂ)).re) (𝓝[>] 0)
        (𝓝[>] (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D 0))) := by
  have e0 : SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D 0 = {0} := by
    simp [SB.prefixPhysSet, ExplState.run, ExplState.init, boundaryWalkSpec]
  have hpt : stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D 0) = 0 := by
    simp [ExplState.run, ExplState.init, boundaryWalkSpec]
  have hc : stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D 0) = Chart.id.recenter 0 := by
    simp [ExplState.run, ExplState.init, boundaryWalkSpec]
  rw [e0, hpt, hc]
  refine ⟨fun y hy => by simp at hy; exact le_of_eq (by exact_mod_cast hy), fun x => x, fun z => z, 0,
    fun x _ => ?_, tendsto_nhdsWithin_of_tendsto_nhds tendsto_id, fun q _ => ?_, continuousOn_id,
    fun q _ => by simp, by simp, fun y hy => ⟨y, hy, rfl⟩, ?_⟩
  · have h : Tendsto (fun z : ℂ => z - ((0 : ℝ) : ℂ)) (𝓝 (x : ℂ)) (𝓝 (x : ℂ)) := by
      simp only [Complex.ofReal_zero, sub_zero]; exact tendsto_id
    exact h.mono_left nhdsWithin_le_nhds
  · have h : Tendsto (fun z : ℂ => z + ((0 : ℝ) : ℂ)) (𝓝 q) (𝓝 q) := by
      simp only [Complex.ofReal_zero, add_zero]; exact tendsto_id
    exact h.mono_left nhdsWithin_le_nhds
  · simp only [Complex.ofReal_re]
    exact tendsto_id

/-- **The seed facts at every launched stage.** -/
theorem stage_seed_all {θ : ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hlm : ∀ k, NoLeftMove κ b jumps θ D k) (hlh : ∀ k, NoLeftHit κ b jumps θ D k) {n : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none) :
    (∀ y : ℝ, (y : ℂ) ∈ SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D n →
      y ≤ stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n)) ∧
    ∃ (e : ℝ → ℝ) (gc : ℂ → ℂ) (Cc : ℝ),
      (∀ x : ℝ, stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) < x →
        Tendsto (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n)).1 (𝓝[H] (x : ℂ))
          (𝓝 (e x : ℂ))) ∧
      Tendsto e (𝓝[>] (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n))) (𝓝 0) ∧
      (∀ q ∈ Hbar, Tendsto (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n)).2.1
        (𝓝[H] q) (𝓝 (gc q))) ∧
      ContinuousOn gc Hbar ∧ (∀ q ∈ Hbar, ‖gc q - q‖ ≤ Cc) ∧
      gc 0 = (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) : ℂ) ∧
      (∀ y : ℝ, 0 < y → ∃ x : ℝ, stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) < x ∧
        gc (y : ℂ) = x) ∧
      Tendsto (fun y : ℝ => (gc (y : ℂ)).re) (𝓝[>] 0)
        (𝓝[>] (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n))) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact stage_seed_facts_zero D
  · exact stage_seed_facts hP hlm hlh hn hl

end InteractingSLE.Theorem14.SB.Sx
