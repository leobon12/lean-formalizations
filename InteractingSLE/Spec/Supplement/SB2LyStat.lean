/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LxObs

/-!
# The status bookkeeping of the lockstep step data

Packet PROVE-T14-SB2LIFT (round 13; item 4 of handoff §R12.3). `SB2LtRun.StepOK` asks for the actual walk's status at
every step:

* at a flow step it is done, dead, or a restart mark beyond `p` (with the launch observables if the seed is
  admissible);
* at a connector step it is done, dead, a mark, or a right threshold with `pt ≤ recR` and no restart mark in
  `(pt, p]`.

This file proves that these conditions persist along the walk, from the starting stage `k₀` (even):

* **`FlowSt p s`**: a mark beyond `p`, done, or dead. **`ContSt p s`**: additionally a right threshold;
* **`stRecR_run_le_succ`**: the right record never decreases (finite launched lifetimes, `RecInv`);
* **`contSt_of_flowSt`**: a flow step from `FlowSt` gives `ContSt`, given no left hit and a nonzero lifetime at a
  launch;
* **`flowSt_of_contSt`**: a connector step from `ContSt` gives `FlowSt`. The move from a right threshold goes to a mark
  beyond the current point, which is the record (`PtRec`), hence beyond `p`;
* **`status_run`**: the invariant at every stage from `k₀` up to `N ≤ length`;
* **`stepOK_of_status`**: hence `StepOK` at every step, given the launch observables in the admissible case. These
  are supplied by `launch_obs_of_fill`.

Inputs: finite launched lifetimes, `NoLeftMove`, `NoLeftHit` (for `PtRec`/`RecInv`, `recInv_ptRec_run`), and no
zero lifetime at the launches after `k₀`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw LuM GW1W
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **The status at a flow step**: a mark beyond `p`, done, or dead. -/
def FlowSt (p : ℝ) (s : ExplState) : Prop :=
  (stStatus s = GW1W.stArcM true ∧ p < stPt s) ∨ stStatus s = stDone ∨ stStatus s = stDead

/-- **The status at a connector step**: a right threshold, or a flow-step status. -/
def ContSt (p : ℝ) (s : ExplState) : Prop := stStatus s = stThr (some true) ∨ FlowSt p s

/-- **The right record never decreases** (finite launched lifetimes; `RecInv` at the launch). -/
theorem stRecR_run_le_succ {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D) {k : ℕ}
    (hfin : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (k + 1)).2.2.2.1 k ≠ none →
      (D k).2 ≠ ⊤) (hok : RecInv κ b jumps θ D k) :
    stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D k) ≤
      stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (k + 1)) := by
  rcases hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (k + 1)).2.2.2.1 k with _ | ⟨c, θ'⟩
  · exact stRecR_run_succ_ge_of_noLaunch (κ := κ) (b := b) (jumps := jumps) _ D hl
  · exact (beyond_launch_step hP hl (hfin (by rw [hl]; simp)) hok).1

/-- **A flow step from `FlowSt` gives `ContSt`.** -/
theorem contSt_of_flowSt {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {p : ℝ} {k : ℕ}
    (hk : k < (boundaryWalkSpec b jumps θ true).2.2.length) (hev : k % 2 = 0)
    (hfin : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (k + 1)).2.2.2.1 k ≠ none →
      (D k).2 ≠ ⊤)
    (hnz : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (k + 1)).2.2.2.1 k ≠ none →
      (D k).2 ≠ 0) (hlh : NoLeftHit κ b jumps θ D k)
    (hs : FlowSt p (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D k)) :
    ContSt p (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (k + 1)) := by
  set s := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D k with hsdef
  have hstep := GW1W.run_succ_walk_flow (κ := κ) (b := b) (jumps := jumps) (θ := θ) (right := true) (D := D) hk hev
  rcases hs with ⟨hst, hpt⟩ | hd | hd
  · by_cases hadm : ExplState.IsAdmissibleSeed κ (leftLim b (stPt s)) (rightLim b (stPt s)) θ
    · have hfl := GW1WalkExit.flowStep_of_launchReady (Or.inr ⟨hst, hadm⟩) k (D k)
      have hlne : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (k + 1)).2.2.2.1 k ≠ none := by
        rw [hstep, hfl, launches_launch, Function.update_self]; simp
      have hf := hfin hlne
      have h0 := hnz hlne
      have hleft : ¬ ∃ x : ℝ, x < stRecL s ∧ lHit (stChart s) ⊤ (D k) x := hlh hlne
      have hmin : min (⊤ : ℝ≥0∞) (D k).2 ≠ ⊤ := by rw [min_eq_right le_top]; exact hf
      obtain ⟨-, -, -, -, hst', -⟩ := launch_eq_of_ne_top s k (D k) θ ⊤ hmin
      have hnlt : ¬ (⊤ : ℝ≥0∞) < (D k).2 := not_lt.2 le_top
      unfold ContSt FlowSt
      rw [hstep, hfl, hst']
      by_cases hR : ∃ x : ℝ, stRecR s < x ∧ lHit (stChart s) ⊤ (D k) x
      · left; simp only [lStatus, hnlt, h0, hR, ↓reduceIte]
      · right; right; right; simp only [lStatus, hnlt, h0, hR, hleft, ↓reduceIte]
    · rw [hstep, flowStep_arcM_not hst hadm k (D k) ⊤]
      exact Or.inr (Or.inl ⟨hst, hpt⟩)
  · rw [hstep, flowStep_of_done hd]
    exact Or.inr (Or.inr (Or.inl hd))
  · rw [hstep, flowStep_of_dead hd]
    exact Or.inr (Or.inr (Or.inr hd))

/-- **A connector step from `ContSt` gives `FlowSt`** (`PtRec` and `p ≤ recR`). -/
theorem flowSt_of_contSt {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {p : ℝ} {k : ℕ}
    (hk : k < (boundaryWalkSpec b jumps θ true).2.2.length) (hodd : k % 2 = 1)
    (hpt : PtRec (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D k))
    (hp : p ≤ stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D k))
    (hs : ContSt p (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D k)) :
    FlowSt p (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (k + 1)) := by
  set s := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D k with hsdef
  have hstep := GW1W.run_succ_walk_cont (κ := κ) (b := b) (jumps := jumps) (θ := θ) (right := true) (D := D) hk hodd
  rcases hs with hst | ⟨hst, hpt'⟩ | hd | hd
  · have hpr : stPt s = stRecR s := by
      rcases hpt with h | h | h
      · rw [hst] at h; exact absurd h (by intro h'; cases h')
      · rw [hst] at h; exact absurd h (by intro h'; cases h')
      · exact h
    rw [hstep, contStep_thr_true' b jumps s hst]
    by_cases hC : (restartSet κ b jumps s).Nonempty
    · simp only [hC, ↓reduceDIte]
      have hmem := Finset.min'_mem _ hC
      simp only [restartSet, Finset.mem_filter] at hmem
      refine Or.inl ⟨stStatus_moveAlong' _ _ _ _, ?_⟩
      rw [GW1W.stPt_moveAlong]
      exact lt_of_le_of_lt (hp.trans hpr.symm.le) hmem.2.1
    · simp only [hC, ↓reduceDIte]
      exact Or.inr (Or.inl (stStatus_moveToEnd'' _ _))
  · rw [hstep, contStep_of_arcM hst]
    exact Or.inl ⟨hst, hpt'⟩
  · rw [hstep, contStep_of_done' hd]
    exact Or.inr (Or.inl hd)
  · rw [hstep]
    exact Or.inr (Or.inr (contStep_of_dead (κ := κ) (b := b) (J := jumps) hd true).2.1)

/-- **The status invariant along the walk** from an even starting stage `k₀` up to `N ≤ length`. -/
theorem status_run {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hfin : ∀ j, (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (j + 1)).2.2.2.1 j ≠ none →
      (D j).2 ≠ ⊤)
    (hlm : ∀ j, NoLeftMove κ b jumps θ D j) (hlh : ∀ j, NoLeftHit κ b jumps θ D j) {p : ℝ} (k₀ N : ℕ)
    (hN : N ≤ (boundaryWalkSpec b jumps θ true).2.2.length) (hk₀ : k₀ % 2 = 0)
    (hnz : ∀ k, k₀ ≤ k → (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (k + 1)).2.2.2.1 k ≠ none →
      (D k).2 ≠ 0)
    (hp₀ : p ≤ stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D k₀))
    (hs₀ : FlowSt p (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D k₀)) :
    ∀ k, k₀ ≤ k → k ≤ N → p ≤ stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D k) ∧
      (k % 2 = 0 → FlowSt p (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D k)) ∧
      (k % 2 = 1 → ContSt p (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D k)) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => exact fun _ => ⟨hp₀, fun _ => hs₀, fun h => absurd h (by omega)⟩
  | succ k hk ih =>
    intro hkN
    have hkN' : k < N := hkN
    obtain ⟨hp, hfl, hco⟩ := ih hkN'.le
    have hlen : k < (boundaryWalkSpec b jumps θ true).2.2.length := lt_of_lt_of_le hkN' hN
    obtain ⟨hinv, hpt⟩ := recInv_ptRec_run hP hfin hlm hlh k
    have hp' := hp.trans (stRecR_run_le_succ hP (hfin k) hinv)
    refine ⟨hp', fun hev => ?_, fun hodd => ?_⟩
    · have hodd' : k % 2 = 1 := by omega
      exact flowSt_of_contSt hlen hodd' hpt hp (hco hodd')
    · have hev' : k % 2 = 0 := by omega
      have hc := contSt_of_flowSt hlen hev' (hfin k) (hnz k hk) (hlh k) (hfl hev')
      exact hc

/-- **`StepOK` from the status invariant** (the launch observables enter in the admissible case). -/
theorem stepOK_of_status {ι : ℝ → ℝ} {R₀ p₀ : ℝ} {s₁ s₂ : ExplState} {D₁ D₂ : (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hRp : R₀ ≤ p₀) (flow : Bool) (hpt : PtRec s₁) (hp : p₀ ≤ stRecR s₁)
    (hst : (flow = true → FlowSt p₀ s₁) ∧ (flow = false → ContSt p₀ s₁))
    (hobs : flow = true → stStatus s₁ = GW1W.stArcM true → R₀ < stPt s₁ → p₀ ≤ stPt s₁ →
      ExplState.IsAdmissibleSeed κ (leftLim b (stPt s₁)) (rightLim b (stPt s₁)) θ →
      (D₂.2 = ⊤ ↔ D₁.2 = ⊤) ∧ (D₂.2 = 0 ↔ D₁.2 = 0) ∧
      ((∃ x : ℝ, stRecR s₂ < x ∧ lHit (stChart s₂) ⊤ D₂ x) ↔
        ∃ x : ℝ, stRecR s₁ < x ∧ lHit (stChart s₁) ⊤ D₁ x) ∧
      (¬ ∃ x : ℝ, x < stRecL s₁ ∧ lHit (stChart s₁) ⊤ D₁ x) ∧
      (¬ ∃ x : ℝ, x < stRecL s₂ ∧ lHit (stChart s₂) ⊤ D₂ x) ∧
      (D₁.2 ≠ ⊤ → lRecR s₂ ⊤ D₂ = ι (max (lRecR s₁ ⊤ D₁) p₀))) :
    StepOK κ θ b jumps R₀ ι p₀ flow s₁ s₂ D₁ D₂ := by
  cases flow
  · simp only [StepOK, Bool.false_eq_true, ↓reduceIte]
    rcases hst.2 rfl with hthr | ⟨ha, -⟩ | hd | hd
    · have hpr : stPt s₁ = stRecR s₁ := by
        rcases hpt with h | h | h
        · rw [hthr] at h; exact absurd h (by intro h'; cases h')
        · rw [hthr] at h; exact absurd h (by intro h'; cases h')
        · exact h
      refine Or.inr (Or.inr (Or.inr ⟨hthr, hpr.le, fun x hx => ?_⟩))
      simp only [restartSet, Finset.mem_filter] at hx
      exact lt_of_le_of_lt (hp.trans hpr.symm.le) hx.2.1
    · exact Or.inr (Or.inr (Or.inl ⟨true, ha⟩))
    · exact Or.inl hd
    · exact Or.inr (Or.inl hd)
  · simp only [StepOK, ↓reduceIte]
    rcases hst.1 rfl with ⟨ha, hlt⟩ | hd | hd
    · exact Or.inr (Or.inr ⟨ha, lt_of_le_of_lt hRp hlt, hlt.le, hobs rfl ha (lt_of_le_of_lt hRp hlt) hlt.le⟩)
    · exact Or.inl hd
    · exact Or.inr (Or.inl hd)

end InteractingSLE.Theorem14.SB.Lk
