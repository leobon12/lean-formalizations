/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2JdStart
import InteractingSLE.Spec.Supplement.SBLzRun

/-!
# SB2(2)'s joint stage induction: the run chart at a restart mark

Packet PROVE-SB2-LIFTSET (round 20). A stage piece starts at a restart mark (`stArcM`). In a boundary walk such a
state was reached by a connector move (`moveAlong`) and is unchanged since:

* **`chart_zero_of_arcM`**: at a restart mark the run chart reads `0` at the current point (the move recentres a real
  chart at the new point, `stChart_moveAlong_self`);
* **`continuousWithinAt_of_arcM`**: if every earlier stage keeps the record invariant and moves only right beyond the
  record, the run chart is continuous from `ℍ` at the current point (`continuousWithinAt_runChart_fwd` at the move's
  target, which lies beyond the record; `BeyondOK`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1Bookkeep

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **At a restart mark the run chart reads `0` at the current point.** -/
theorem chart_zero_of_arcM (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    ∀ n, n ≤ (boundaryWalkSpec b jumps θ true).2.2.length → ∀ r,
      stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) = GW1W.stArcM r →
      (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n)).1
        (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n)) = 0 := by
  intro n
  induction n with
  | zero => intro _ r hr; cases hr
  | succ n ih =>
    intro hn r hr
    set Rn := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D with hRdef
    rcases Nat.mod_two_eq_zero_or_one n with hev | hodd
    · have hf : Rn (n + 1) = ExplState.flowStep κ b false (Rn n) n (D n) θ ⊤ :=
        GW1W.run_succ_walk_flow (by omega) hev
      rcases GW1W.flowStep_false_cases (κ := κ) (b := b) (Rn n) n (D n) θ ⊤ with he | he
      · rw [hf, he] at hr ⊢
        exact ih (by omega) r hr
      · rw [hf, he] at hr
        exact (WalkSeedFinite.launch_top_ne_arcM _ _ _ _ _ hr).elim
    · have hc : Rn (n + 1) = ExplState.contStep κ b jumps (Rn n) none true :=
        GW1W.run_succ_walk_cont (by omega) hodd
      rw [hc] at hr ⊢
      rcases contStep_cases (κ := κ) (b := b) (jumps := jumps) (Rn n) none true with
        he | he | ⟨r', x, mk, he⟩ | ⟨r', he⟩
      · rw [he] at hr ⊢
        exact ih (by omega) r hr
      · rw [he] at hr
        exact (Lz.stStatus_setDead_ne_arcM _ _ hr).elim
      · rw [he, GW1W.stPt_moveAlong]
        exact stChart_moveAlong_self (isRealChart_run _ D n) r' x mk
      · rw [he] at hr
        exact (Lz.stStatus_moveToEnd_ne_arcM _ _ _ hr).elim

/-- **At a restart mark the run chart is continuous from `ℍ` at the current point**, if every earlier stage keeps
the record invariant and moves only right beyond the record. -/
theorem continuousWithinAt_of_arcM {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D) :
    ∀ n, n ≤ (boundaryWalkSpec b jumps θ true).2.2.length →
      (∀ k < n, RecInv κ b jumps θ D k ∧ WalkMovesRight κ b jumps θ D k) → ∀ r,
      stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) = GW1W.stArcM r →
      ContinuousWithinAt (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n)).1 H
        (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n)) := by
  intro n
  induction n with
  | zero => intro _ _ r hr; cases hr
  | succ n ih =>
    intro hn hinv r hr
    have ih' := ih (by omega) (fun k hk => hinv k (by omega))
    set Rn := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D with hRdef
    rcases Nat.mod_two_eq_zero_or_one n with hev | hodd
    · have hf : Rn (n + 1) = ExplState.flowStep κ b false (Rn n) n (D n) θ ⊤ :=
        GW1W.run_succ_walk_flow (by omega) hev
      rcases GW1W.flowStep_false_cases (κ := κ) (b := b) (Rn n) n (D n) θ ⊤ with he | he
      · rw [hf, he] at hr ⊢
        exact ih' r hr
      · rw [hf, he] at hr
        exact (WalkSeedFinite.launch_top_ne_arcM _ _ _ _ _ hr).elim
    · have hc : Rn (n + 1) = ExplState.contStep κ b jumps (Rn n) none true :=
        GW1W.run_succ_walk_cont (by omega) hodd
      rcases contStep_cases (κ := κ) (b := b) (jumps := jumps) (Rn n) none true with
        he | he | ⟨r', x, mk, he⟩ | ⟨r', he⟩
      · rw [hc, he] at hr ⊢
        exact ih' r hr
      · rw [hc, he] at hr
        exact (Lz.stStatus_setDead_ne_arcM _ _ hr).elim
      · obtain ⟨hrec, hmv⟩ := hinv n (by omega)
        obtain ⟨-, hx⟩ := hmv r' x mk (hc.trans he)
        obtain ⟨h1, h2, -, -⟩ := hrec x hx
        obtain ⟨hcw, -⟩ := continuousWithinAt_runChart_fwd hP x n h1 h2
        rw [hc, he, GW1W.stPt_moveAlong]
        have hfun : (stChart (ExplState.moveAlong (Rn n) r' x mk)).1 =
            fun z => (stChart (Rn n)).1 z - (((stChart (Rn n)).1 x).re : ℂ) := by
          funext z; rw [stChart_moveAlong']; rfl
        rw [hfun]
        exact hcw.sub continuousWithinAt_const
      · rw [hc, he] at hr
        exact (Lz.stStatus_moveToEnd_ne_arcM _ _ _ hr).elim

end InteractingSLE.Theorem14.SB.Lk
