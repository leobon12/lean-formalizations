/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LeArc

/-!
# SB2(2): the visit to `R` at a restart mark (a piece start with seed `R`), `recAfter` there, the zero root

Packet PROVE-SB2-LIFTSET (round 7). `arcStart_actual` leaves the case where the connector through `R` ends exactly at
`R` (a restart mark). Then the walk starts its next piece at `R`:

* **`run_eq_of_stuck_mark`**: a walk at a restart mark whose flow instruction does not launch stays there forever
  (the seed is inadmissible, and connector instructions at a mark change nothing), so a walk that finishes launches at
  every mark it stops at;
* **`markStart`**: at the first stage carrying `R`, if `R` is the restart mark, the actual fields of the piece start at
  `o + 2`: the launch, not a tip, `pt = R`, `recR ≤ R`, and `R` lies on the launched piece (the seed is on its piece,
  by piece simplicity `WalkChainFacts`);
* **`recAfter_of_mark`**, `stRecR_moveAlong_eq`: there the record after the piece is `≥ R` (the record at the launching
  stage is `R`; records do not decrease, `stRecR_run_le_succ'` with SB2LIFT's `RecInv`);
* `zeroDrv`, **`isRegularDriver_zeroDrv`**, `zeroDrv_snd`: the relative zero root of an arc start (`reg₀`, `zero₀`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1Bookkeep
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **A walk at a restart mark whose flow instruction does not launch stays there forever** (the seed is
inadmissible, so every later flow instruction leaves the state, and every connector instruction at a mark too). -/
theorem run_eq_of_stuck_mark {n : ℕ} (hev : n % 2 = 0) (hlen : n < (boundaryWalkSpec b jumps θ true).2.2.length)
    (hst : stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) = GW1W.stArcM true)
    (hnl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n = none) :
    ∀ k, n ≤ k → ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D k =
      ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n := by
  set s := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n with hs
  have hadm : ¬ ExplState.IsAdmissibleSeed κ (leftLim b (stPt s)) (rightLim b (stPt s)) θ := by
    intro hadm
    have heq := GW1W.run_succ_walk_flow (κ := κ) (D := D) hlen hev
    rw [heq, GW1WalkExit.flowStep_of_launchReady (Or.inr ⟨hst, hadm⟩) n (D n), launches_launch,
      Function.update_self] at hnl
    cases hnl
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => rfl
  | succ k hk ih =>
    by_cases hlen : k < (boundaryWalkSpec b jumps θ true).2.2.length
    · rcases Nat.mod_two_eq_zero_or_one k with hev' | hodd
      · rw [GW1W.run_succ_walk_flow (κ := κ) (D := D) hlen hev', ih, flowStep_arcM_not hst hadm k (D k) ⊤]
      · rw [GW1W.run_succ_walk_cont (κ := κ) (D := D) hlen hodd, ih, contStep_of_arcM hst true]
    · rw [run_succ, GW1Conn.getElem?_boundaryWalkSpec, ite_eq_right hlen]
      exact ih


/-- **`R` is the restart mark: a piece start with seed `R`.** At the first stage carrying `R` the connector from stage
`o + 1` ends exactly at `R` (a restart mark); the walk, which finishes, launches at `R` (`run_eq_of_stuck_mark`), and
the actual fields of the piece start at `o + 2` hold: the launch, not a tip, `pt = R`, `recR ≤ R`, and `R` lies on
the launched piece (piece simplicity: the seed is on its piece). -/
theorem markStart (hW : WalkChainFacts κ b jumps θ D) {o N : ℕ} {R : ℝ} (ho : o % 2 = 0)
    (hlen : o + 2 < (boundaryWalkSpec b jumps θ true).2.2.length)
    (hd : stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D N) = stDone) (hoN : o + 2 ≤ N)
    (hmove : ExplState.contStep κ b jumps (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1)) none
        true =
      if hC : (restartSet κ b jumps (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1))).Nonempty then
        ExplState.moveAlong (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1)) true
          ((restartSet κ b jumps (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1))).min' hC) true
      else ExplState.moveToEnd (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1)) true)
    (hmark : R ∈ restartSet κ b jumps (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1)))
    (hrec : stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1)) ≤ R)
    (hn : (R : ℂ) ∉ statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1)))
    (hn1 : (R : ℂ) ∈ statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1 + 1))) :
    ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 2 + 1) =
        ExplState.launch (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 2)) (o + 2) (D (o + 2)) θ ⊤ ∧
      stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 2)) ≠ .inr (.inl ()) ∧
      stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 2)) = R ∧
      stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 2)) ≤ R ∧
      (R : ℂ) ∈ (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 2)) (D (o + 2))).1.tipSet
        (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 2)) (D (o + 2))).2.1
        (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 2)) (D (o + 2))).2.2 := by
  set s := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 1) with hs
  have hC : (restartSet κ b jumps s).Nonempty := ⟨R, hmark⟩
  have hstep : ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 2) =
      ExplState.moveAlong s true ((restartSet κ b jumps s).min' hC) true := by
    rw [show o + 2 = o + 1 + 1 by omega, GW1W.run_succ_walk_cont (κ := κ) (D := D) (by omega) (by omega), hmove]
    simp only [hC, ↓reduceDIte]
  -- the connector ends exactly at `R`
  have hmR : (restartSet κ b jumps s).min' hC = R := by
    have h1 := hn1
    rw [show o + 1 + 1 = o + 2 by omega, hstep, GW1WalkChain.statePhysicalSet_moveAlong] at h1
    rcases h1 with h | ⟨y, hy, hyR⟩
    · exact absurd h hn
    · have hyR' : y = R := Complex.ofReal_injective hyR
      subst hyR'
      simp only [↓reduceIte] at hy
      exact le_antisymm (Finset.min'_le _ _ hmark) hy.2
  rw [hmR] at hstep
  set s₂ := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 2) with hs₂
  have hst₂ : stStatus s₂ = GW1W.stArcM true := by rw [hstep, stStatus_moveAlong']
  have hpt₂ : stPt s₂ = R := by rw [hstep, GW1W.stPt_moveAlong]
  have hrec₂ : stRecR s₂ ≤ R := by rw [hstep, stRecR_moveAlong_true]; exact max_le hrec le_rfl
  -- the walk launches at `R`
  have hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 2 + 1)).2.2.2.1 (o + 2) ≠ none := by
    intro hnl
    have e := run_eq_of_stuck_mark (by omega) hlen hst₂ hnl N hoN
    rw [e, hst₂] at hd
    cases hd
  have hlaunch := GW1W.launch_walk hl
  have hl' : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (o + 2 + 1)).2.2.2.1 (o + 2) =
      some (stChart s₂, θ) := by
    rw [hlaunch, launches_launch, Function.update_self]
  refine ⟨hlaunch, (fun e => by rw [hst₂] at e; cases e), hpt₂, hrec₂, ?_⟩
  -- the seed lies on its piece
  have hnd : stStatus s₂ ≠ stDone := fun e => by rw [hst₂] at e; cases e
  have hseed := (prefix_facts hW.1 hW.2 (o + 2)).2 hnd
  have hpiece := hW.1 (o + 2) (stChart s₂) θ hl' hseed
  rw [Lx.instrTime_boundaryWalk_of_launch hl'] at hpiece
  have hmeet := GW1WalkChain.tipSet_inter_of_pieceSimpleAt hpiece
  have hmem : (stPt s₂ : ℂ) ∈ (stChart s₂).tipSet
      (fun r => (D (o + 2)).1 (min (r : ℝ≥0∞) (min ⊤ (D (o + 2)).2)).toNNReal) (min ⊤ (D (o + 2)).2) := by
    have : (stPt s₂ : ℂ) ∈ ({(stPt s₂ : ℂ)} : Set ℂ) := rfl
    rw [← hmeet] at this
    exact this.1
  rw [hpt₂] at hmem
  exact hmem


/-- **`recAfter` at a mark start**: the record at the launching stage is `R` (`stPt = R = recR`), and the record does
not decrease over the launch (`stRecR_run_le_succ'`, given SB2LIFT's record invariant at that stage). -/
theorem recAfter_of_mark {n : ℕ} {R : ℝ} (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hinv : RecInv κ b jumps θ D n)
    (hR : R ≤ stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n)) :
    R ≤ stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)) :=
  hR.trans (stRecR_run_le_succ' hP hinv)

/-- At a mark start the record at the launching stage is `R` itself (the connector ended at `R` beyond the old
record). -/
theorem stRecR_moveAlong_eq {s : ExplState} {R : ℝ} (hrec : stRecR s ≤ R) :
    stRecR (ExplState.moveAlong s true R true) = R := by
  rw [stRecR_moveAlong_true, max_eq_right hrec]

/-- **The relative zero root** of an arc start (`ArcStartData.reg₀`, `zero₀`): the driver `0` with lifetime `0`. -/
def zeroDrv : (ℝ≥0 → ℝ) × ℝ≥0∞ := (fun _ => 0, 0)

/-- The zero root is a regular driver. -/
theorem isRegularDriver_zeroDrv : IsRegularDriver zeroDrv :=
  ⟨fun t ht => absurd ht (by simp [zeroDrv]), rfl, fun _ _ => rfl, fun _ h => absurd h (by simp [zeroDrv])⟩

/-- The zero root has lifetime `0`. -/
theorem zeroDrv_snd : zeroDrv.2 = 0 := rfl

end InteractingSLE.Theorem14.SB.Lk
