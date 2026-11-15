/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LgChain
import InteractingSLE.Spec.Supplement.SB2LzExit

/-!
# SB2(2): locating the visit to `R` in the actual walk (the start configuration, actual side)

Packet PROVE-SB2-LIFTSET (round 5). The start bundles `ArcStartData`, `PieceStartData` (`SB2LoAE`) need the stage of
the actual lower walk that first carries `R`, and their actual-side fields. Deterministic, at one sample:

* **`exists_first_stage`**: a point outside the initial physical part but inside the final one is added by a first
  step `n`;
* **`first_stage_cases`**: that step is a launch whose piece contains the point (then `n` is even and the step is the
  launch at the horizon), or a rightward/leftward move to a mark or to the end whose connector contains it;
* **`arc_fields_of_first_stage`**: at a connector step adding `R`, with SB2LIFT's exit classification (`AllowedSt`) and
  the record at the current point (`PtRec`): the step is the rightward move from an outward right threshold (the
  `move` field), `pt ≤ R`, `recR ≤ R`, and every restart mark lies beyond `R` (the `gap` field) or `R` is itself the
  restart mark (then the next piece starts at `R`: a piece start with seed `R`);
* **`piece_fields_of_launch`**: at a launch, the `tip` field and `recR ≤ R` once `pt ≤ R` (which follows from the
  head inclusion `head_of_pieceStart` and Lemma S2's head bound `sb2LowerHead`).
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

/-- Marking a state dead changes no physical point. -/
theorem statePhysicalSet_setDead (x : ℝ) (s : ExplState) : statePhysicalSet x (setDead s) = statePhysicalSet x s := rfl

/-- **The first stage adding a point**: a point not in the initial physical part but in the one at stage `N` is added
by some step `n < N`. -/
theorem exists_first_stage {spec : ExplSpec} {z : ℂ}
    (h0 : z ∉ statePhysicalSet 0 (ExplState.run κ b jumps spec D 0)) {N : ℕ}
    (hN : z ∈ statePhysicalSet 0 (ExplState.run κ b jumps spec D N)) :
    ∃ n < N, z ∉ statePhysicalSet 0 (ExplState.run κ b jumps spec D n) ∧
      z ∈ statePhysicalSet 0 (ExplState.run κ b jumps spec D (n + 1)) := by
  classical
  have hex : ∃ m, z ∈ statePhysicalSet 0 (ExplState.run κ b jumps spec D m) := ⟨N, hN⟩
  have hmz := Nat.find_spec hex
  have hm0 : Nat.find hex ≠ 0 := fun e => h0 (by rw [← e]; exact hmz)
  obtain ⟨n, hn⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  have hle := Nat.find_min' hex hN
  have hmin := Nat.find_min hex (m := n) (by omega)
  rw [hn] at hmz hle
  exact ⟨n, by omega, hmin, hmz⟩

/-- **The step adding a point to a walk's physical part**: a launch whose piece contains it, or a move (to a mark or
to the end) whose connector contains it. -/
theorem first_stage_cases {right : Bool} {z : ℂ} {n : ℕ}
    (hn : z ∉ statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n))
    (hn1 : z ∈ statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (n + 1))) :
    ((ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (n + 1)).2.2.2.1 n ≠ none ∧ n % 2 = 0 ∧
      ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (n + 1) =
        ExplState.launch (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n) n (D n) θ ⊤ ∧
      z ∈ (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n) (D n)).1.tipSet
        (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n) (D n)).2.1
        (newPc (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n) (D n)).2.2) ∨
    (n < (boundaryWalkSpec b jumps θ right).2.2.length ∧ n % 2 = 1 ∧ ∃ (r : Bool) (x : ℝ),
      ExplState.contStep κ b jumps (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n) none right =
        ExplState.moveAlong (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n) r x true ∧
      z ∈ ((↑) : ℝ → ℂ) '' (if r then Icc (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n)) x
        else Icc x (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n)))) ∨
    (n < (boundaryWalkSpec b jumps θ right).2.2.length ∧ n % 2 = 1 ∧ ∃ r : Bool,
      ExplState.contStep κ b jumps (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n) none right =
        ExplState.moveToEnd (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n) r ∧
      z ∈ range (GW1WalkChain.realRay r (stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n)))) := by
  set s := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D n with hs
  by_cases hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (n + 1)).2.2.2.1 n ≠ none
  · have heq := GW1W.launch_walk hl
    refine Or.inl ⟨hl, (GW1W.even_of_launches_walk hl).1, heq, ?_⟩
    rw [heq, GW1WalkChain.statePhysicalSet_launch] at hn1
    rcases hn1 with h | h
    · exact absurd h hn
    · simpa [newPc] using h
  · push Not at hl
    by_cases hlen : n < (boundaryWalkSpec b jumps θ right).2.2.length
    · rcases Nat.mod_two_eq_zero_or_one n with hev | hodd
      · exfalso
        have heq := GW1W.run_succ_walk_flow (κ := κ) (D := D) hlen hev
        have hnl := hl
        rw [heq] at hnl
        rw [heq, GW1W.flowStep_eq_self_of_noLaunch _ _ _ _ _ hnl] at hn1
        exact hn hn1
      · have heq := GW1W.run_succ_walk_cont (κ := κ) (D := D) hlen hodd
        rw [heq] at hn1
        rcases GW1WalkChain.contStep_none_cases (κ := κ) b jumps s right with e | e | ⟨r, x, -, e⟩ | ⟨r, e⟩
        · rw [e] at hn1; exact absurd hn1 hn
        · rw [e, statePhysicalSet_setDead] at hn1; exact absurd hn1 hn
        · rw [e, GW1WalkChain.statePhysicalSet_moveAlong] at hn1
          rcases hn1 with h | h
          · exact absurd h hn
          · exact Or.inr (Or.inl ⟨hlen, hodd, r, x, e, h⟩)
        · rw [e, GW1WalkChain.statePhysicalSet_moveToEnd] at hn1
          rcases hn1 with h | h
          · exact absurd h hn
          · exact Or.inr (Or.inr ⟨hlen, hodd, r, e, h⟩)
    · exfalso
      have heq : ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (n + 1) = s := by
        rw [run_succ, GW1Conn.getElem?_boundaryWalkSpec, ite_eq_right hlen]
      rw [heq] at hn1
      exact hn hn1


/-- Two states with the same pieces and connectors have the same physical part. -/
theorem statePhysicalSet_congr {s s' : ExplState} (h1 : s'.1 = s.1) (h2 : s'.2.1 = s.2.1) (x : ℝ) :
    statePhysicalSet x s' = statePhysicalSet x s := by
  unfold statePhysicalSet; rw [h1, h2]

/-- **The arc start at the first stage adding `R` by a connector** (`R` real): the walk is at an outward right
threshold (`AllowedSt`, with nothing added from a mark, done or dead), so the connector step is the rightward move to
the least restart mark or to the end; `pt ≤ R`, `recR ≤ R` (`PtRec`), and either every restart mark lies beyond `R`
or `R` is itself a restart mark (then the next piece starts at `R`). -/
theorem arc_fields_of_first_stage {n : ℕ} {R : ℝ} (hlen : n < (boundaryWalkSpec b jumps θ true).2.2.length)
    (hodd : n % 2 = 1) (hA : AllowedSt κ b (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n))
    (hpt : PtRec (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n))
    (hn : (R : ℂ) ∉ statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n))
    (hn1 : (R : ℂ) ∈ statePhysicalSet 0 (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1))) :
    (ExplState.contStep κ b jumps (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) none true =
      if hC : (restartSet κ b jumps (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n)).Nonempty then
        ExplState.moveAlong (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) true
          ((restartSet κ b jumps (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n)).min' hC) true
      else ExplState.moveToEnd (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) true) ∧
    stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) ≤ R ∧
    stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) ≤ R ∧
    ((∀ y ∈ restartSet κ b jumps (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n), R < y) ∨
      R ∈ restartSet κ b jumps (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n)) := by
  set s := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n with hs
  have heq : ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1) =
      ExplState.contStep κ b jumps s none true := GW1W.run_succ_walk_cont hlen hodd
  rw [heq] at hn1
  -- the walk is at an outward right threshold
  have hthr : stStatus s = stThr (some true) ∨
      (stStatus s = stThr none ∧ rightLim b (stPt s) + stAngle s * QuantumZipper.chiC κ ≤ -sleLambda κ) := by
    rcases hA with h | h | h | h | ⟨h, hlow⟩
    · rw [contStep_of_arcM h] at hn1; exact absurd hn1 hn
    · rw [contStep_of_done' h] at hn1; exact absurd hn1 hn
    · rw [statePhysicalSet_congr (contStep_pieces b jumps s none true) (contStep_of_dead h true).2.2.2.2] at hn1
      exact absurd hn1 hn
    · exact Or.inl h
    · exact Or.inr ⟨h, by simpa using hlow⟩
  have hmove : ExplState.contStep κ b jumps s none true =
      if hC : (restartSet κ b jumps s).Nonempty then
        ExplState.moveAlong s true ((restartSet κ b jumps s).min' hC) true else ExplState.moveToEnd s true := by
    rcases hthr with h | ⟨h, hlow⟩
    · exact contStep_thr_true' b jumps s h
    · exact contStep_thr_none_right b jumps s h hlow
  have hrec : stPt s = stRecR s := by
    rcases hpt with h | h | h
    · rcases hthr with h' | ⟨h', -⟩ <;> rw [h'] at h <;> cases h
    · rcases hthr with h' | ⟨h', -⟩ <;> rw [h'] at h <;> cases h
    · exact h
  refine ⟨hmove, ?_⟩
  rw [hmove] at hn1
  by_cases hC : (restartSet κ b jumps s).Nonempty
  · simp only [hC, ↓reduceDIte] at hn1
    rw [GW1WalkChain.statePhysicalSet_moveAlong] at hn1
    rcases hn1 with h | ⟨y, hy, hyR⟩
    · exact absurd h hn
    · simp only [↓reduceIte] at hy
      have hyR' : y = R := Complex.ofReal_injective hyR
      subst hyR'
      refine ⟨hy.1, hrec ▸ hy.1, ?_⟩
      rcases eq_or_lt_of_le hy.2 with he | hlt
      · exact Or.inr (he ▸ Finset.min'_mem _ hC)
      · exact Or.inl fun z hz => lt_of_lt_of_le hlt (Finset.min'_le _ _ hz)
  · simp only [hC, ↓reduceDIte] at hn1
    rw [GW1WalkChain.statePhysicalSet_moveToEnd, GW1WalkChain.range_realRay] at hn1
    rcases hn1 with h | ⟨y, hy, hyR⟩
    · exact absurd h hn
    · simp only [↓reduceIte] at hy
      have hyR' : y = R := Complex.ofReal_injective hyR
      subst hyR'
      exact ⟨hy, hrec ▸ hy, Or.inl fun z hz => absurd ⟨z, hz⟩ hC⟩


/-- **The piece start's status fields at a launch**: a launching state is not an interior tip, and its record is at
its current point (`PtRec`), hence `≤ R` once the current point is. -/
theorem piece_fields_of_launch {n : ℕ} {R : ℝ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none)
    (hA : n = 0 ∨ AllowedSt κ b (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n))
    (hpt : PtRec (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n))
    (hle : stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) ≤ R) :
    stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) ≠ .inr (.inl ()) ∧
      stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) ≤ R := by
  set s := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n with hs
  have hnone : s.2.2.2.1 n = none := launches_run_of_le (κ := κ) (b := b) (jumps := jumps) _ D (le_refl n)
  have hev := (GW1W.even_of_launches_walk hl)
  have hstep := GW1W.run_succ_walk_flow (κ := κ) (D := D) hev.2 hev.1
  refine ⟨?_, ?_⟩
  · rcases hA with h0 | h
    · subst h0
      have : stStatus s = .inl () := by simp [hs, ExplState.run, ExplState.init]
      rw [this]; intro e; cases e
    · rcases h with h | h | h | h | ⟨h, -⟩ <;> rw [h] <;> intro e <;> cases e
  · rcases hpt with h | h | h
    · rw [hstep, flowStep_of_done h] at hl; exact absurd hnone hl
    · rw [hstep, flowStep_of_dead h] at hl; exact absurd hnone hl
    · rw [← h]; exact hle

end InteractingSLE.Theorem14.SB.Lk
