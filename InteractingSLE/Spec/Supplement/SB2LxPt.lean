/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LvObs
import InteractingSLE.Spec.Supplement.SBLuPath

/-!
# The walk moves right: the current point stays at the record

Packet PROVE-T14-SB2LIFT (round 12; item 2 of handoff §R11.3). Round 11's record invariant `recInv_run` took the
named input `WalkMovesRight`: every boundary move goes to the right, beyond the current record. This file reduces it
to two more primitive inputs, at every step:

* **`NoLeftMove`**: the walk never moves along the boundary to the left;
* **`NoLeftHit`**: no launched piece hits the real line left of the left record.

The invariant **`PtRec`** says that the current point is the right record, unless the walk has finished or died.
**`recInv_ptRec_run`** proves `RecInv` and `PtRec` together at every stage:

* a step without a launch is unchanged, dead, a move, or the end. A right move starts at the current point
  (`lt_of_run_succ_eq_moveAlong`), which is the record by `PtRec`, so the move goes beyond the record;
* at a launch with a finite lifetime, a right hit puts the current point at the new record. A zero lifetime swallows
  nothing beyond the record: the chart points there are nonzero by `RecInv`, so they are alive at time `0`.
  Otherwise the walk dies.

So `WalkMovesRight` holds at every step (`walkMovesRight_of_ptRec`). Also `stPt ≤ stRecR` at every stage, which is
the connector-step condition `pt ≤ recR` of `StepOK`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar fwdMap IsForwardSol)

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw LuM

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **The current point is at the right record**, unless the walk has finished or died. -/
def PtRec (s : ExplState) : Prop := stStatus s = stDone ∨ stStatus s = stDead ∨ stPt s = stRecR s

/-- **Named input: no left move at step `n`.** -/
def NoLeftMove (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (θ : ℝ) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (n : ℕ) : Prop :=
  ∀ (w : ℝ) (m : Bool), ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1) ≠
    ExplState.moveAlong (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) false w m

/-- **Named input: no left hit at step `n`.** -/
def NoLeftHit (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (θ : ℝ) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (n : ℕ) : Prop :=
  (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none →
    ¬ ∃ x : ℝ, x < stRecL (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) ∧
      lHit (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n)) ⊤ (D n) x

theorem stStatus_setDead (s : ExplState) : stStatus (setDead s) = stDead := by
  obtain ⟨pieces, arcs, ret, lau, chart, status, pt, angle, recR, recL⟩ := s
  rfl

theorem arcs_setDead (s : ExplState) : (setDead s).2.1 = s.2.1 := by
  obtain ⟨pieces, arcs, ret, lau, chart, status, pt, angle, recR, recL⟩ := s
  rfl

theorem arcs_moveAlong_ne (s : ExplState) (r : Bool) (x : ℝ) (m : Bool) :
    (ExplState.moveAlong s r x m).2.1 ≠ s.2.1 := by
  obtain ⟨pieces, arcs, ret, lau, chart, status, pt, angle, recR, recL⟩ := s
  intro h
  have := congrArg List.length h
  simp [ExplState.moveAlong] at this

theorem stStatus_moveAlong' (s : ExplState) (r : Bool) (x : ℝ) (m : Bool) :
    stStatus (ExplState.moveAlong s r x m) = .inr (.inr (.inr (.inl (r, m)))) := by
  obtain ⟨pieces, arcs, ret, lau, chart, status, pt, angle, recR, recL⟩ := s
  rfl

theorem stStatus_moveToEnd'' (s : ExplState) (r : Bool) : stStatus (ExplState.moveToEnd s r) = stDone := by
  obtain ⟨pieces, arcs, ret, lau, chart, status, pt, angle, recR, recL⟩ := s
  rfl

/-- **A walk step is unchanged, a flow step or a connector step.** -/
theorem run_succ_walk_cases (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (n : ℕ) :
    ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1) =
        ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n ∨
      ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1) =
        ExplState.flowStep κ b false (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) n (D n) θ ⊤ ∨
      ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1) =
        ExplState.contStep κ b jumps (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) none true := by
  by_cases hn : n < (boundaryWalkSpec b jumps θ true).2.2.length
  · rcases Nat.mod_two_eq_zero_or_one n with hev | hodd
    · exact Or.inr (Or.inl (GW1W.run_succ_walk_flow hn hev))
    · exact Or.inr (Or.inr (GW1W.run_succ_walk_cont hn hodd))
  · left
    rw [run_succ]
    have : (boundaryWalkSpec b jumps θ true).2.2[n]? = none := List.getElem?_eq_none (not_lt.1 hn)
    rw [this]

/-- A finished or dead walk state does not change its connectors. -/
theorem arcs_run_succ_of_terminal (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {n : ℕ}
    (hs : stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) = stDone ∨
      stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) = stDead) :
    (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.1 =
      (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n).2.1 := by
  rcases run_succ_walk_cases (κ := κ) (b := b) (jumps := jumps) (θ := θ) D n with e | e | e <;> rw [e]
  · rcases hs with hs | hs
    · rw [flowStep_of_done hs]
    · rw [flowStep_of_dead hs]
  · rcases hs with hs | hs
    · rw [contStep_of_done' hs]
    · exact (contStep_of_dead (κ := κ) (b := b) (J := jumps) hs true).2.2.2.2

/-- **A right move of a walk starts at the current point and goes beyond it.** -/
theorem lt_of_run_succ_eq_moveAlong (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {n : ℕ} {w : ℝ} {m : Bool}
    (h : ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1) =
      ExplState.moveAlong (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) true w m) :
    stPt (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) < w := by
  set s := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n with hs
  have hne := arcs_moveAlong_ne s true w m
  rcases run_succ_walk_cases (κ := κ) (b := b) (jumps := jumps) (θ := θ) D n with e | e | e
  · rw [e] at h
    exact absurd (congrArg (fun t : ExplState => t.2.1) h).symm hne
  · rw [e] at h
    rcases flowStep_trichotomy (κ := κ) (b := b) false s n (D n) θ ⊤ with e' | e' | e'
    · rw [e'] at h; exact absurd (congrArg (fun t : ExplState => t.2.1) h).symm hne
    · rw [e'] at h
      exact absurd ((congrArg (fun t : ExplState => t.2.1) h).symm.trans (arcs_setDead s)) hne
    · rw [e'] at h
      exact absurd ((congrArg (fun t : ExplState => t.2.1) h).symm.trans (GW2aCont.arcs_launch s n (D n) θ ⊤)) hne
  · rw [e] at h
    rcases contStep_four_cases (κ := κ) (b := b) (jumps := jumps) s none true with ⟨ha, -⟩ | ⟨x, mk, e', hx⟩ |
      ⟨x, mk, e', -⟩ | ⟨r, e'⟩
    · rw [h] at ha; exact absurd ha hne
    · rw [h] at e'
      have hw : w = x := by
        have := congrArg stPt e'
        simpa [stPt_moveAlong] using this
      exact hw ▸ hx
    · rw [h] at e'
      have := congrArg stStatus e'
      rw [stStatus_moveAlong', stStatus_moveAlong'] at this
      simp at this
    · rw [h] at e'
      have := congrArg stStatus e'
      rw [stStatus_moveAlong', stStatus_moveToEnd''] at this
      exact absurd this (by intro h'; cases h')

/-- **`PtRec` and no left move give `WalkMovesRight`.** -/
theorem walkMovesRight_of_ptRec (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {n : ℕ}
    (hpt : PtRec (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n))
    (hleft : NoLeftMove κ b jumps θ D n) : WalkMovesRight κ b jumps θ D n := by
  intro r w m e
  cases r
  · exact absurd e (hleft w m)
  · refine ⟨rfl, ?_⟩
    rcases hpt with hd | hd | hpr
    · exact absurd ((arcs_run_succ_of_terminal D (Or.inl hd)).symm.trans (by rw [e])) (arcs_moveAlong_ne _ _ _ _).symm
    · exact absurd ((arcs_run_succ_of_terminal D (Or.inr hd)).symm.trans (by rw [e])) (arcs_moveAlong_ne _ _ _ _).symm
    · rw [← hpr]
      exact lt_of_run_succ_eq_moveAlong D e

/-- **A step without a launch keeps `PtRec`** (no left move). -/
theorem ptRec_noLaunch (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {n : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n = none)
    (hpt : PtRec (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n))
    (hleft : NoLeftMove κ b jumps θ D n) :
    PtRec (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)) := by
  have hmove := walkMovesRight_of_ptRec D hpt hleft
  rcases run_succ_cases_of_noLaunch (κ := κ) (b := b) (jumps := jumps) (boundaryWalkSpec b jumps θ true) D hl with
    e | e | ⟨r, w, m, e⟩ | ⟨r, e⟩
  · rw [e]; exact hpt
  · rw [e]; exact Or.inr (Or.inl (stStatus_setDead _))
  · obtain ⟨hr, hw⟩ := hmove r w m e
    subst hr
    refine Or.inr (Or.inr ?_)
    rw [e, stPt_moveAlong, GW1W.stRecR_moveAlong_true, max_eq_right hw.le]
  · rw [e]; exact Or.inl (stStatus_moveToEnd'' _ _)

/-- A walk state that launches at step `n` has neither finished nor died. -/
theorem not_terminal_of_launch (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {n : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n ≠ none) :
    stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) ≠ stDone ∧
      stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) ≠ stDead := by
  have h0 := launches_run_of_le (κ := κ) (b := b) (jumps := jumps) (boundaryWalkSpec b jumps θ true) D
    (le_refl n)
  constructor <;> intro hs <;>
  rcases run_succ_walk_cases (κ := κ) (b := b) (jumps := jumps) (θ := θ) D n with e | e | e <;> rw [e] at hl
  · exact hl h0
  · rw [flowStep_of_done hs] at hl; exact hl h0
  · rw [contStep_of_done' hs] at hl; exact hl h0
  · exact hl h0
  · rw [flowStep_of_dead hs] at hl; exact hl h0
  · rw [launches_contStep] at hl; exact hl h0

/-- At a zero stop every real point with a nonzero chart point is alive. -/
theorem lAlive_of_zero {c : Chart} {d : (ℝ≥0 → ℝ) × ℝ≥0∞} (hd0 : d.1 0 = 0) (h0 : d.2 = 0) {z : ℂ}
    (hz : c.1 z ≠ 0) : lAlive c ⊤ d z := by
  have hT : stopTime ⊤ d = 0 := by simp [stopTime, h0]
  have hW0 : stopDrv ⊤ d 0 = 0 := by simp [stopDrv, retOf, h0, hd0]
  refine ⟨fun _ => c.1 z, ?_⟩
  rw [hT]
  refine ⟨continuousOn_const, fun t ht => ?_⟩
  have ht0 : t = 0 := le_antisymm ht.2 ht.1
  subst ht0
  refine ⟨hz, ?_⟩
  simp [hW0]

/-- **A launch with a finite lifetime keeps `PtRec`** (no left hit; `RecInv` for the zero lifetime). -/
theorem ptRec_launch {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D) {n : ℕ} {c : Chart} {θ' : ℝ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n = some (c, θ'))
    (hfin : (D n).2 ≠ ⊤) (hpt : PtRec (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n))
    (hok : RecInv κ b jumps θ D n) (hleft : NoLeftHit κ b jumps θ D n) :
    PtRec (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)) := by
  set spec := boundaryWalkSpec b jumps θ true with hspec
  set s₀ := ExplState.run κ b jumps spec D n with hs₀
  have hlne : (ExplState.run κ b jumps spec D (n + 1)).2.2.2.1 n ≠ none := by rw [hl]; simp
  have hPR := pieceRegular_of_launch hP hlne
  obtain ⟨hnd, hnd'⟩ := not_terminal_of_launch D hlne
  have hpr : stPt s₀ = stRecR s₀ := by
    rcases hpt with h | h | h
    · exact absurd h hnd
    · exact absurd h hnd'
    · exact h
  obtain ⟨-, he, -⟩ := eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) spec D hl
  rw [Lx.instrTime_boundaryWalk_of_launch hl] at he
  have hmin : min (⊤ : ℝ≥0∞) (D n).2 ≠ ⊤ := by rw [min_eq_right le_top]; exact hfin
  obtain ⟨-, -, hrec, -, hst, hptl⟩ := launch_eq_of_ne_top s₀ n (D n) θ' ⊤ hmin
  have hleft' : ¬ ∃ x : ℝ, x < stRecL s₀ ∧ lHit (stChart s₀) ⊤ (D n) x := hleft hlne
  unfold PtRec
  rw [he, hst, hptl, hrec]
  have hnlt : ¬ (⊤ : ℝ≥0∞) < (D n).2 := not_lt.2 le_top
  by_cases h0 : (D n).2 = 0
  · -- nothing beyond the record is swallowed at a zero stop
    refine Or.inr (Or.inr ?_)
    have hptl0 : lPt s₀ ⊤ (D n) = stPt s₀ := by simp only [lPt, h0, ↓reduceIte, ite_self]
    rw [hptl0, hpr]
    have hempty : {x : ℝ | stRecR s₀ < x ∧ ¬ lAlive (stChart s₀) ⊤ (D n) x} = ∅ := by
      ext x
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and, not_not]
      intro hx
      exact lAlive_of_zero hPR.1 h0 (hok x hx).2.2.2
    unfold lRecR
    rw [hempty, insert_empty_eq, csSup_singleton]
  · by_cases hR : ∃ x : ℝ, stRecR s₀ < x ∧ lHit (stChart s₀) ⊤ (D n) x
    · refine Or.inr (Or.inr ?_)
      simp only [lPt, hnlt, h0, hR, ↓reduceIte]
    · refine Or.inr (Or.inl ?_)
      simp only [lStatus, hnlt, h0, hR, hleft', ↓reduceIte]

/-- **The record invariant and `PtRec` along the walk** (finite launched lifetimes, no left move, no left hit). -/
theorem recInv_ptRec_run {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hfin : ∀ j, (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (j + 1)).2.2.2.1 j ≠ none →
      (D j).2 ≠ ⊤)
    (hlm : ∀ j, NoLeftMove κ b jumps θ D j) (hlh : ∀ j, NoLeftHit κ b jumps θ D j) :
    ∀ n, RecInv κ b jumps θ D n ∧ PtRec (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n)
  | 0 => by
    refine ⟨recInv_zero D, Or.inr (Or.inr ?_)⟩
    simp [ExplState.run, ExplState.init, boundaryWalkSpec]
  | n + 1 => by
    obtain ⟨hrec, hpt⟩ := recInv_ptRec_run hP hfin hlm hlh n
    rcases hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n with _ | ⟨c, θ'⟩
    · exact ⟨recInv_noLaunch hP hl (walkMovesRight_of_ptRec D hpt (hlm n)) hrec, ptRec_noLaunch D hl hpt (hlm n)⟩
    · have hf := hfin n (by rw [hl]; simp)
      exact ⟨recInv_launch hP hl hf hrec, ptRec_launch hP hl hf hpt hrec (hlh n)⟩

/-- **`WalkMovesRight` along the walk** (finite launched lifetimes, no left move, no left hit). -/
theorem walkMovesRight_run {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hfin : ∀ j, (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (j + 1)).2.2.2.1 j ≠ none →
      (D j).2 ≠ ⊤)
    (hlm : ∀ j, NoLeftMove κ b jumps θ D j) (hlh : ∀ j, NoLeftHit κ b jumps θ D j) (n : ℕ) :
    WalkMovesRight κ b jumps θ D n :=
  walkMovesRight_of_ptRec D (recInv_ptRec_run hP hfin hlm hlh n).2 (hlm n)

end InteractingSLE.Theorem14.SB.Lk
