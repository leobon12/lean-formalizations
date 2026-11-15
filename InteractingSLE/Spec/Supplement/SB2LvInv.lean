/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LvStep

/-!
# The record invariants of a walk run

Packet PROVE-T14-SB2LIFT (round 11; item 2 of handoff §R9.2). The physical aliveness criterion `lAlive_run_iff`
needs `BeyondOK` at the points it is applied to. Here it is proved at **every point beyond the current right
record**, by induction over a right boundary-walk run with regular launches, as long as every launched piece has a
finite lifetime:

* **`RecInv n`**: `BeyondOK … n x` for every `x > stRecR (run n)`;
* `recInv_zero`: at the root (record `0`) every point `x > 0` qualifies;
* **`recInv_launch`**: a launch with a finite lifetime keeps the invariant, with no further input.
  - The record does not decrease, and points beyond the new record were left alive and are off the new closed fill
    (`beyond_launch_step`).
  - The boundary limits persist (`GW1WalkExit.exteriorInverse_launch`, with `isRealChart_run`).
  - The new chart point is the nonzero value of the forward flow;
* **`recInv_noLaunch`**: a step without a launch keeps the invariant if it moves only to the right beyond the record
  (`WalkMovesRight`). The chart is recentred (`tendsto_recenter`), the filled prefix is unchanged (connectors are
  real), and the chart points of two points beyond the record differ because their boundary values differ;
* **`recInv_run`**: the invariant at every stage up to `N`.

The named input is **`WalkMovesRight`**: every boundary move of the walk goes to the right, to a point beyond the
current record. It holds for the right walk under SB2(2)'s regime: no left hits, connectors start at the record, and
marks lie beyond it.
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

/-- **The record invariant at stage `n`**: `BeyondOK` at every point beyond the right record. -/
def RecInv (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (θ : ℝ) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (n : ℕ) : Prop :=
  ∀ x : ℝ, stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) < x → BeyondOK κ b jumps θ true D n x

/-- **Named input: the walk moves only to the right, beyond the record.** -/
def WalkMovesRight (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) (θ : ℝ) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (n : ℕ) : Prop :=
  ∀ (r : Bool) (w : ℝ) (m : Bool), ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1) =
    ExplState.moveAlong (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) r w m →
    r = true ∧ stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) < w

theorem recInv_zero (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) : RecInv κ b jumps θ D 0 := by
  have hs : ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D 0 = ExplState.init 0 := by
    simp [ExplState.run, boundaryWalkSpec]
  intro x hx
  rw [hs] at hx
  have hx0 : (0 : ℝ) < x := hx
  refine ⟨fun j hj => absurd hj (Nat.not_lt_zero j), fun j hj => ?_, ?_, ?_⟩
  · rw [Nat.le_zero.1 hj]
    have h0 : fillH (SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D 0) = ∅ := by
      refine YuanCharacterisation.fillH_eq_empty_of_subset fun z hz => ?_
      have : SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D 0 = {(0 : ℂ)} := by
        simp [SB.prefixPhysSet, ExplState.run, ExplState.init, boundaryWalkSpec]
      rw [this, mem_singleton_iff] at hz
      rw [hz]
      simp
    rw [h0, closure_empty]
    exact notMem_empty _
  · rw [hs]
    have hc : Continuous fun z : ℂ => z + ((0 : ℝ) : ℂ) := continuous_id.add continuous_const
    simpa [ExplState.init, Chart.id, Chart.recenter] using (hc.tendsto (x : ℂ)).mono_left nhdsWithin_le_nhds
  · rw [hs]
    simpa [ExplState.init, Chart.id, Chart.recenter] using hx0.ne'

/-- Some point beyond the record gives the finiteness of the earlier launched lifetimes. -/
theorem recInv_fin {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {n : ℕ} (hok : RecInv κ b jumps θ D n) :
    ∀ j < n, (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (j + 1)).2.2.2.1 j ≠ none →
      (D j).2 ≠ ⊤ := fun j hj hl =>
  ((hok _ (lt_add_one _)).1 j hj hl).1

/-- **The launch step of the record invariant.** -/
theorem beyond_launch_step {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D) {n : ℕ} {c : Chart} {θ' : ℝ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n = some (c, θ'))
    (hfin : (D n).2 ≠ ⊤) (hok : RecInv κ b jumps θ D n) :
    stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n) ≤
      stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)) ∧
    ∀ x : ℝ, stRecR (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)) < x →
      lAlive (stChart (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D n)) ⊤ (D n) x ∧
      (x : ℂ) ∉ closure (fillH (SB.prefixPhysSet κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1))) := by
  set spec := boundaryWalkSpec b jumps θ true with hspec
  set s₀ := ExplState.run κ b jumps spec D n with hs₀
  obtain ⟨-, he, -⟩ := eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) spec D hl
  rw [Lx.instrTime_boundaryWalk_of_launch hl] at he
  have hmin : min (⊤ : ℝ≥0∞) (D n).2 ≠ ⊤ := by rw [min_eq_right le_top]; exact hfin
  have hrec : stRecR (ExplState.run κ b jumps spec D (n + 1)) = lRecR s₀ ⊤ (D n) := by
    rw [he]; exact (launch_eq_of_ne_top s₀ n (D n) θ' ⊤ hmin).2.2.1
  have hformula := lRecR_run_eq hP hl hfin hok
  -- the new fill is bounded
  have hfin'' : ∀ j < n + 1, (ExplState.run κ b jumps spec D (j + 1)).2.2.2.1 j ≠ none → (D j).2 ≠ ⊤ := by
    intro j hj hj'
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact recInv_fin hok j hj hj'
    · exact hfin
  obtain ⟨K, hKc, hKR, -⟩ := image_runChart_walk hP (n + 1) hfin''
  have hfill : fillH K = fillH (SB.prefixPhysSet κ b jumps spec D (n + 1)) := fillH_eq_of_union_im hKR
  obtain ⟨M, hM⟩ := ((isBounded_fillH hKc.isClosed hKc.isBounded).closure).subset_closedBall 0
  rw [hfill] at hM
  set S := {x : ℝ | stRecR s₀ < x ∧ (x : ℂ) ∈ closure (fillH (SB.prefixPhysSet κ b jumps spec D (n + 1)))}
    with hSdef
  have hSb : BddAbove S := ⟨M, fun x hx => by
    have h1 := hM hx.2
    rw [mem_closedBall_zero_iff, Complex.norm_real, Real.norm_eq_abs] at h1
    exact (le_abs_self x).trans h1⟩
  have hAb : BddAbove (insert (stRecR s₀) S) := hSb.insert _
  have hge : stRecR s₀ ≤ lRecR s₀ ⊤ (D n) := by
    rw [hformula]; exact le_csSup hAb (mem_insert _ _)
  refine ⟨hrec ▸ hge, fun x hx => ?_⟩
  rw [hrec] at hx
  have hx₀ : stRecR s₀ < x := lt_of_le_of_lt hge hx
  have hnot : (x : ℂ) ∉ closure (fillH (SB.prefixPhysSet κ b jumps spec D (n + 1))) := by
    intro hm
    have : x ≤ lRecR s₀ ⊤ (D n) := by rw [hformula]; exact le_csSup hAb (mem_insert_of_mem _ ⟨hx₀, hm⟩)
    exact absurd hx (not_lt.2 this)
  obtain ⟨h1, h2, h3, h4⟩ := hok x hx₀
  exact ⟨(lAlive_run_iff hP hl hfin x h1 h2 h3 h4).2 hnot, hnot⟩

/-- **A launch with a finite lifetime keeps the record invariant.** -/
theorem recInv_launch {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D) {n : ℕ} {c : Chart} {θ' : ℝ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n = some (c, θ'))
    (hfin : (D n).2 ≠ ⊤) (hok : RecInv κ b jumps θ D n) : RecInv κ b jumps θ D (n + 1) := by
  set spec := boundaryWalkSpec b jumps θ true with hspec
  set s₀ := ExplState.run κ b jumps spec D n with hs₀
  have hlne : (ExplState.run κ b jumps spec D (n + 1)).2.2.2.1 n ≠ none := by rw [hl]; simp
  have hPR := pieceRegular_of_launch hP hlne
  obtain ⟨-, he, -⟩ := eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) spec D hl
  rw [Lx.instrTime_boundaryWalk_of_launch hl] at he
  obtain ⟨hmono, hbeyond⟩ := beyond_launch_step hP hl hfin hok
  -- the exterior inverse after the launch
  have hext : GW1WalkExit.ExteriorInverse true s₀ := fun y hy => (hok y hy).2.2.1
  have hinv : GW1WalkExit.ExteriorInverse true (ExplState.launch s₀ n (D n) θ' ⊤) := by
    refine GW1WalkExit.exteriorInverse_launch hext (isRealChart_run spec D n) n θ' hPR hfin fun y hy => ?_
    have hy' : stRecR (ExplState.run κ b jumps spec D (n + 1)) < y := by rw [he]; exact hy
    exact ⟨lt_of_le_of_lt hmono hy', (hbeyond y hy').1⟩
  intro x hx
  have hx₀ : stRecR s₀ < x := lt_of_le_of_lt hmono hx
  obtain ⟨h1, h2, -, -⟩ := hok x hx₀
  obtain ⟨halive, hoff⟩ := hbeyond x hx
  refine ⟨fun j hj hj' => ?_, fun j hj => ?_, ?_, ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact h1 j hj hj'
    · exact ⟨hfin, halive⟩
  · rcases Nat.of_le_succ hj with hj | rfl
    · exact h2 j hj
    · exact hoff
  · have hx' : GW1WalkExit.outwardRecord true (ExplState.launch s₀ n (D n) θ' ⊤) < GW1WalkFinish.sideCoord true x := by
      simp only [GW1WalkExit.outwardRecord, GW1WalkFinish.sideCoord, ↓reduceIte]
      rw [← he]; exact hx
    have := hinv x hx'
    rw [he]; exact this
  · -- the chart point after the launch is the nonzero end value of the forward flow
    have hmin : min (⊤ : ℝ≥0∞) (D n).2 ≠ ⊤ := by rw [min_eq_right le_top]; exact hfin
    have hch := (launch_eq_of_ne_top s₀ n (D n) θ' ⊤ hmin).1
    obtain ⟨u, hu⟩ := halive
    have hWc : Continuous (stopDrv ⊤ (D n)) := by
      obtain ⟨hdrv, -, -⟩ := stopDrv_eq_and_isGeneratingTrace hPR hfin
      have h := hPR.continuous_stoppedReal.1
      rw [hdrv]
      simpa only [min_eq_right (le_top : (D n).2 ≤ ⊤)] using h
    have hT0 := stopTime_nonneg ⊤ (D n)
    show (stChart (ExplState.run κ b jumps spec D (n + 1))).1 x ≠ 0
    rw [he, hch]
    show fwdMap (stopDrv ⊤ (D n)) (stopTime ⊤ (D n)) ((stChart s₀).1 x) ≠ 0
    rw [fwdMap_eq_of_isForwardSol hWc hu ⟨hT0, le_rfl⟩]
    exact (hu.2 _ ⟨hT0, le_rfl⟩).1

/-- **A step without a launch keeps the record invariant** when the walk moves only to the right. -/
theorem recInv_noLaunch {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D) {n : ℕ}
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n = none)
    (hmove : WalkMovesRight κ b jumps θ D n) (hok : RecInv κ b jumps θ D n) : RecInv κ b jumps θ D (n + 1) := by
  set spec := boundaryWalkSpec b jumps θ true with hspec
  set s₀ := ExplState.run κ b jumps spec D n with hs₀
  have hmono := stRecR_run_succ_ge_of_noLaunch (κ := κ) (b := b) (jumps := jumps) spec D hl
  have hc := isRealChart_run (κ := κ) (b := b) (jumps := jumps) spec D n
  intro x hx
  have hx₀ : stRecR s₀ < x := lt_of_le_of_lt hmono hx
  obtain ⟨h1, h2, h3, h4⟩ := hok x hx₀
  -- the filled prefix does not change
  have hnp : newPiece κ b jumps θ true D n = ∅ := by
    ext z
    simp only [newPiece, mem_ofPred_eq, mem_empty_iff_false, iff_false, not_and]
    exact fun h => absurd hl h
  have hfillEq : fillH (SB.prefixPhysSet κ b jumps spec D (n + 1)) = fillH (SB.prefixPhysSet κ b jumps spec D n) := by
    refine fillH_eq_of_union_im ?_
    rw [prefixPhysSet_succ_walk hP n, hnp, union_empty, union_assoc]
    congr 1
    refine union_eq_right.2 ?_
    rintro _ ⟨y, -, rfl⟩
    simp
  refine ⟨fun j hj hj' => ?_, fun j hj => ?_, ?_, ?_⟩
  · rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact h1 j hj hj'
    · exact absurd hl hj'
  · rcases Nat.of_le_succ hj with hj | rfl
    · exact h2 j hj
    · rw [hfillEq]; exact h2 n le_rfl
  · obtain ⟨a, ha⟩ := chart_run_succ_of_noLaunch (κ := κ) (b := b) (jumps := jumps) spec D hl
    show Tendsto (ExplState.run κ b jumps spec D (n + 1)).2.2.2.2.1.2.1
      (𝓝[H] ((ExplState.run κ b jumps spec D (n + 1)).2.2.2.2.1.1 x)) (𝓝 (x : ℂ))
    rw [ha]
    exact tendsto_recenter h3 a
  · rcases run_succ_cases_of_noLaunch (κ := κ) (b := b) (jumps := jumps) spec D hl with e | e | ⟨r, w, m, e⟩ | ⟨r, e⟩
    · show (stChart (ExplState.run κ b jumps spec D (n + 1))).1 x ≠ 0
      rw [e]; exact h4
    · show (stChart (ExplState.run κ b jumps spec D (n + 1))).1 x ≠ 0
      rw [e, stChart_setDead]; exact h4
    · obtain ⟨hr, hw⟩ := hmove r w m e
      subst hr
      have hxw : w < x := by
        have := GW1W.stRecR_moveAlong_true s₀ w m
        rw [← e] at this
        rw [this] at hx
        exact lt_of_le_of_lt (le_max_right _ _) hx
      obtain ⟨-, -, hw3, -⟩ := hok w hw
      show (stChart (ExplState.run κ b jumps spec D (n + 1))).1 x ≠ 0
      rw [e, stChart_moveAlong']
      show (stChart s₀).1 x - (((stChart s₀).1 w).re : ℂ) ≠ 0
      intro h0
      have hyw : (stChart s₀).1 x = (stChart s₀).1 w := by
        rw [sub_eq_zero] at h0
        rw [h0]
        exact Complex.ext (by simp) (by rw [Complex.ofReal_im]; exact (hc w).symm)
      rw [hyw] at h3
      have : (𝓝[H] ((stChart s₀).1 w)).NeBot :=
        GW1P.neBot_nhdsWithin_H (show 0 ≤ ((stChart s₀).1 w).im by rw [hc w])
      exact hxw.ne (Complex.ofReal_injective (tendsto_nhds_unique hw3 h3))
    · show (stChart (ExplState.run κ b jumps spec D (n + 1))).1 x ≠ 0
      rw [e, stChart_moveToEnd']; exact h4

/-- **The record invariant along the run** (finite launched lifetimes; the walk moves only to the right). -/
theorem recInv_run {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} (hP : RegLaunches κ b jumps (boundaryWalkSpec b jumps θ true) D)
    (hfin : ∀ j, (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (j + 1)).2.2.2.1 j ≠ none →
      (D j).2 ≠ ⊤)
    (hmove : ∀ j, WalkMovesRight κ b jumps θ D j) : ∀ n, RecInv κ b jumps θ D n
  | 0 => recInv_zero D
  | n + 1 => by
    have ih := recInv_run hP hfin hmove n
    rcases hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ true) D (n + 1)).2.2.2.1 n with _ | ⟨c, θ'⟩
    · exact recInv_noLaunch hP hl (hmove n) ih
    · exact recInv_launch hP hl (hfin n (by rw [hl]; simp)) ih

end InteractingSLE.Theorem14.SB.Lk
