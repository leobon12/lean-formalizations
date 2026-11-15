/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2XyLen
import InteractingSLE.Spec.Supplement.SB2XyTr

/-!
# The run inputs `RunInputs''` at the offset `relOff`, from the piece lifts (one sample)

Packet PROVE-T14-SB2LIFT (round 28; LIFTSET's item 4). **`runInputs_of_lifts`**: at one sample, from the actual
walk's facts (regular launches, chain facts, no left moves or hits, finished at the end of its program), the start at
`relOff` (an arc start, or a piece start with a finite start piece), the piece lifts `PiecesLift`, the per-stage facts
`StageFactsAll` of the relative family, the good-time density at the later actual stages, the upper chart and the tail
lift curve: there is `N` with `RunInputs'' … relOff N`, every field proved —

* `fin₁`, `two_le`, `len₁`, `done`, the actual part of `len`: the first finished stage `M = N + relOff` (the walk is not
  finished at `relOff + 1`: `notDone_of_arcStart`, `notDone_of_pieceStart`);
* `len₂` and the relative part of `len`: the count `first_done_le` (`len_rel`), with the statuses after the start
  (`flowSt_of_start`, `contSt_of_start`) and the first record (`q0_of_start`);
* `reg₂` (`regLaunches_of_facts`), `piece` (`piece_of_lifts`), `trLift` (`trLift_of_facts`, with the relative
  positivity `relPos_of_lifts`), `cont` (the ray correspondence).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Mn

open Exist Exist.Staged Exist.StagedLaw Lk LuM GW1W GW1Bookkeep
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

variable {κ θ : ℝ} {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} {R : ℝ} {ι : ℝ → ℝ} {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0}
  {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {o : ℕ}

/-- Away from stage `0` the stage shift is `0`. -/
theorem shiftD_of_ne {j : ℕ} (hj : j ≠ 0) : shiftD κ θ b₁ J₁ R D₁ j = 0 := by
  unfold shiftD; simp only [hj, ↓reduceIte]

/-- At an arc start the walk is not finished before its connector (the connector appends an arc). -/
theorem notDone_of_arcStart (hA : ArcStart κ θ b₁ J₁ R D₁ D₂ β₀ tL o) :
    stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)) ≠ stDone := by
  intro hd
  have h := hA.move
  rw [contStep_of_done' hd] at h
  split_ifs at h with hC
  · have := congrArg (fun s : ExplState => s.2.1.length) h
    simp only [arcs_length_moveAlong] at this
    omega
  · have := congrArg (fun s : ExplState => s.2.1.length) h
    simp only [arcs_moveToEnd_append, List.length_append, List.length_singleton] at this
    omega

/-- At a piece start with a finite start piece the walk is not finished after the start launch. -/
theorem notDone_of_pieceStart (hPV : PieceStartV κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL o) (hfin : (D₁ o).2 ≠ ⊤) :
    stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)) ≠ stDone := by
  rw [hPV.launch, (launch_eq_of_ne_top _ o (D₁ o) θ ⊤ (min_top_ne_top hfin)).2.2.2.2.1]
  unfold lStatus
  split_ifs <;> first | (intro h; cases h) | (intro h; split at h <;> cases h)

/-- **The connector statuses after the start.** -/
theorem contSt_of_start {N : ℕ} (hP₁ : RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁)
    (hlm₁ : ∀ j, NoLeftMove κ b₁ J₁ θ D₁ j) (hlh₁ : ∀ j, NoLeftHit κ b₁ J₁ θ D₁ j)
    (hfin₁ : ∀ j, j + 1 < N + o →
      (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + 1)).2.2.2.1 j ≠ none → (D₁ j).2 ≠ ⊤)
    (hN₁ : N + o ≤ (boundaryWalkSpec b₁ J₁ θ true).2.2.length) (ho : o % 2 = 0)
    (hnz : ∀ k, 2 + o ≤ k →
      (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (k + 1)).2.2.2.1 k ≠ none → (D₁ k).2 ≠ 0)
    (hS : ArcStart κ θ b₁ J₁ R D₁ D₂ β₀ tL o ∨
      (PieceStartV κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL o ∧ (D₁ o).2 ≠ ⊤)) :
    ∀ k, 2 + o ≤ k → k ≤ N + o → k % 2 = 1 →
      ContSt R (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k) := by
  intro k hk1 hk2 hodd
  rcases flowSt_two_of_start hP₁ hlm₁ hlh₁ (fun j hj => hfin₁ j (by omega)) hS with hd | ⟨hs₀, hp₀⟩
  · exact Or.inr (Or.inr (Or.inl (done_of_le hd hk1)))
  · exact (status_run_le hP₁ (2 + o) (N + o) hfin₁ hlm₁ hlh₁ hN₁ (by omega) hnz hp₀ hs₀ k hk1 hk2).2.2 hodd

/-- **The first record after the start** is a jump point right of `R` (unless the walk is finished). -/
theorem q0_of_start {M : ℕ} (hM : stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ M) = stDone)
    (hoM : o + 1 ≤ M) (hP₁ : RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁)
    (hlm₁ : ∀ j, NoLeftMove κ b₁ J₁ θ D₁ j) (hlh₁ : ∀ j, NoLeftHit κ b₁ J₁ θ D₁ j)
    (hfin₁ : ∀ j, j < o + 1 →
      (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + 1)).2.2.2.1 j ≠ none → (D₁ j).2 ≠ ⊤)
    (hS : ArcStart κ θ b₁ J₁ R D₁ D₂ β₀ tL o ∨
      (PieceStartV κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL o ∧ (D₁ o).2 ≠ ⊤)) :
    stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 2)) ≠ stDone →
      stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 2)) ∈ jumpSet b₁ J₁ ∧
        R < stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 2)) := by
  intro hnd
  rcases hS with hA | ⟨hPV, hfin⟩
  · have e := GW1W.run_succ_walk_cont (κ := κ) (b := b₁) (jumps := J₁) (θ := θ) (right := true) (D := D₁)
      hA.len (by have := hA.even; omega)
    rw [hA.move] at e
    rw [show o + 2 = o + 1 + 1 by omega] at hnd ⊢
    split_ifs at e with hC
    · have hw := Finset.mem_filter.1 ((GW1W.restartSet κ b₁ J₁
        (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1))).min'_mem hC)
      have hRw := hA.gap _ ((GW1W.restartSet κ b₁ J₁
        (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1))).min'_mem hC)
      rw [e, stRecR_moveAlong_true, max_eq_right (hA.recLe.trans hRw.le)]
      exact ⟨hw.1, hRw⟩
    · exact absurd (by rw [e]; exact stStatus_moveToEnd'' _ _) hnd
  · have hlne : (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)).2.2.2.1 o ≠ none := by
      rw [hPV.launch, launches_launch, Function.update_self]; simp
    have hc1 := contSt_after_launch R hPV.launch (hPV.nz₁ o le_rfl hlne) (hlh₁ o)
    have hne : stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)) ≠ GW1W.stArcM true := by
      rw [hPV.launch]; exact stStatus_launch_ne_arcM _ _ _ _
    obtain ⟨-, hpt1⟩ := recInv_ptRec_run_le hP₁ (N := o + 1) hfin₁ hlm₁ hlh₁ (o + 1) le_rfl
    have hW := walkMovesRight_of_ptRec D₁ hpt1 (hlm₁ (o + 1))
    have hRrec := hPV.recAfter hfin
    rw [show o + 2 = o + 1 + 1 by omega] at hnd ⊢
    rcases hc1 with hthr | ⟨h, -⟩ | h | h
    · rcases cont_round hPV.len.1 (by have := hPV.even; omega) hthr hW with h1 | ⟨h1, h2⟩
      · exact absurd h1 hnd
      · exact ⟨h1, lt_of_le_of_lt hRrec h2⟩
    · exact absurd h hne
    · exact absurd (done_of_le h (Nat.le_succ _)) hnd
    · have := dead_persist h M hoM
      rw [hM] at this; cases this

/-- **The run inputs at `relOff` from the piece lifts** (one sample), every field proved. -/
theorem runInputs_of_lifts (hι : RayCorr b₁ J₁ b₂ J₂ R ι) (hcont : ContinuousOn ι (Ici R))
    (hP₁ : RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁) (hW₁ : WalkChainFacts κ b₁ J₁ θ D₁)
    (hlm₁ : ∀ j, NoLeftMove κ b₁ J₁ θ D₁ j) (hlh₁ : ∀ j, NoLeftHit κ b₁ J₁ θ D₁ j)
    (hdoneL : stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁
      (boundaryWalkSpec b₁ J₁ θ true).2.2.length) = stDone)
    (hS : ArcStart κ θ b₁ J₁ R D₁ D₂ β₀ tL (relOff κ θ b₁ J₁ R D₁) ∨
      (PieceStartV κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL (relOff κ θ b₁ J₁ R D₁) ∧
        (D₁ (relOff κ θ b₁ J₁ R D₁)).2 ≠ ⊤))
    (hL : PiecesLift κ θ b₁ J₁ b₂ J₂ R D₁ D₂ β₀ γ tL) (hreg₂ : ∀ j, IsRegularDriver (D₂ j))
    {c : Chart} {m : ℝ} {A : Set ℂ} (hfacts : StageFactsAll κ θ b₁ J₁ b₂ J₂ R c m A D₁ D₂)
    (hgd : ∀ i, 2 ≤ i →
      (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + relOff κ θ b₁ J₁ R D₁ + 1)).2.2.2.1
        (i + relOff κ θ b₁ J₁ R D₁) ≠ none →
      {t : ℝ≥0 | (t : ℝ≥0∞) < (D₁ (i + relOff κ θ b₁ J₁ R D₁)).2} ⊆
        closure (goodT c (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + relOff κ θ b₁ J₁ R D₁))
          (D₁ (i + relOff κ θ b₁ J₁ R D₁))))
    (hγ : IsTailLiftCurve c R m β₀ tL γ) (hU : UpperChartOK c) (hK : β₀ '' Icc 0 tL ⊆ hullK A)
    (hDom : c.2.1 '' H = H \ fillH A) (hβ : Supp9B.IsProperCurve β₀)
    (hβr : range β₀ = ExplState.physSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁)
    (hγp : Supp9B.IsProperCurve γ) :
    ∃ N, RunInputs'' κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL (relOff κ θ b₁ J₁ R D₁) N := by
  set o := relOff κ θ b₁ J₁ R D₁ with ho_def
  have ho : o % 2 = 0 := relOff_even κ θ b₁ J₁ R D₁
  have hnz : ∀ k, 2 + o ≤ k →
      (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (k + 1)).2.2.2.1 k ≠ none → (D₁ k).2 ≠ 0 := by
    rcases hS with hA | ⟨hPV, -⟩
    · exact hA.nz₁
    · exact fun k hk => hPV.nz₁ k (by omega)
  have hnd : stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)) ≠ stDone := by
    rcases hS with hA | ⟨hPV, hfin⟩
    · exact notDone_of_arcStart hA
    · exact notDone_of_pieceStart hPV hfin
  obtain ⟨M, hM, hmin⟩ := exists_first_done (κ := κ) (b := b₁) (jumps := J₁) (θ := θ) (D := D₁) ⟨_, hdoneL⟩
  have hML : M ≤ (boundaryWalkSpec b₁ J₁ θ true).2.2.length := by
    by_contra h; push Not at h; exact hmin _ h hdoneL
  have hoM : o + 1 < M := by
    by_contra h; push Not at h; exact hnd (done_of_le hM h)
  set N := M - o with hN
  have hNM : N + o = M := by omega
  have hfin₁ : ∀ j, j + 1 < N + o →
      (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + 1)).2.2.2.1 j ≠ none → (D₁ j).2 ≠ ⊤ :=
    fun j hj hl => fin_before_first_done hmin j (by omega) hl
  have hN₁ : N + o ≤ (boundaryWalkSpec b₁ J₁ θ true).2.2.length := by omega
  have h2N : 2 ≤ N := by omega
  have hflow := flowSt_of_start hP₁ hlm₁ hlh₁ hfin₁ hN₁ h2N ho hnz hS
  have hcontS := contSt_of_start hP₁ hlm₁ hlh₁ hfin₁ hN₁ ho hnz hS
  have hrp := recInv_ptRec_run_le hP₁ (N := M - 1) (fun j hj hl => fin_before_first_done hmin j (by omega) hl)
    hlm₁ hlh₁
  have hrec : ∀ k, k < M → RecInv κ b₁ J₁ θ D₁ k := fun k hk => (hrp k (by omega)).1
  have hWall : ∀ k, k < M → WalkMovesRight κ b₁ J₁ θ D₁ k := fun k hk =>
    walkMovesRight_of_ptRec D₁ (hrp k (by omega)).2 (hlm₁ k)
  have hq0 := q0_of_start hM hoM.le hP₁ hlm₁ hlh₁ (fun j hj hl => fin_before_first_done hmin j (by omega) hl) hS
  have hcount := first_done_le hP₁ hrec hWall hM hmin hML ho
    (fun k h1 h2 h3 => hflow k (by omega) (by omega) h3) (fun k h1 h2 h3 => hcontS k (by omega) (by omega) h3) hq0
  have hlen₂ : N ≤ (boundaryWalkSpec b₂ J₂ θ true).2.2.length := len_rel hι (o := o) (by omega)
  refine ⟨N, ⟨hcont, ?_, hfin₁, ?_, ?_, h2N, ?_, hN₁, hlen₂, by rw [hNM]; exact hM⟩⟩
  · exact regLaunches_of_facts hreg₂ (fun j hl hz => (hfacts j hl hz).1.2.2.2.2.2.2)
  · exact piece_of_lifts hL (fun i hi hiN => by omega)
  · intro i hi hiN hl₁ hl₂ hfin
    have hev : i % 2 = 0 := (GW1W.even_of_launches_walk hl₂).1
    have hpos₁ := hnz (i + o) (by omega) hl₁
    have hF := hflow (i + o) (by omega) (by omega) (by omega)
    have hz₂ := relPos_of_lifts hL hi hev (by omega) hF hl₁ hpos₁ hP₁ hW₁ (hgd i hi hl₁) hβr hK hDom hγp.2.1
    have hSF := (hfacts i hl₂ hz₂).1
    rw [shiftD_of_ne (by omega)] at hSF
    exact trLift_of_facts hγ hβ hU hK hDom hβr hP₁ hl₁ hfin hpos₁ hSF
  · intro i hi hiN
    exact ⟨by omega, by omega⟩

end InteractingSLE.Theorem14.SB.Mn
