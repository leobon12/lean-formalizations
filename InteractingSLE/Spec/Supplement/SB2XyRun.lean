/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2XyPos
import InteractingSLE.Spec.Supplement.SB2XwAS

/-!
# The run inputs' relative fields at one sample: statuses, lifts, positivity, `piece`, `reg₂`, `trLift`

Packet PROVE-T14-SB2LIFT (round 28; LIFTSET's item 4). At one sample, with the actual walk's start data at the offset
`o = relOff` and the piece lifts `PiecesLift`:

* **`flowSt_two_of_start`**, **`flowSt_of_start`**: at every flow stage after the start, the actual walk is at a mark
  right of `R` or finished (`FlowSt R`), by the status bookkeeping `status_run_le` from the start;
* **`arcM_of_flowSt_launch`**: a launch at such a stage is from an arc mark with an admissible seed;
* **`liftRel_of_lifts`**, **`relPos_of_lifts`**: there the relative piece is the lift of the actual one, and has
  positive lifetime (`pos_of_liftRel`, zero lifetime together);
* **`piece_of_lifts`**, **`regLaunches_of_facts`**, **`trLift_of_facts`**: the fields `piece`, `reg₂`, `trLift` of
  `RunInputs''` (`trLift_concrete` from the per-stage facts).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.SB.Mn

open Exist Exist.Staged Exist.StagedLaw Lk LuM GW1W GW1Bookkeep Sec7.PocketTraversal Sec7.Lemma71C
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

variable {κ θ : ℝ} {b₁ b₂ : ℝ → ℝ} {J₁ J₂ : Finset ℝ} {R : ℝ} {ι : ℝ → ℝ} {β₀ γ : ℝ≥0 → ℂ} {tL : ℝ≥0}
  {D₁ D₂ : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {o N : ℕ}

/-- **The status two stages after the start**: finished, or at a mark right of `R` with record right of `R`. -/
theorem flowSt_two_of_start (hP₁ : RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁)
    (hlm₁ : ∀ j, NoLeftMove κ b₁ J₁ θ D₁ j) (hlh₁ : ∀ j, NoLeftHit κ b₁ J₁ θ D₁ j)
    (hfin₁ : ∀ j, j < o + 1 →
      (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + 1)).2.2.2.1 j ≠ none → (D₁ j).2 ≠ ⊤)
    (hS : ArcStart κ θ b₁ J₁ R D₁ D₂ β₀ tL o ∨
      (PieceStartV κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL o ∧ (D₁ o).2 ≠ ⊤)) :
    stStatus (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (2 + o)) = stDone ∨
      (FlowSt R (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (2 + o)) ∧
        R ≤ stRecR (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (2 + o))) := by
  rcases hS with hA | ⟨hPV, hfin⟩
  · exact flowSt_after_arc hA.len hA.even hA.move hA.gap
  · have hlne : (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (o + 1)).2.2.2.1 o ≠ none := by
      rw [hPV.launch, launches_launch, Function.update_self]; simp
    have hc1 := contSt_after_launch R hPV.launch (hPV.nz₁ o le_rfl hlne) (hlh₁ o)
    obtain ⟨hinv1, hpt1⟩ := recInv_ptRec_run_le hP₁ (N := o + 1) hfin₁ hlm₁ hlh₁ (o + 1) le_rfl
    have hlen1 : o + 1 < (boundaryWalkSpec b₁ J₁ θ true).2.2.length := hPV.len.1
    have hRrec := hPV.recAfter hfin
    have hev := hPV.even
    refine Or.inr ⟨?_, ?_⟩
    · rw [show 2 + o = o + 1 + 1 by omega]
      exact flowSt_of_contSt hlen1 (by omega) hpt1 hRrec hc1
    · rw [show 2 + o = o + 1 + 1 by omega]
      exact hRrec.trans (stRecR_run_le_succ' hP₁ hinv1)

/-- **The status at every flow stage after the start, up to the end of the lockstep.** -/
theorem flowSt_of_start (hP₁ : RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁)
    (hlm₁ : ∀ j, NoLeftMove κ b₁ J₁ θ D₁ j) (hlh₁ : ∀ j, NoLeftHit κ b₁ J₁ θ D₁ j)
    (hfin₁ : ∀ j, j + 1 < N + o →
      (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (j + 1)).2.2.2.1 j ≠ none → (D₁ j).2 ≠ ⊤)
    (hN₁ : N + o ≤ (boundaryWalkSpec b₁ J₁ θ true).2.2.length) (h2N : 2 ≤ N) (ho : o % 2 = 0)
    (hnz : ∀ k, 2 + o ≤ k →
      (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (k + 1)).2.2.2.1 k ≠ none → (D₁ k).2 ≠ 0)
    (hS : ArcStart κ θ b₁ J₁ R D₁ D₂ β₀ tL o ∨
      (PieceStartV κ θ b₁ J₁ b₂ J₂ R ι D₁ D₂ β₀ γ tL o ∧ (D₁ o).2 ≠ ⊤)) :
    ∀ k, 2 + o ≤ k → k ≤ N + o → k % 2 = 0 →
      FlowSt R (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ k) := by
  intro k hk1 hk2 hev
  rcases flowSt_two_of_start hP₁ hlm₁ hlh₁ (fun j hj => hfin₁ j (by omega)) hS with hd | ⟨hs₀, hp₀⟩
  · exact Or.inr (Or.inl (done_of_le hd hk1))
  · exact (status_run_le hP₁ (2 + o) (N + o) hfin₁ hlm₁ hlh₁ hN₁ (by omega) hnz hp₀ hs₀ k hk1 hk2).2.1 hev

/-- **A launch at a flow stage of status `FlowSt` is from an arc mark with an admissible seed.** -/
theorem arcM_of_flowSt_launch {b : ℝ → ℝ} {J : Finset ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞} {k : ℕ} {p : ℝ}
    (hk : k < (boundaryWalkSpec b J θ true).2.2.length) (hev : k % 2 = 0)
    (hF : FlowSt p (ExplState.run κ b J (boundaryWalkSpec b J θ true) D k))
    (hl : (ExplState.run κ b J (boundaryWalkSpec b J θ true) D (k + 1)).2.2.2.1 k ≠ none) :
    stStatus (ExplState.run κ b J (boundaryWalkSpec b J θ true) D k) = GW1W.stArcM true ∧
      ExplState.IsAdmissibleSeed κ (leftLim b (stPt (ExplState.run κ b J (boundaryWalkSpec b J θ true) D k)))
        (rightLim b (stPt (ExplState.run κ b J (boundaryWalkSpec b J θ true) D k))) θ := by
  obtain ⟨⟨c, θ'⟩, hl'⟩ := Option.ne_none_iff_exists'.1 hl
  have hst : stStatus (ExplState.run κ b J (boundaryWalkSpec b J θ true) D k) = GW1W.stArcM true := by
    rcases hF with ⟨h, -⟩ | h | h
    · exact h
    · exact absurd h (WalkIntRunChron.not_done_of_launch _ D hl')
    · exfalso
      apply hl
      rw [GW1W.run_succ_walk_flow (κ := κ) (b := b) (jumps := J) (θ := θ) (right := true) (D := D) hk hev,
        flowStep_of_dead h]
      exact launches_run_of_le _ D le_rfl
  exact ⟨hst, admissible_of_launched_arcM hk hev hst hl⟩

/-- **The relative piece is the lift of the actual one** at a later launching stage (the piece lifts). -/
theorem liftRel_of_lifts (hL : PiecesLift κ θ b₁ J₁ b₂ J₂ R D₁ D₂ β₀ γ tL) {i : ℕ} (hi : 2 ≤ i) (hev : i % 2 = 0)
    (hk : i + relOff κ θ b₁ J₁ R D₁ < (boundaryWalkSpec b₁ J₁ θ true).2.2.length)
    (hF : FlowSt R (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + relOff κ θ b₁ J₁ R D₁)))
    (hl : (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + relOff κ θ b₁ J₁ R D₁ + 1)).2.2.2.1
      (i + relOff κ θ b₁ J₁ R D₁) ≠ none) :
    LiftRel β₀ tL γ (newPc (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + relOff κ θ b₁ J₁ R D₁))
        (D₁ (i + relOff κ θ b₁ J₁ R D₁)))
      (newPc (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i) (D₂ i)) := by
  have hev' : (i + relOff κ θ b₁ J₁ R D₁) % 2 = 0 := by
    have := relOff_even κ θ b₁ J₁ R D₁; omega
  obtain ⟨hst, hadm⟩ := arcM_of_flowSt_launch hk hev' hF hl
  exact hL i hi hl (decide_eq_true hev) hst hadm

/-- **Zero lifetime together at a later launching stage** (the relative lifetime is positive). -/
theorem relPos_of_lifts (hL : PiecesLift κ θ b₁ J₁ b₂ J₂ R D₁ D₂ β₀ γ tL) {i : ℕ} (hi : 2 ≤ i) (hev : i % 2 = 0)
    (hk : i + relOff κ θ b₁ J₁ R D₁ < (boundaryWalkSpec b₁ J₁ θ true).2.2.length)
    (hF : FlowSt R (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + relOff κ θ b₁ J₁ R D₁)))
    (hl : (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + relOff κ θ b₁ J₁ R D₁ + 1)).2.2.2.1
      (i + relOff κ θ b₁ J₁ R D₁) ≠ none)
    (hpos : (D₁ (i + relOff κ θ b₁ J₁ R D₁)).2 ≠ 0)
    (hP₁ : RegLaunches κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁) (hW₁ : WalkChainFacts κ b₁ J₁ θ D₁)
    {c : Chart} {A : Set ℂ}
    (hgd : {t : ℝ≥0 | (t : ℝ≥0∞) < (D₁ (i + relOff κ θ b₁ J₁ R D₁)).2} ⊆
      closure (goodT c (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + relOff κ θ b₁ J₁ R D₁))
        (D₁ (i + relOff κ θ b₁ J₁ R D₁))))
    (hβr : range β₀ = ExplState.physSet κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁)
    (hK : β₀ '' Icc 0 tL ⊆ hullK A) (hDom : c.2.1 '' H = H \ fillH A) (hγ : Function.Injective γ) :
    (D₂ i).2 ≠ 0 :=
  pos_of_liftRel hP₁ hW₁ hl hpos hgd hβr hK hDom hγ (liftRel_of_lifts hL hi hev hk hF hl)

/-- **The field `piece` of the run inputs** from the piece lifts. -/
theorem piece_of_lifts (hL : PiecesLift κ θ b₁ J₁ b₂ J₂ R D₁ D₂ β₀ γ tL)
    (hlen : ∀ i, 2 ≤ i → i < N →
      i + relOff κ θ b₁ J₁ R D₁ < (boundaryWalkSpec b₁ J₁ θ true).2.2.length) :
    ∀ i, 2 ≤ i → i < N →
      StepPiece κ θ b₁ (LiftRel β₀ tL γ) (i % 2 = 0)
        (ExplState.run κ b₁ J₁ (boundaryWalkSpec b₁ J₁ θ true) D₁ (i + relOff κ θ b₁ J₁ R D₁))
        (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ i) (D₁ (i + relOff κ θ b₁ J₁ R D₁)) (D₂ i) := by
  intro i hi hiN hflow hst hadm
  have hev : i % 2 = 0 := of_decide_eq_true hflow
  have hev' : (i + relOff κ θ b₁ J₁ R D₁) % 2 = 0 := by
    have := relOff_even κ θ b₁ J₁ R D₁; omega
  have hl := launched_of_admissible (hlen i hi hiN) hev' hst hadm
  exact hL i hi (by rw [hl]; simp) hflow hst hadm

/-- A regular driver of lifetime `0` is a regular piece. -/
theorem pieceRegular_of_zero {e : Drv} (hr : IsRegularDriver e) (h0 : e.2 = 0) : GW1P.PieceRegular e.1 e.2 := by
  refine ⟨hr.2.1, ?_, fun _ => 0, ⟨rfl, continuousOn_const, fun t ht => ?_⟩, fun h => ?_⟩
  · refine (Set.Subsingleton.continuousOn ?_ _)
    intro x hx y hy
    have hx0 : (x : ℝ≥0∞) = 0 := le_antisymm (h0 ▸ hx) bot_le
    have hy0 : (y : ℝ≥0∞) = 0 := le_antisymm (h0 ▸ hy) bot_le
    exact_mod_cast hx0.trans hy0.symm
  · rw [h0] at ht; exact absurd ht (not_lt.2 bot_le)
  · rw [h0] at h; exact absurd h ENNReal.zero_ne_top

/-- **The field `reg₂` of the run inputs**: relative launches are regular (positive ones by the per-stage facts). -/
theorem regLaunches_of_facts (hreg₂ : ∀ j, IsRegularDriver (D₂ j))
    (hpr : ∀ j, (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (j + 1)).2.2.2.1 j ≠ none →
      (D₂ j).2 ≠ 0 → GW1P.PieceRegular (D₂ j).1 (D₂ j).2) :
    RegLaunches κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ := by
  intro k c θ' hl
  have hl' : (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D₂ (k + 1)).2.2.2.1 k ≠ none := by
    rw [hl]; simp
  rw [GW1W.instrTime_walk hl', min_eq_right le_top]
  by_cases h0 : (D₂ k).2 = 0
  · exact pieceRegular_of_zero (hreg₂ k) h0
  · exact hpr k hl' h0

end InteractingSLE.Theorem14.SB.Mn
