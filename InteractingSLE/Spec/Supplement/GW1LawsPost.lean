/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW1LawsRetarget
import InteractingSLE.Spec.Supplement.GW1ActiveRunL

/-!
# GW1's terminal restart: the stop word after a completed piece of a walk

Packet PROVE-GW1-LAWS (deterministic). After an ordinary piece of a boundary walk that is followed by another launch,
the piece is finite and ends either with zero lifetime or at a new outward record (`post_case_right`,
`post_case_left`). In both cases the post-piece state has an outward profile and the stop word is the original word
beyond the new record (`post_rProf_rOrig`, `post_lProf_lOrig`, assembled from PROVE-T14-GW1W's `rProf_launch`,
`rProf_launch_zero`, `rOrig_of_rel` and their mirrors). Hence the stop word satisfies both height bounds of the
counterflow lifetime criterion (`isCfGoodWord_stop_right`, `isCfGoodWord_stop_left`): the inward side by Lemma GW1's
(GW1.1) (`stopWord_fn_add_lt_of_neg`), the untouched outward ray by the ambient bound. This is the word computation of
BW1 (supplement p. 614, (BW1.2): "the whole conditional word is admissible") for the walks.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)

namespace InteractingSLE.Theorem14.GW1Laws

open Exist Exist.StagedLaw Exist.Staged Restart PiecewiseConstantBoundaryData GW1W

section Post

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {β : BoundaryWord} {s : ExplState} {k : ℕ}
  {D : (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **The right profile and the original stop word after a completed piece of the right walk.** -/
theorem post_rProf_rOrig (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hI : RInv κ θ b jumps β s) (hreg : IsRegularDriver D)
    (hgood : D.2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf ⊤ D))) (hfin : D.2 ≠ ⊤)
    (hcase : D.2 = 0 ∨ stStatus (ExplState.launch s k D θ ⊤) = stThr (some true)) :
    RProf (ExplState.launch s k D θ ⊤) ∧ ROrig b jumps (stopWord κ (β, θ, recOf ⊤ D)) (ExplState.launch s k D θ ⊤) := by
  rcases hcase with h0 | hthr
  · obtain ⟨hs₁, hrel⟩ := rProf_launch_zero hI.2.1 k θ hreg h0
    exact ⟨hs₁, rOrig_of_rel hκ hb hI.2.1 hI.2.2 θ ⟨hs₁, hrel⟩⟩
  · obtain ⟨-, hhit, -, -⟩ := launch_thr_true hfin hthr
    obtain ⟨hs₁, hrel⟩ := rProf_launch hI.2.1 k θ hreg (hgood hfin) hfin hhit
    exact ⟨hs₁, rOrig_of_rel hκ hb hI.2.1 hI.2.2 θ ⟨hs₁, hrel⟩⟩

/-- **The left profile and the original stop word after a completed piece of the left walk.** -/
theorem post_lProf_lOrig (hκ : 0 < κ) (hb : IsPiecewiseConstantBoundaryData b jumps)
    (hI : LInv κ θ b jumps β s) (hreg : IsRegularDriver D)
    (hgood : D.2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf ⊤ D))) (hfin : D.2 ≠ ⊤)
    (hcase : D.2 = 0 ∨ stStatus (ExplState.launch s k D θ ⊤) = stThr (some false)) :
    LProf (ExplState.launch s k D θ ⊤) ∧ LOrig b jumps (stopWord κ (β, θ, recOf ⊤ D)) (ExplState.launch s k D θ ⊤) := by
  rcases hcase with h0 | hthr
  · obtain ⟨hs₁, hrel⟩ := lProf_launch_zero hI.2.1 k θ hreg h0
    exact ⟨hs₁, lOrig_of_rel hκ hb hI.2.1 hI.2.2.1 θ ⟨hs₁, hrel⟩⟩
  · obtain ⟨-, hhit, -, -⟩ := launch_thr_false hfin hthr
    obtain ⟨hs₁, hrel⟩ := lProf_launch hI.2.1 k θ hreg (hgood hfin) hfin hhit
    exact ⟨hs₁, lOrig_of_rel hκ hb hI.2.1 hI.2.2.1 θ ⟨hs₁, hrel⟩⟩

end Post

section Case

variable {κ θ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}

/-- **A piece of a walk followed by another launch is finite and ends with zero lifetime or at a threshold** (the
case analysis of `rInv_walk_step`), for either walk, with a forbidden threshold side `bad`. -/
theorem post_case {right : Bool} {n : ℕ} (bad : Bool)
    (hl : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (2 * n + 1)).2.2.2.1 (2 * n) ≠ none)
    (hk : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (2 * (n + 1) + 1)).2.2.2.1
      (2 * (n + 1)) ≠ none)
    (hno : stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (2 * n + 1)) ≠
      stThr (some bad)) :
    (D (2 * n)).2 ≠ ⊤ ∧ ((D (2 * n)).2 = 0 ∨
      stStatus (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D (2 * n + 1)) = stThr (some (!bad))) := by
  set R := ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D with hRdef
  have hn : ∀ j, 2 * n < j → j < 2 * (n + 1) → (R (j + 1)).2.2.2.1 j = none := by
    intro j hj1 hj2
    have hj : j = 2 * n + 1 := by omega
    subst hj
    exact GW1RestartPair.noLaunch_walk_odd D n
  obtain ⟨-, hrunk, r, hstk⟩ := run_eq_of_last_launch (by omega) hk hl hn
  have hrun1 : R (2 * n + 1) = ExplState.launch (R (2 * n)) (2 * n) (D (2 * n)) θ ⊤ := launch_walk hl
  have hfin : (D (2 * n)).2 ≠ ⊤ := by
    intro htop
    have hmin : min ⊤ (D (2 * n)).2 = ⊤ := by rw [htop]; rfl
    have hd := (launch_eq_of_top (R (2 * n)) (2 * n) (D (2 * n)) θ ⊤ hmin).2.2.2.2.1
    rw [← hrun1] at hd
    have := contStep_eq_self (κ := κ) (b := b) (jumps := jumps) (R (2 * n + 1)) right (Or.inr (Or.inl hd))
    rw [← hrunk] at this
    rw [this, hd] at hstk
    exact absurd hstk (by simp [stArcM])
  refine ⟨hfin, ?_⟩
  by_cases h0 : (D (2 * n)).2 = 0
  · exact Or.inl h0
  · right
    have hcases := launch_status_of_pos (s := R (2 * n)) (k := 2 * n) (θ := θ) hfin h0
    rw [← hrun1] at hcases
    have hdead : stStatus (R (2 * n + 1)) ≠ stDead := by
      intro hd
      have := contStep_eq_self (κ := κ) (b := b) (jumps := jumps) (R (2 * n + 1)) right (Or.inr (Or.inr hd))
      rw [← hrunk] at this
      rw [this, hd] at hstk
      exact absurd hstk (by simp [stArcM, stDead])
    rcases hcases with h | h | h
    · cases bad
      · exact h
      · exact absurd h hno
    · cases bad
      · exact absurd h hno
      · exact h
    · exact absurd h hdead

end Case

end InteractingSLE.Theorem14.GW1Laws
