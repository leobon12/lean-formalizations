/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2UxExit
import InteractingSLE.Spec.Supplement.SB2LuStart
import InteractingSLE.Spec.Supplement.BW1TermRestart

/-!
# The relative walk's start: the inputs of `stCorr_run_strong2` before relative stage `2`

Packet PROVE-T14-SB2LIFT (round 22; the start, handoff §R21.2 1). `stCorr_run_strong2` asks of the relative walk,
before the start stage `i₀ = 2`: no left moves, no left hits, finite lifetimes, and the profile invariant `InvR` at
stage `2`. Both of PROVE-SB2-LIFTSET's starts give them deterministically.

* **`relStart_arc`** (the start on an actual connector, `ArcStart`): the relative first piece has zero lifetime
  (`zero₀`), so the relative walk is at a threshold without a hit at `0`. The outward height there is the actual one at
  `R` (`RayCorr.rightLim_eq`), which is low (`ArcStart.low`). So stage `1` moves right, and `InvR` at stage `2` comes
  from the root (`lProf3_init`, `BW1Term.rProf_init`), the zero launch (`profiles_launch`) and the right move
  (`invR_cont`);
* **`relStart_piece`** (the start on an actual piece, `PieceStart`): the relative first piece has a nonzero finite
  lifetime and no left hit (`PieceStart.zero`, `top`, `hitL₂`). The walk ends at a right threshold or dead, both
  allowed, and the same steps give `InvR` at stage `2`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC)

namespace InteractingSLE.Theorem14.SB.Lk

open Exist Exist.Staged Exist.StagedLaw LuM GW1W GW1WalkExit GW1WalkFinish
open PiecewiseConstantBoundaryData (rightLim leftLim jumpSet)

variable {κ θ : ℝ} {b₂ : ℝ → ℝ} {J₂ : Finset ℝ}

theorem run_zero_walk' {b : ℝ → ℝ} {J : Finset ℝ} (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    ExplState.run κ b J (boundaryWalkSpec b J θ true) D 0 = ExplState.init 0 := by
  simp [ExplState.run, boundaryWalkSpec]

/-- The root is ready for its launch. -/
theorem rReady_init : RReady (ExplState.init 0) := ⟨Or.inl rfl, rfl⟩

/-- **The invariant after the root launch** (with a regular driver and a good record). -/
theorem invR_launch_init {D : (ℝ≥0 → ℝ) × ℝ≥0∞} (hreg : IsRegularDriver D)
    (hgood : D.2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf ⊤ D))) :
    InvR (ExplState.launch (ExplState.init 0) 0 D θ ⊤) := by
  obtain ⟨hl, ht⟩ := profiles_launch (lProf3_init 0) BW1Term.rProf_init rReady_init 0 θ hreg hgood
  exact ⟨hl, ht, fun h => absurd h (stStatus_launch_ne_arcM _ _ _ _)⟩

/-- The record of the relative root piece is good (a launched regular piece). -/
theorem isDrvGood_root {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D) (hreg : IsRegularDriver (D 0)) :
    (D 0).2 ≠ ⊤ → LocalExt.IsDrvGood (recHist (recOf ⊤ (D 0))) := fun hT => by
  have hl : (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D 1).2.2.2.1 0 ≠ none := by
    rw [run_one_walk b₂ J₂ D]
    exact launched_launch _ _ _ _ _
  exact BW1Prop.isDrvGood_of_pieceRegular hreg (pieceRegular_of_launch hP hl) hT

/-- **The common part of both starts**: from an allowed state after the root launch with no left hit there, the
relative walk has `InvR` at stage `2`, no left moves and no left hits before it, and finite lifetimes before it (if
the root piece is finite). -/
theorem relStart_of_allowed {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D) (hreg : IsRegularDriver (D 0))
    (hA : AllowedSt κ b₂ (ExplState.launch (ExplState.init 0) 0 (D 0) θ ⊤))
    (hL : ¬ ∃ y : ℝ, y < 0 ∧ lHit (stChart (ExplState.init 0)) ⊤ (D 0) y) (hfin : (D 0).2 ≠ ⊤) :
    InvR (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D 2) ∧
      (∀ j, j < 2 → NoLeftMove κ b₂ J₂ θ D j) ∧ (∀ j, j < 2 → NoLeftHit κ b₂ J₂ θ D j) ∧
      ∀ j, j < 2 → (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D (j + 1)).2.2.2.1 j ≠ none →
        (D j).2 ≠ ⊤ := by
  have hlen := one_lt_length_boundaryWalkSpec b₂ J₂ θ true
  have h1 := run_one_walk (κ := κ) (θ := θ) b₂ J₂ D
  have h2 : ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D 2 =
      ExplState.contStep κ b₂ J₂ (ExplState.launch (ExplState.init 0) 0 (D 0) θ ⊤) none true := by
    rw [run_succ_walk_cont (by omega) (by norm_num), h1]
  have hI1 := invR_launch_init (θ := θ) hreg (isDrvGood_root hP hreg)
  refine ⟨by rw [h2]; exact invR_cont hA hI1, fun j hj => ?_, fun j hj => ?_, fun j hj hl => ?_⟩
  · interval_cases j
    · exact noLeftMove_of_arcs_eq (arcs_run_succ_flow (by omega))
    · have h := (allowedSt_cont (D := D) (by omega : 1 < (boundaryWalkSpec b₂ J₂ θ true).2.2.length)
        (by norm_num : 1 % 2 = 1) (by rw [h1]; exact hA)).2
      exact h
  · interval_cases j
    · intro _
      rw [run_zero_walk']
      exact hL
    · intro hl
      exact absurd (GW1W.even_of_launches_walk hl).1 (by norm_num)
  · interval_cases j
    · exact hfin
    · exact absurd (GW1W.even_of_launches_walk hl).1 (by norm_num)

variable {b₁ : ℝ → ℝ} {J₁ : Finset ℝ} {R : ℝ} {ι : ℝ → ℝ}

/-- **The relative start at an actual connector** (`ArcStart`): a zero-lifetime root piece and a low outward height
at `R`. -/
theorem relStart_arc (hι : RayCorr b₁ J₁ b₂ J₂ R ι) {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D) (hreg : IsRegularDriver (D 0))
    (h0 : (D 0).2 = 0) (hlow : rightLim b₁ R + θ * chiC κ ≤ -sleLambda κ) :
    InvR (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D 2) ∧
      (∀ j, j < 2 → NoLeftMove κ b₂ J₂ θ D j) ∧ (∀ j, j < 2 → NoLeftHit κ b₂ J₂ θ D j) ∧
      ∀ j, j < 2 → (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D (j + 1)).2.2.2.1 j ≠ none →
        (D j).2 ≠ ⊤ := by
  obtain ⟨hst, hpt, -, hθ, -⟩ := launch_init_zero (θ := θ) hreg h0
  have hA : AllowedSt κ b₂ (ExplState.launch (ExplState.init 0) 0 (D 0) θ ⊤) := by
    refine Or.inr (Or.inr (Or.inr (Or.inr ⟨hst, ?_⟩)))
    simp only [↓reduceIte]
    rw [hpt, hθ, ← hι.map_base, hι.rightLim_eq R le_rfl]
    exact hlow
  have hL : ¬ ∃ y : ℝ, y < 0 ∧ lHit (stChart (ExplState.init 0)) ⊤ (D 0) y := by
    rintro ⟨y, hy, hhit⟩
    refine not_leftHit_of_lProf3 (lProf3_init 0) BW1Term.rProf_init 0 θ hreg (isDrvGood_root hP hreg) ?_
      ⟨y, hy, hhit⟩
    rw [hst]
    intro h
    cases h
  exact relStart_of_allowed hP hreg hA hL (by rw [h0]; exact ENNReal.zero_ne_top)

/-- **The relative start at an actual piece** (`PieceStart`): a nonzero finite root piece without a left hit. -/
theorem relStart_piece {D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hP : RegLaunches κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D) (hreg : IsRegularDriver (D 0))
    (hnz : (D 0).2 ≠ 0) (hfin : (D 0).2 ≠ ⊤)
    (hL : ¬ ∃ y : ℝ, y < 0 ∧ lHit (stChart (ExplState.init 0)) ⊤ (D 0) y) :
    InvR (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D 2) ∧
      (∀ j, j < 2 → NoLeftMove κ b₂ J₂ θ D j) ∧ (∀ j, j < 2 → NoLeftHit κ b₂ J₂ θ D j) ∧
      ∀ j, j < 2 → (ExplState.run κ b₂ J₂ (boundaryWalkSpec b₂ J₂ θ true) D (j + 1)).2.2.2.1 j ≠ none →
        (D j).2 ≠ ⊤ := by
  have hA : AllowedSt κ b₂ (ExplState.launch (ExplState.init 0) 0 (D 0) θ ⊤) := by
    obtain ⟨-, -, -, -, hst, -⟩ := launch_eq_of_ne_top (ExplState.init 0) 0 (D 0) θ ⊤ (min_top_ne_top hfin)
    have hnlt : ¬ (⊤ : ℝ≥0∞) < (D 0).2 := not_lt.2 le_top
    have hL' : ¬ ∃ y : ℝ, y < stRecL (ExplState.init 0) ∧ lHit (stChart (ExplState.init 0)) ⊤ (D 0) y := hL
    have hst' : stStatus (ExplState.launch (ExplState.init 0) 0 (D 0) θ ⊤) = stThr (some true) ∨
        stStatus (ExplState.launch (ExplState.init 0) 0 (D 0) θ ⊤) = stDead := by
      rw [hst]
      unfold lStatus
      simp only [hnlt, hnz, hL', ↓reduceIte]
      split_ifs
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hst' with h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
    · exact Or.inr (Or.inr (Or.inl h))
  exact relStart_of_allowed hP hreg hA hL hfin

end InteractingSLE.Theorem14.SB.Lk
