/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntCanonChart

/-!
# The actual run and prefix lifts are normalized at infinity

The finite program induction follows the existing derivative-lift induction.
In particular an infinite terminal stop leaves the previous chart intact.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Complex
open scoped Real NNReal ENNReal

namespace InteractingSLE.Theorem14.WalkIntCanon

open Exist.Staged Exist.StagedLaw GW2aCont

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- Every run chart whose launched pieces are regular has its inherited
zero-at-infinity derivative argument. -/
theorem isNormalized_runChart (spec : ExplSpec)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    ∀ k, (∀ j < k, ∀ (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps spec D (j + 1)).2.2.2.1 j = some (c, θ) →
        GW1P.PieceRegular (D j).1 (min (instrTime spec j) (D j).2)) →
      IsNormalized (ExplState.run κ b jumps spec D k).2.2.2.2.1
  | 0, _ => isNormalized_id.recenter spec.1
  | k + 1, hreg => by
    have hreg' : ∀ j < k, ∀ (c : Chart) (θ : ℝ),
        (ExplState.run κ b jumps spec D (j + 1)).2.2.2.1 j = some (c, θ) →
          GW1P.PieceRegular (D j).1 (min (instrTime spec j) (D j).2) :=
      fun j hj => hreg j (Nat.lt_succ_of_lt hj)
    have hL := isNormalized_runChart spec D k hreg'
    rcases hl : (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k with _ | ⟨c, θ⟩
    · obtain ⟨a, ha⟩ := chart_run_succ_of_noLaunch (κ := κ) (b := b)
        (jumps := jumps) spec D hl
      rw [ha]
      exact hL.recenter a
    · obtain ⟨-, he, -⟩ := eq_launch_of_launches (κ := κ) (b := b)
        (jumps := jumps) spec D hl
      rw [he]
      by_cases htop : min (instrTime spec k) (D k).2 = ⊤
      · rw [GW2aCont.chart_launch_of_top _ _ _ _ _ htop]
        exact hL
      rw [chart_launch _ _ _ _ _ htop]
      obtain ⟨hW, hW0⟩ :=
        (hreg k (Nat.lt_succ_self k) c θ hl).continuous_stoppedReal
      exact hL.loewner hW hW0 (NNReal.coe_nonneg _)

/-- A recorded live prefix uses the actual canonical branch, including
every earlier launch and real recentring. -/
theorem isNormalized_prefixChart (spec : ExplSpec)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (n : ℕ)
    (hreg : ∀ j < n, ∀ (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps spec D (j + 1)).2.2.2.1 j = some (c, θ) →
        GW1P.PieceRegular (D j).1 (min (instrTime spec j) (D j).2))
    (hD : ∀ j, IsRegularDriver (D j)) {pre post : List WalkBdry.Piece}
    {pc : WalkBdry.Piece}
    (hs : (ExplState.run κ b jumps spec D n).1 = pre ++ pc :: post)
    {τ : ℝ≥0} (hτ : (τ : ℝ≥0∞) < pc.2.2) :
    IsNormalized (WalkBdry.prefixChart pc τ) := by
  obtain ⟨ℓ, hℓ, θ', -, -, hpc⟩ :=
    WalkSide.exists_launch_of_pieces_eq (κ := κ) (b := b) (jumps := jumps)
      spec D n hs
  subst hpc
  have hτ' : (τ : ℝ≥0∞) < min (instrTime spec ℓ) (D ℓ).2 := hτ
  rw [WalkSide.prefixChart_recPiece _ (hD ℓ) hτ']
  have hτζ : (τ : ℝ≥0∞) < (D ℓ).2 := hτ'.trans_le (min_le_right _ _)
  have hreg' : ∀ j < ℓ, ∀ (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps spec D (j + 1)).2.2.2.1 j = some (c, θ) →
        GW1P.PieceRegular (D j).1 (min (instrTime spec j) (D j).2) :=
    fun j hj => hreg j (hj.trans hℓ)
  have hL := isNormalized_runChart (κ := κ) (b := b) (jumps := jumps)
    spec D ℓ hreg'
  have hWon : ContinuousOn (D ℓ).1
      {t : ℝ≥0 | (t : ℝ≥0∞) ≤ min (τ : ℝ≥0∞) (D ℓ).2} :=
    (hD ℓ).1.mono fun t ht => (ht.trans (min_le_left _ _)).trans_lt hτζ
  have hWc : Continuous fun x : ℝ =>
      (D ℓ).1 (min ((x.toNNReal : ℝ≥0) : ℝ≥0∞)
        (min (τ : ℝ≥0∞) (D ℓ).2)).toNNReal :=
    (CounterflowRange.continuous_stopped hWon).comp continuous_real_toNNReal
  have hW0 : (fun x : ℝ => (D ℓ).1
      (min ((x.toNNReal : ℝ≥0) : ℝ≥0∞) (min (τ : ℝ≥0∞) (D ℓ).2)).toNNReal) 0 = 0 := by
    simp only [Real.toNNReal_zero, ENNReal.coe_zero, zero_le, min_eq_left,
      ENNReal.toNNReal_zero]
    exact (hD ℓ).2.1
  exact hL.loewner hWc hW0 (NNReal.coe_nonneg _)

end InteractingSLE.Theorem14.WalkIntCanon
