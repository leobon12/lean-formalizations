/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntCanonModel

/-!
# Physical hulls and canonical lifts of actual walk prefixes

Every regular finite run, and every recorded live prefix, has a physical
compact hull model. Its stored lift is exactly the canonical derivative
argument of that hull, without any integer correction.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Complex
open scoped Real NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.WalkIntCanon

open Exist.Staged Exist.StagedLaw GW2aCont

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

theorem exists_hullModel_runChart (spec : ExplSpec)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) :
    ∀ k, (∀ j < k, ∀ (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps spec D (j + 1)).2.2.2.1 j = some (c, θ) →
        GW1P.PieceRegular (D j).1 (min (instrTime spec j) (D j).2)) →
      Nonempty (HullModel (ExplState.run κ b jumps spec D k).2.2.2.2.1)
  | 0, _ => ⟨hullModel_id.recenter spec.1⟩
  | k + 1, hreg => by
    have hreg' : ∀ j < k, ∀ (c : Chart) (θ : ℝ),
        (ExplState.run κ b jumps spec D (j + 1)).2.2.2.1 j = some (c, θ) →
          GW1P.PieceRegular (D j).1 (min (instrTime spec j) (D j).2) :=
      fun j hj => hreg j (Nat.lt_succ_of_lt hj)
    obtain ⟨M⟩ := exists_hullModel_runChart spec D k hreg'
    have hL := isNormalized_runChart (κ := κ) (b := b) (jumps := jumps) spec D k hreg'
    rcases hl : (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k with _ | ⟨c, θ⟩
    · obtain ⟨a, ha⟩ := chart_run_succ_of_noLaunch (κ := κ) (b := b)
        (jumps := jumps) spec D hl
      rw [ha]
      exact ⟨M.recenter a⟩
    · obtain ⟨-, he, -⟩ := eq_launch_of_launches (κ := κ) (b := b)
        (jumps := jumps) spec D hl
      rw [he]
      by_cases htop : min (instrTime spec k) (D k).2 = ⊤
      · rw [GW2aCont.chart_launch_of_top _ _ _ _ _ htop]
        exact ⟨M⟩
      rw [chart_launch _ _ _ _ _ htop]
      obtain ⟨hW, hW0⟩ :=
        (hreg k (Nat.lt_succ_self k) c θ hl).continuous_stoppedReal
      exact ⟨M.loewner hL hW hW0 (NNReal.coe_nonneg _)⟩

theorem exists_hullModel_prefixChart (spec : ExplSpec)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (n : ℕ)
    (hreg : ∀ j < n, ∀ (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps spec D (j + 1)).2.2.2.1 j = some (c, θ) →
        GW1P.PieceRegular (D j).1 (min (instrTime spec j) (D j).2))
    (hD : ∀ j, IsRegularDriver (D j)) {pre post : List WalkBdry.Piece}
    {pc : WalkBdry.Piece}
    (hs : (ExplState.run κ b jumps spec D n).1 = pre ++ pc :: post)
    {τ : ℝ≥0} (hτ : (τ : ℝ≥0∞) < pc.2.2) :
    Nonempty (HullModel (WalkBdry.prefixChart pc τ)) := by
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
  obtain ⟨M⟩ := exists_hullModel_runChart (κ := κ) (b := b) (jumps := jumps)
    spec D ℓ hreg'
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
  exact ⟨M.loewner hL hWc hW0 (NNReal.coe_nonneg _)⟩

/-- The canonical argument is independent of which mapping-out function
represents the physical hull. -/
theorem HullModel.lift_eq_canonDerivLog {c : Chart} (M : HullModel c)
    (h : IsNormalized c) :
    EqOn c.2.2 (fun z => (Restart.canonDerivLog M.hull z).im) (H \ M.hull) := by
  have hL := Restart.isCanonicalDerivLog_canonDerivLog M.isHull
  exact M.lift_eq_canonical h (hL.congr M.isHull
    ((ConformalImage.isMapOut_mapOut M.isHull).eqOn M.isHull M.mapOut))

/-- Every recorded live prefix has a physical compact hull whose canonical
derivative argument is exactly its stored lift. -/
theorem exists_canonical_prefix (spec : ExplSpec)
    (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) (n : ℕ)
    (hreg : ∀ j < n, ∀ (c : Chart) (θ : ℝ),
      (ExplState.run κ b jumps spec D (j + 1)).2.2.2.1 j = some (c, θ) →
        GW1P.PieceRegular (D j).1 (min (instrTime spec j) (D j).2))
    (hD : ∀ j, IsRegularDriver (D j)) {pre post : List WalkBdry.Piece}
    {pc : WalkBdry.Piece}
    (hs : (ExplState.run κ b jumps spec D n).1 = pre ++ pc :: post)
    {τ : ℝ≥0} (hτ : (τ : ℝ≥0∞) < pc.2.2) :
    ∃ M : HullModel (WalkBdry.prefixChart pc τ),
      EqOn (WalkBdry.prefixChart pc τ).2.2
        (fun z => (Restart.canonDerivLog M.hull z).im) (H \ M.hull) := by
  obtain ⟨M⟩ := exists_hullModel_prefixChart spec D n hreg hD hs hτ
  exact ⟨M, M.lift_eq_canonDerivLog (isNormalized_prefixChart spec D n hreg hD hs hτ)⟩

end InteractingSLE.Theorem14.WalkIntCanon
