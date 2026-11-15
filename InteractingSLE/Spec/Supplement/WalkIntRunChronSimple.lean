/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntRunChronRecorded

/-!
# The actual chronological piece inputs from GW1 simplicity and coordinates

Use the committed GW1 adapter. Piece simplicity already gives regularity
of every launched piece; the run chart therefore maps H into H. Physical
seed and endpoint coordinates supply PieceSimpleAt with no history input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.WalkIntRunChron

open GW1WalkChain GW1Bookkeep Exist Exist.Staged Exist.StagedLaw

/-- The entire hP argument of the run-history construction follows from
the already defined piece simplicity and physical tip coordinates. -/
theorem pieceSimpleAt_at_launch {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (spec : ExplSpec) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hSimple : ∀ k c θ', (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ') →
      GW1Z.IsSimplePiece c (D k).1 (min (instrTime spec k) (D k).2)
        (SB.prefixPhysSet κ b jumps spec D k))
    (hTip : WalkTipCoordinates κ b jumps spec D) {k : ℕ} {c : Chart} {θ' : ℝ}
    (hl : (ExplState.run κ b jumps spec D (k + 1)).2.2.2.1 k = some (c, θ'))
    (hseed : (stPt (ExplState.run κ b jumps spec D k) : ℂ) ∈
      statePhysicalSet spec.1 (ExplState.run κ b jumps spec D k)) :
    PieceSimpleAt c (D k).1 (min (instrTime spec k) (D k).2)
      (statePhysicalSet spec.1 (ExplState.run κ b jumps spec D k))
      (stPt (ExplState.run κ b jumps spec D k)) (stPt (ExplState.run κ b jumps spec D (k + 1))) := by
  have hreg : ∀ j c θ', (ExplState.run κ b jumps spec D (j + 1)).2.2.2.1 j = some (c, θ') →
      GW1P.PieceRegular (D j).1 (min (instrTime spec j) (D j).2) := by
    intro j c θ' hj
    obtain ⟨_, η, _, _, _, h0, hW, hη, htr, _, _⟩ := hSimple j c θ' hj
    exact ⟨h0, hW, η, hη, htr⟩
  have hmaps := maps_H_chart_run (κ := κ) (b := b) (jumps := jumps) spec D hreg k
  have hc := (eq_launch_of_launches spec D hl).2.2
  have hmaps' : MapsTo c.2.1 H H := by rw [hc]; exact hmaps
  exact pieceSimpleAt_of_isSimplePiece (hSimple k c θ' hl) hmaps' hseed
    (hTip k c θ' hl).1 (hTip k c θ' hl).2

end InteractingSLE.Theorem14.WalkIntRunChron
