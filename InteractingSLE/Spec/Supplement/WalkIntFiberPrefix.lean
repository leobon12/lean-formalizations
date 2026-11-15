/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntFiberLimit

/-!
# Proper inverse extensions of recorded live prefixes

A prefix is the final chart of the existing capped program. Its proper
boundary extension is inherited from that program's regular pieces.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open scoped Real NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.Theorem14.WalkIntFiber

open WalkBdry Exist.StagedLaw

/-- The good boundary extension needed by the fibre argument is already
available for every live recorded boundary-walk prefix. -/
theorem hasProperBdryExt_prefixChart {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    (θ : ℝ) (right : Bool) (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (hreg : ∀ k c θ', (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right)
      D (k + 1)).2.2.2.1 k = some (c, θ') →
      GW1P.PieceRegular (D k).1
        (min (instrTime (boundaryWalkSpec b jumps θ right) k) (D k).2))
    (hD : ∀ k, Exist.Staged.IsRegularDriver (D k))
    {pre post : List Piece} {pc : Piece}
    (hs : (ExplState.run κ b jumps (boundaryWalkSpec b jumps θ right) D
      (boundaryWalkSpec b jumps θ right).2.2.length).1 = pre ++ pc :: post)
    {τ : ℝ≥0} (hτ : (τ : ℝ≥0∞) < pc.2.2) :
    GW1P.HasProperBdryExt (prefixChart pc τ) := by
  let w := boundaryWalkSpec b jumps θ right
  obtain ⟨ℓ, hℓ, θ', hl, -, hpc⟩ :=
    WalkSide.exists_launch_of_pieces_eq (κ := κ) (b := b) (jumps := jumps)
      w D w.2.2.length hs
  have hins := (eq_launch_of_launches (κ := κ) (b := b) (jumps := jumps) w D hl).1
  obtain ⟨hθ, ht⟩ := WalkLeaf.boundaryWalkSpec_inl hins
  have hins' : w.2.2[ℓ]? = some (Sum.inl (θ, ⊤)) := by
    simpa only [hθ, ht] using hins
  rw [ht] at hpc
  have hτ' : (τ : ℝ≥0∞) < min ⊤ (D ℓ).2 := by
    rw [hpc] at hτ
    exact hτ
  let E : ℕ → Unit → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun k _ => D k
  have hchart := WalkSide.prefixChart_eq_chart (κ := κ) (b := b) (jumps := jumps)
    E () hℓ.le hins' hl (hD ℓ) hτ'
  rw [hpc, hchart]
  exact (GW1P.isClosed_pieces_run (WalkSide.capSpec w ℓ θ τ) D
    (WalkSide.pieceRegular_capSpec D hℓ.le hins' hreg τ) (ℓ + 1)).1

end InteractingSLE.Theorem14.WalkIntFiber
