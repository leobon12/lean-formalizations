/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntRunChronPrefixArc
import InteractingSLE.Spec.Supplement.WalkIntChronoCap

/-!
# Actual capped carriers have chronological histories

The finite cap changes the ordinary lifetime, while retaining the earlier
real connectors. Append its finite physical arc to the original run's
pre-launch history. The endpoint need not be the capped machine's record.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.WalkIntRunChron

open GW1WalkChain GW1Bookkeep Exist Exist.Staged Exist.StagedLaw WalkBdry

/-- Exact physical carrier identity for a capped launch, including all
old connectors and the actual minimum of cap time and sampled lifetime. -/
theorem prefixPhysSet_cap_eq {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    {w : ExplSpec} (D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞) {k : ℕ} {θ θ' : ℝ} {c : Chart}
    (hk : k ≤ w.2.2.length) (hins : w.2.2[k]? = some (Sum.inl (θ, ⊤)))
    (hl : (ExplState.run κ b jumps w D (k + 1)).2.2.2.1 k = some (c, θ')) (τ : ℝ≥0) :
    SB.prefixPhysSet κ b jumps (WalkSide.capSpec w k θ τ) D (k + 1) =
      SB.prefixPhysSet κ b jumps w D k ∪
        c.tipSet (fun r => (D k).1 (min (r : ℝ≥0∞) (min (τ : ℝ≥0∞) (D k).2)).toNNReal)
          (min (τ : ℝ≥0∞) (D k).2) := by
  have hp := WalkSide.pieces_run_capSpec_succ hk hins D hl (τ : ℝ≥0∞)
  have ha : (ExplState.run κ b jumps (WalkSide.capSpec w k θ τ) D (k + 1)).2.1 =
      (ExplState.run κ b jumps w D k).2.1 := by
    rw [WalkSide.run_capSpec_succ hk D, GW2aCont.arcs_flowStep]
  have hc := (eq_launch_of_launches w D hl).2.2
  ext z
  simp only [SB.prefixPhysSet, hp, ha, WalkSide.capSpec_fst, WalkSide.recPiece,
    hc, mem_union, mem_iUnion, exists_prop, List.mem_append, List.mem_singleton]
  simp only [or_and_right, exists_or, exists_eq_left]
  constructor
  · rintro ((hz | hz | hz) | hz)
    · exact Or.inl (Or.inl (Or.inl hz))
    · exact Or.inl (Or.inl (Or.inr hz))
    · exact Or.inr hz
    · exact Or.inl (Or.inr hz)
  · rintro (((hz | hz) | hz) | hz)
    · exact Or.inl (Or.inl hz)
    · exact Or.inl (Or.inr (Or.inl hz))
    · exact Or.inr hz
    · exact Or.inl (Or.inr (Or.inr hz))

end InteractingSLE.Theorem14.WalkIntRunChron
