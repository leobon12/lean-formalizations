/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBS3RetainedReg
import InteractingSLE.Spec.Supplement.SBS3TerminalAfterChart

/-!
# S3: the actual complement at every finite prefix
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.SB.S3

open Exist Exist.Staged Exist.StagedLaw Restart

/-- A finite ordinary-time prefix has chart domain clopen in its actual
explored-set complement. Switches, nonlaunches and terminal states are
included; no following launch is assumed. -/
theorem ae_clopen_runChart_stageSet_finite_prefix {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {spec : ExplSpec}
    {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hR : StagedPiecesRegular κ b jumps P spec E)
    (k : ℕ) (htime : HasFiniteOrdinaryTimes spec k) :
    ∀ᵐ ω ∂P,
      (((ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1).dom : Set ℂ) ⊆
          H \ WalkLaw.stageSet κ b jumps spec E k ω ∧
        IsOpen ((H \ WalkLaw.stageSet κ b jumps spec E k ω) \
          (ExplState.run κ b jumps spec (fun j => E j ω) k).2.2.2.2.1.dom) := by
  induction k with
  | zero =>
    refine Eventually.of_forall fun ω => ?_
    rw [WalkLaw.stageSet_zero]
    have hd : ((ExplState.run κ b jumps spec (fun j => E j ω) 0).2.2.2.2.1.dom : Set ℂ) = H := by
      change ((Chart.id.recenter spec.1).dom : Set ℂ) = H
      rw [WalkSide.dom_recenter]
      exact WalkNorm.coe_dom_id
    rw [hd]
    simp only [sdiff_empty, Set.sdiff_self]
    exact ⟨Subset.rfl, isOpen_empty⟩
  | succ k ih =>
    filter_upwards [ih (fun j hj => htime j (Nat.lt_succ_of_lt hj)),
      ae_clopen_runChart_stageSet_after_finite hR k] with ω hold hpost
    by_cases hn : (ExplState.run κ b jumps spec (fun j => E j ω) (k + 1)).2.2.2.1 k = none
    · have hset : WalkLaw.stageSet κ b jumps spec E (k + 1) ω =
          WalkLaw.stageSet κ b jumps spec E k ω := by
        rw [WalkLaw.stageSet_succ]
        simp only [WalkLaw.pieceSet, ite_eq_left hn, union_empty]
      rw [chart_recenter_of_noLaunch spec (fun j => E j ω) hn, WalkSide.dom_recenter, hset]
      exact hold
    · obtain ⟨⟨c, θ⟩, hcθ⟩ := Option.ne_none_iff_exists'.1 hn
      exact hpost hn (ne_top_of_le_ne_top
        (htime k (Nat.lt_succ_self k) θ _ (eq_launch_of_launches spec (fun j => E j ω) hcθ).1)
        (min_le_left _ _))

end InteractingSLE.Theorem14.SB.S3
