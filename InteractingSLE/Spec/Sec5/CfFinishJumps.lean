/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfFinishLimits

/-!
# Genuine jumps of a finite force boundary function

Packet PROVE-CFCHART2. At a nonzero point the boundary jump is `λ` times the total
weight of marks at that point. This remains valid when several marks coincide.
-/

set_option autoImplicit false

noncomputable section

open Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CfFinish

open PiecewiseConstantBoundaryData

open scoped Classical in
/-- Subtracting strict and nonstrict finite cumulative sums selects equality. -/
theorem sum_filter_le_sub_lt {α : Type*} [Fintype α] (ρ f : α → ℝ) (y : ℝ) :
    (∑ i ∈ Finset.univ.filter (fun i => f i ≤ y), ρ i) -
      (∑ i ∈ Finset.univ.filter (fun i => f i < y), ρ i) =
        ∑ i ∈ Finset.univ.filter (fun i => f i = y), ρ i := by
  classical
  simp only [Finset.sum_filter, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rcases lt_trichotomy (f i) y with hi | hi | hi
  · simp only [hi.le, hi, ite_true, sub_self, ne_of_lt hi, ite_false]
  · simp only [hi, le_refl, lt_self_iff_false, ite_true, ite_false, sub_zero]
  · simp only [not_le_of_gt hi, not_lt_of_ge hi.le, ne_of_gt hi, ite_false, sub_self]

variable {nL nR : ℕ} (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
  (vL : Fin nL → ℝ) (vR : Fin nR → ℝ)

open scoped Classical in
/-- A negative jump is the left-side coincident weight sum times `λ`. -/
theorem jump_force_of_neg {y : ℝ} (hy : y < 0) :
    rightLim (forceBoundaryData κ ρL ρR vL vR) y -
      leftLim (forceBoundaryData κ ρL ρR vL vR) y =
        sleLambda κ * ∑ i ∈ Finset.univ.filter (fun i => vL i = y), ρL i := by
  rw [rightLim_force_of_neg κ ρL ρR vL vR hy,
    leftLim_force_of_nonpos κ ρL ρR vL vR hy.le]
  have hs := sum_filter_le_sub_lt ρL (fun i => -vL i) (-y)
  simp only [neg_le_neg_iff, neg_lt_neg_iff, neg_inj] at hs
  calc
    _ = sleLambda κ * ((∑ i ∈ Finset.univ.filter (fun i => y ≤ vL i), ρL i) -
        ∑ i ∈ Finset.univ.filter (fun i => y < vL i), ρL i) := by ring
    _ = _ := congrArg (fun z => sleLambda κ * z) hs

open scoped Classical in
/-- A positive jump is the right-side coincident weight sum times `λ`. -/
theorem jump_force_of_pos {y : ℝ} (hy : 0 < y) :
    rightLim (forceBoundaryData κ ρL ρR vL vR) y -
      leftLim (forceBoundaryData κ ρL ρR vL vR) y =
        sleLambda κ * ∑ j ∈ Finset.univ.filter (fun j => vR j = y), ρR j := by
  rw [rightLim_force_of_nonneg κ ρL ρR vL vR hy.le,
    leftLim_force_of_pos κ ρL ρR vL vR hy]
  calc
    _ = sleLambda κ * ((∑ j ∈ Finset.univ.filter (fun j => vR j ≤ y), ρR j) -
        ∑ j ∈ Finset.univ.filter (fun j => vR j < y), ρR j) := by ring
    _ = _ := congrArg (fun z => sleLambda κ * z) (sum_filter_le_sub_lt ρR vR y)

end InteractingSLE.Sec5.CfFinish
