import HigherDimLQGContinuity.Core.Interfaces

/-!
# The finite union bound for pairs and catalogues

This is the probability summation used in (4.27), before inserting the
geometric cardinality and one-catalogue probability estimates.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

open MeasureTheory
open scoped ENNReal

/-- A union over two net points and one catalogue costs at most the product
of their cardinalities. No measurability hypothesis is needed for this outer
measure bound. -/
theorem q11_pair_catalogue_union_bound {Ω X Y Z : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (A : Finset X) (B : Finset Y) (C : Finset Z)
    (E : X → Y → Z → Set Ω) (u : ℝ≥0∞)
    (hE : ∀ x ∈ A, ∀ y ∈ B, ∀ z ∈ C, μ (E x y z) ≤ u) :
    μ (⋃ x ∈ A, ⋃ y ∈ B, ⋃ z ∈ C, E x y z) ≤
      (A.card * B.card * C.card : ℕ) • u := by
  classical
  calc
    μ (⋃ x ∈ A, ⋃ y ∈ B, ⋃ z ∈ C, E x y z)
        ≤ ∑ x ∈ A, μ (⋃ y ∈ B, ⋃ z ∈ C, E x y z) :=
          measure_biUnion_finset_le A _
    _ ≤ ∑ x ∈ A, ∑ y ∈ B, μ (⋃ z ∈ C, E x y z) := by
          apply Finset.sum_le_sum
          intro x hx
          exact measure_biUnion_finset_le B _
    _ ≤ ∑ x ∈ A, ∑ y ∈ B, ∑ z ∈ C, μ (E x y z) := by
          apply Finset.sum_le_sum
          intro x hx
          apply Finset.sum_le_sum
          intro y hy
          exact measure_biUnion_finset_le C _
    _ ≤ ∑ x ∈ A, ∑ y ∈ B, ∑ z ∈ C, u := by
          apply Finset.sum_le_sum
          intro x hx
          apply Finset.sum_le_sum
          intro y hy
          apply Finset.sum_le_sum
          intro z hz
          exact hE x hx y hy z hz
    _ = (A.card * B.card * C.card : ℕ) • u := by
          simp only [Finset.sum_const]
          rw [smul_smul, smul_smul]

/-- The pair-only form of the same finite union bound. -/
theorem q11_pair_union_bound {Ω X Y : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (A : Finset X) (B : Finset Y)
    (E : X → Y → Set Ω) (u : ℝ≥0∞)
    (hE : ∀ x ∈ A, ∀ y ∈ B, μ (E x y) ≤ u) :
    μ (⋃ x ∈ A, ⋃ y ∈ B, E x y) ≤ (A.card * B.card : ℕ) • u := by
  classical
  calc
    μ (⋃ x ∈ A, ⋃ y ∈ B, E x y)
        ≤ ∑ x ∈ A, μ (⋃ y ∈ B, E x y) := measure_biUnion_finset_le A _
    _ ≤ ∑ x ∈ A, ∑ y ∈ B, μ (E x y) := by
          apply Finset.sum_le_sum
          intro x hx
          exact measure_biUnion_finset_le B _
    _ ≤ ∑ x ∈ A, ∑ y ∈ B, u := by
          apply Finset.sum_le_sum
          intro x hx
          apply Finset.sum_le_sum
          intro y hy
          exact hE x hx y hy
    _ = (A.card * B.card : ℕ) • u := by
          simp only [Finset.sum_const]
          rw [smul_smul]

end HigherDimLQGContinuity
