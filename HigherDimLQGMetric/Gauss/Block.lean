import Mathlib.Data.Nat.Dist
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.InnerProductSpace.Orthonormal
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Schur bound for Gaussian blocks

The row-sum estimate controls the squared norm of any finite sum from
pairwise covariance bounds. It is independent of the number of blocks.
-/

set_option autoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Finset
private theorem row_eq (c : ℕ → ℝ) {n i : ℕ} (hi : i < n) :
    (∑ j ∈ range n, c (Nat.dist i j)) =
      c 0 + (∑ k ∈ range i, c (k + 1)) +
        (∑ k ∈ range (n - (i + 1)), c (k + 1)) := by
  have hn : n = i + 1 + (n - (i + 1)) := by omega
  conv_lhs => rw [hn, sum_range_add, sum_range_succ]
  have hleft : (∑ j ∈ range i, c (Nat.dist i j)) =
      ∑ k ∈ range i, c (k + 1) := by
    rw [← sum_range_reflect (fun k => c (k + 1)) i]
    apply sum_congr rfl
    intro j hj
    have hji : j < i := mem_range.mp hj
    congr 1
    simp only [Nat.dist]
    omega
  rw [hleft]
  have hmid : Nat.dist i i = 0 := by simp
  rw [hmid]
  have hright : (∑ x ∈ range (n - (i + 1)), c (Nat.dist i (i + 1 + x))) =
      ∑ k ∈ range (n - (i + 1)), c (k + 1) := by
    apply sum_congr rfl
    intro j hj
    congr 1
    simp only [Nat.dist]
    omega
  rw [hright]
  ring

private theorem row_le (c : ℕ → ℝ) (hc : ∀ k, 0 ≤ c k) (hcs : Summable c)
    {n i : ℕ} (hi : i < n) :
    (∑ j ∈ range n, c (Nat.dist i j)) ≤
      c 0 + 2 * ∑' k, c (k + 1) := by
  rw [row_eq c hi]
  have hst : Summable (fun k => c (k + 1)) :=
    (summable_nat_add_iff 1).2 hcs
  have h₁ : (∑ k ∈ range i, c (k + 1)) ≤ ∑' k, c (k + 1) :=
    hst.sum_le_tsum _ (by intro j hj; exact hc _) 
  have h₂ : (∑ k ∈ range (n - (i + 1)), c (k + 1)) ≤ ∑' k, c (k + 1) :=
    hst.sum_le_tsum _ (by intro j hj; exact hc _)
  linarith

theorem norm_sum_sq_le_of_corr {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {n : ℕ} (Y : Fin n → H) (c : ℕ → ℝ)
    (hc0 : ∀ k, 0 ≤ c k) (hcs : Summable c)
    (hcorr : ∀ i j : Fin n,
      |@inner ℝ H _ (Y i) (Y j)| ≤
        c (Nat.dist (i : ℕ) (j : ℕ)) * (‖Y i‖ * ‖Y j‖)) :
    ‖∑ i, Y i‖ ^ 2 ≤
      (c 0 + 2 * ∑' k, c (k + 1)) * ∑ i, ‖Y i‖ ^ 2 := by
  let K : ℝ := c 0 + 2 * ∑' k, c (k + 1)
  have hrow (i : Fin n) :
      (∑ j : Fin n, c (Nat.dist (i : ℕ) (j : ℕ))) ≤ K := by
    change (∑ j : Fin n, (fun k : ℕ => c (Nat.dist (i : ℕ) k)) j) ≤
      c 0 + 2 * ∑' k, c (k + 1)
    exact (le_of_eq (Fin.sum_univ_eq_sum_range
      (fun k : ℕ => c (Nat.dist (i : ℕ) k)) n)).trans
        (row_le c hc0 hcs i.isLt)
  have hpoint (i j : Fin n) :
      c (Nat.dist (i : ℕ) (j : ℕ)) * (‖Y i‖ * ‖Y j‖) ≤
      (c (Nat.dist (i : ℕ) (j : ℕ)) * ‖Y i‖ ^ 2 +
        c (Nat.dist (i : ℕ) (j : ℕ)) * ‖Y j‖ ^ 2) / 2 := by
    have hc := hc0 (Nat.dist (i : ℕ) (j : ℕ))
    have hs := sq_nonneg (‖Y i‖ - ‖Y j‖)
    nlinarith
  have hleft :
      (∑ i : Fin n, ∑ j : Fin n,
        c (Nat.dist (i : ℕ) (j : ℕ)) * ‖Y i‖ ^ 2) ≤
      K * ∑ i : Fin n, ‖Y i‖ ^ 2 := by
    calc
      _ = ∑ i : Fin n, ‖Y i‖ ^ 2 *
          (∑ j : Fin n, c (Nat.dist (i : ℕ) (j : ℕ))) := by
            apply Finset.sum_congr rfl
            intro i hi
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j hj
            ring
      _ ≤ ∑ i : Fin n, ‖Y i‖ ^ 2 * K := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (hrow i) (sq_nonneg _)
      _ = K * ∑ i : Fin n, ‖Y i‖ ^ 2 := by rw [← Finset.sum_mul]; ring
  have hright :
      (∑ i : Fin n, ∑ j : Fin n,
        c (Nat.dist (i : ℕ) (j : ℕ)) * ‖Y j‖ ^ 2) ≤
      K * ∑ i : Fin n, ‖Y i‖ ^ 2 := by
    rw [Finset.sum_comm]
    convert hleft using 1
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [Nat.dist_comm]
  have hnorm : ‖∑ i : Fin n, Y i‖ ^ 2 =
      ∑ i : Fin n, ∑ j : Fin n, inner ℝ (Y i) (Y j) := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    simp_rw [inner_sum]
  calc
    ‖∑ i, Y i‖ ^ 2 =
        ∑ i : Fin n, ∑ j : Fin n, inner ℝ (Y i) (Y j) := hnorm
    _ ≤ ∑ i : Fin n, ∑ j : Fin n, |inner ℝ (Y i) (Y j)| := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      exact le_abs_self _
    _ ≤ ∑ i : Fin n, ∑ j : Fin n,
        c (Nat.dist (i : ℕ) (j : ℕ)) * (‖Y i‖ * ‖Y j‖) := by
      exact Finset.sum_le_sum (fun i hi =>
        Finset.sum_le_sum (fun j hj => hcorr i j))
    _ ≤ (∑ i : Fin n, ∑ j : Fin n,
        (c (Nat.dist (i : ℕ) (j : ℕ)) * ‖Y i‖ ^ 2 +
        c (Nat.dist (i : ℕ) (j : ℕ)) * ‖Y j‖ ^ 2)) / 2 := by
      have hh := Finset.sum_le_sum (s := Finset.univ)
        (fun i (hi : i ∈ (Finset.univ : Finset (Fin n))) =>
          Finset.sum_le_sum (s := Finset.univ)
            (fun j (hj : j ∈ (Finset.univ : Finset (Fin n))) => hpoint i j))
      simpa only [Finset.sum_div] using hh
    _ = ((∑ i : Fin n, ∑ j : Fin n,
        c (Nat.dist (i : ℕ) (j : ℕ)) * ‖Y i‖ ^ 2) +
        (∑ i : Fin n, ∑ j : Fin n,
        c (Nat.dist (i : ℕ) (j : ℕ)) * ‖Y j‖ ^ 2)) / 2 := by
      simp only [← Finset.sum_add_distrib]
    _ ≤ K * ∑ i : Fin n, ‖Y i‖ ^ 2 := by linarith only [hleft, hright]

end HigherDimLQGMetric
