import HigherDimLQGMetric.Gauss.Block

/-!
# Geometric Schur coefficient

The nearby scales use Cauchy–Schwarz and separated scales use covariance decay.
This module computes the resulting exact row-sum constant.
-/

set_option autoImplicit false
noncomputable section
namespace HigherDimLQGMetric

def blockCorrCoeff (C q : ℝ) (k₀ k : ℕ) : ℝ :=
  if k < k₀ then 1 else C * q ^ k

theorem blockCorrCoeff_nonneg {C q : ℝ} (hC : 0 ≤ C) (hq : 0 ≤ q)
    (k₀ k : ℕ) : 0 ≤ blockCorrCoeff C q k₀ k := by
  unfold blockCorrCoeff
  split_ifs <;> positivity

theorem blockCorrCoeff_summable {C q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1)
    (k₀ : ℕ) : Summable (blockCorrCoeff C q k₀) := by
  apply (summable_nat_add_iff k₀).mp
  have heq : (fun n => blockCorrCoeff C q k₀ (n + k₀)) =
      (fun n => (C * q ^ k₀) * q ^ n) := by
    funext n
    simp only [blockCorrCoeff, not_lt.mpr (Nat.le_add_left k₀ n), ite_false]
    rw [show n + k₀ = k₀ + n by omega, pow_add]
    ring
  rw [heq]
  exact (summable_geometric_of_lt_one hq hq1).mul_left _

theorem blockCorrCoeff_tsum_tail {C q : ℝ} (hq : 0 ≤ q) (hq1 : q < 1)
    {k₀ : ℕ} (hk₀ : 1 ≤ k₀) :
    (∑' k : ℕ, blockCorrCoeff C q k₀ (k + 1)) =
      (k₀ - 1 : ℕ) + C * q ^ k₀ / (1 - q) := by
  let f : ℕ → ℝ := fun k => blockCorrCoeff C q k₀ (k + 1)
  have hsf : Summable f := (summable_nat_add_iff 1).mpr
    (blockCorrCoeff_summable hq hq1 k₀)
  have hsplit := hsf.sum_add_tsum_nat_add (k₀ - 1)
  have hfront : (∑ k ∈ Finset.range (k₀ - 1), f k) =
      (k₀ - 1 : ℕ) := by
    have heq : ∀ k ∈ Finset.range (k₀ - 1), f k = 1 := by
      intro k hk
      dsimp [f, blockCorrCoeff]
      split_ifs with h
      · rfl
      · have hk' := Finset.mem_range.mp hk
        omega
    simp_rw [Finset.sum_congr rfl heq]
    simp
  have htail : (∑' k : ℕ, f (k + (k₀ - 1))) =
      C * q ^ k₀ / (1 - q) := by
    have heq : (fun k => f (k + (k₀ - 1))) =
        (fun k => (C * q ^ k₀) * q ^ k) := by
      funext k
      dsimp [f, blockCorrCoeff]
      have hk : ¬k + (k₀ - 1) + 1 < k₀ := by omega
      simp only [hk, ite_false]
      rw [show k + (k₀ - 1) + 1 = k₀ + k by omega, pow_add]
      ring
    rw [heq, tsum_mul_left, tsum_geometric_of_lt_one hq hq1]
    ring
  rw [hfront, htail] at hsplit
  linarith

theorem blockCorrCoeff_schur {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {n : ℕ} (Y : Fin n → H)
    {C q : ℝ} (hC : 0 ≤ C) (hq : 0 ≤ q) (hq1 : q < 1)
    {k₀ : ℕ} (hk₀ : 1 ≤ k₀)
    (hcorr : ∀ i j : Fin n,
      |inner ℝ (Y i) (Y j)| ≤
        blockCorrCoeff C q k₀ (Nat.dist (i : ℕ) (j : ℕ)) *
          (‖Y i‖ * ‖Y j‖)) :
    ‖∑ i, Y i‖ ^ 2 ≤
      ((2 * k₀ - 1 : ℝ) + 2 * C * q ^ k₀ / (1 - q)) *
        ∑ i, ‖Y i‖ ^ 2 := by
  have hs := norm_sum_sq_le_of_corr Y (blockCorrCoeff C q k₀)
    (blockCorrCoeff_nonneg hC hq k₀)
    (blockCorrCoeff_summable hq hq1 k₀) hcorr
  have hzero : blockCorrCoeff C q k₀ 0 = 1 := by
    simp [blockCorrCoeff, show 0 < k₀ by omega]
  rw [hzero, blockCorrCoeff_tsum_tail hq hq1 hk₀] at hs
  convert hs using 1
  congr 1
  have hnat : (k₀ - 1 : ℕ) + 1 = k₀ := Nat.sub_add_cancel hk₀
  have hcast : (↑(k₀ - 1) : ℝ) = (k₀ : ℝ) - 1 := by
    rw [Nat.cast_sub hk₀, Nat.cast_one]
  rw [hcast]
  ring

end HigherDimLQGMetric
namespace HigherDimLQGMetric

theorem blockCorrCoeff_coordinate_bound {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] {n : ℕ} (m : Fin n → ℕ)
    (X : ∀ i : Fin n, Fin (m i) → H)
    (horth : ∀ i, Orthonormal ℝ (X i))
    (w : ∀ i : Fin n, Fin (m i) → ℝ)
    {C q : ℝ} (hC : 0 ≤ C) (hq : 0 ≤ q) (hq1 : q < 1)
    {k₀ : ℕ} (hk₀ : 1 ≤ k₀)
    (hcorr : ∀ i j : Fin n,
      |inner ℝ (∑ k, w i k • X i k) (∑ k, w j k • X j k)| ≤
        blockCorrCoeff C q k₀ (Nat.dist (i : ℕ) (j : ℕ)) *
          (‖∑ k, w i k • X i k‖ * ‖∑ k, w j k • X j k‖)) :
    ‖∑ i : Fin n, ∑ k : Fin (m i), w i k • X i k‖ ^ 2 ≤
      ((2 * k₀ - 1 : ℝ) + 2 * C * q ^ k₀ / (1 - q)) *
        ∑ i : Fin n, ∑ k : Fin (m i), (w i k) ^ 2 := by
  let Y : Fin n → H := fun i => ∑ k, w i k • X i k
  have hn (i : Fin n) : ‖Y i‖ ^ 2 = ∑ k : Fin (m i), (w i k) ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simpa only [Y, RCLike.conj_to_real, pow_two] using
      (horth i).inner_sum (w i) (w i) Finset.univ
  have hs := blockCorrCoeff_schur Y hC hq hq1 hk₀ hcorr
  simpa only [Y, hn] using hs

end HigherDimLQGMetric
