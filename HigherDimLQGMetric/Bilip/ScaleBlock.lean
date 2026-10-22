import HigherDimLQGMetric.Bilip.CompareCover
import HigherDimLQGMetric.Sharp.ScaleIndices

/-! Every fifth dyadic radius gives disjoint observation shells of ratio `1/32`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGMetric

private theorem bilip_half_pow_antitone :
    Antitone (fun k : ℕ => (1 / 2 : ℝ) ^ k) := by
  intro i j hij
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hij

theorem bilip_exists_sparse_block {ε : ℝ} (hε0 : 0 < ε)
    (hε64 : ε < 1 / 64) :
    ∃ k N : ℕ, 0 < N ∧ k ≤ 5 * N + 5 ∧
      (1 / 2 : ℝ) ^ k < ε ∧
      ∀ i < N, ε ^ 2 ≤ (1 / 2 : ℝ) ^ (k + 5 * i) ∧
        (1 / 2 : ℝ) ^ (k + 5 * i) ≤ ε := by
  obtain ⟨k, n, hnk, hn, hk, -, hblock⟩ :=
    exists_dyadic_block hε0 (by linarith : ε < 1 / 8)
  have hk7 : 7 ≤ k := by
    by_contra hnot
    have hk6 : k ≤ 6 := by omega
    have hp := bilip_half_pow_antitone hk6
    norm_num at hp
    linarith
  let N := n / 5
  have hN : 0 < N := by dsimp [N]; omega
  have hkle : k ≤ 5 * N + 5 := by dsimp [N]; omega
  refine ⟨k, N, hN, hkle, hk, ?_⟩
  intro i hi
  have hidx : 5 * i < n := by dsimp [N] at hi; omega
  exact hblock (5 * i) hidx

/-- The sparse-shell tail converts to a polynomial mesh bound. -/
theorem bilip_exp_sparse_bound {ε : ℝ} (_hε : 0 < ε)
    {k N m : ℕ} (hk : k ≤ 5 * N + 5)
    (hpow : (1 / 2 : ℝ) ^ k < ε) :
    Real.exp (-((5 * m : ℕ) : ℝ) * Real.log 2 * N) ≤
      (2 : ℝ) ^ (5 * m) * ε ^ m := by
  have hlog : Real.exp (-Real.log 2) = (1 / 2 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num)]
    norm_num
  have heq : Real.exp (-((5 * m : ℕ) : ℝ) * Real.log 2 * N) =
      ((1 / 2 : ℝ) ^ (5 * N)) ^ m := by
    calc
      Real.exp (-((5 * m : ℕ) : ℝ) * Real.log 2 * N) =
          Real.exp (((5 * N * m : ℕ) : ℝ) * (-Real.log 2)) := by
            congr 1
            push_cast
            ring
      _ = (Real.exp (-Real.log 2)) ^ (5 * N * m) := Real.exp_nat_mul _ _
      _ = (1 / 2 : ℝ) ^ (5 * N * m) := by rw [hlog]
      _ = ((1 / 2 : ℝ) ^ (5 * N)) ^ m := by rw [← pow_mul]
  have hsmall : (1 / 2 : ℝ) ^ (5 * N) ≤ (2 : ℝ) ^ 5 * ε := by
    have hp : (1 / 2 : ℝ) ^ (5 * N + 5) ≤ (1 / 2 : ℝ) ^ k :=
      bilip_half_pow_antitone hk
    have hq : (1 / 2 : ℝ) ^ (5 * N) =
        (2 : ℝ) ^ 5 * (1 / 2 : ℝ) ^ (5 * N + 5) := by
      rw [pow_add]
      norm_num
      ring
    rw [hq]
    exact (mul_le_mul_of_nonneg_left hp (by positivity)).trans
      (mul_le_mul_of_nonneg_left hpow.le (by positivity))
  rw [heq]
  calc
    ((1 / 2 : ℝ) ^ (5 * N)) ^ m ≤ ((2 : ℝ) ^ 5 * ε) ^ m :=
      pow_le_pow_left₀ (by positivity) hsmall m
    _ = (2 : ℝ) ^ (5 * m) * ε ^ m := by rw [mul_pow, pow_mul]

end HigherDimLQGMetric
