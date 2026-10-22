import HigherDimLQGContinuity.Improve.Net

/-!
# Pair count for the source net
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

open HigherDimLFPP (Rd)

/-- The square of the net size has the expected `t ^ (-2d)` bound. -/
theorem q11_net_pair_count {d : ℕ} (hd : 1 ≤ d) {t : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (N : Finset (Rd d))
    (hN : (N.card : ℝ) ≤ (8 * Real.sqrt d / t + 1) ^ d) :
    ((N.card * N.card : ℕ) : ℝ) ≤
      (9 * Real.sqrt d / t) ^ (2 * d) := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hroot : 1 ≤ Real.sqrt (d : ℝ) := by
    simpa using Real.sqrt_le_sqrt hdR
  have hunit : 1 ≤ Real.sqrt (d : ℝ) / t := by
    apply (le_div_iff₀ ht).2
    linarith
  have hlinear : 8 * Real.sqrt (d : ℝ) / t + 1 ≤
      9 * Real.sqrt d / t := by
    rw [mul_div_assoc, mul_div_assoc]
    linarith only [hunit]
  have hbase : 0 ≤ 9 * Real.sqrt (d : ℝ) / t := by positivity
  have hcard : (N.card : ℝ) ≤ (9 * Real.sqrt d / t) ^ d := by
    exact hN.trans (by gcongr)
  calc
    ((N.card * N.card : ℕ) : ℝ) = (N.card : ℝ) ^ (2 : ℕ) := by
      simp only [Nat.cast_mul, pow_two]
    _ ≤ ((9 * Real.sqrt d / t) ^ d) ^ (2 : ℕ) := by gcongr
    _ = (9 * Real.sqrt d / t) ^ (2 * d) := by rw [← pow_mul]; congr 1; omega

end HigherDimLQGContinuity
