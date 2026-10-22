import HigherDimLQGMetric.Growth.BC

/-!
# Gaussian tails at dyadic large radii

Packet L2a, Lemma 2.14: the centre value at radius `2^k` has variance at most linear
in `k`, so its square-root-logarithm threshold has an inverse-square tail.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric Filter Topology

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

theorem l2a_exists_large_point_tail (hd : 2 ≤ d) :
    ∃ M : ℝ, 0 < M ∧ ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
      {h : Ω → DistRd d}, IsWholeSpaceLGF h P → ∀ k : ℕ,
        P.real {ω | Real.sqrt (4 * M * ((k : ℝ) + 1) *
          Real.log ((k : ℝ) + 1)) ≤
          |sphereAvg (h ω) ((2 : ℝ) ^ k) 0 - sphereAvg (h ω) 1 0|} ≤
          2 * (((k : ℝ) + 1) ^ 2)⁻¹ := by
  obtain ⟨K, hK⟩ := exists_variance_sphereAvg_sub_le hd
  set M : ℝ := 2 + |K| with hM
  have hM0 : 0 < M := by positivity
  refine ⟨M, hM0, fun {Ω} _ {P} {h} hh k => ?_⟩
  have hr : 0 < (2 : ℝ) ^ k := by positivity
  have hr1 : 1 ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have hvar0 := (hK hh hr one_pos (0 : Rd d) 0).2 hr1
  have hlog2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
    linarith
  have hvar : Var[fun ω => sphereAvg (h ω) ((2 : ℝ) ^ k) 0 -
      sphereAvg (h ω) 1 0; P] ≤ M * ((k : ℝ) + 1) - 1 := by
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hKle : K ≤ |K| := le_abs_self K
    simp only [sub_self, norm_zero, zero_div, Real.log_zero, max_self, mul_zero, add_zero,
      div_one, Real.log_pow] at hvar0
    have hmul : (k : ℝ) * Real.log 2 ≤ (k : ℝ) := by nlinarith
    dsimp [M]
    nlinarith [mul_nonneg (abs_nonneg K) hk]
  have hA : 0 ≤ Real.sqrt (4 * M * ((k : ℝ) + 1) *
      Real.log ((k : ℝ) + 1)) := Real.sqrt_nonneg _
  have ht := l2a_point_tail hd hh hr one_pos (0 : Rd d) 0 hvar hA
  rw [sub_add_cancel] at ht
  rw [l2a_exp_point_log hM0 k] at ht
  exact ht

end HigherDimLQGMetric
