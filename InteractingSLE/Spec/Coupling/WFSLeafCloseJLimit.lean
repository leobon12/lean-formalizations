/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafCloseJMaximal

/-!
# Locally uniform limits from geometric consecutive errors

The scalar limit is the pointwise `limUnder` of the approximating processes.
Eventual geometric bounds on every integer horizon imply locally uniform
convergence and continuity, using Mathlib's geometric Cauchy estimate.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.WFS

/-- Eventual geometric control on each compact interval makes the pointwise
limit continuous. No stochastic regularity assumption is used here. -/
theorem continuous_limUnder_of_local_geometric
    {f : ℕ → ℝ≥0 → ℝ} (hc : ∀ n, Continuous (f n))
    (hstep : ∀ N : ℕ, ∀ᶠ n in atTop, ∀ t : ℝ≥0, t ≤ N →
      dist (f n t) (f (n + 1) t) ≤ (1 / 2 : ℝ) ^ n) :
    Continuous (fun t => limUnder atTop fun n => f n t) ∧
      ∀ t, Tendsto (fun n => f n t) atTop (𝓝 (limUnder atTop fun n => f n t)) := by
  let g (t : ℝ≥0) : ℝ := limUnder atTop fun n => f n t
  have ht (t : ℝ≥0) : Tendsto (fun n => f n t) atTop (𝓝 (g t)) := by
    obtain ⟨T, hT⟩ := exists_nat_ge t
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hstep T)
    have hsum : Summable (fun n => dist (f n t) (f (n + 1) t)) := by
      rw [← summable_nat_add_iff N]
      refine Summable.of_nonneg_of_le (fun _ => dist_nonneg)
        (fun n => hN (n + N) (Nat.le_add_left N n) t hT) ?_
      simp_rw [pow_add]
      exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_right _
    exact (cauchySeq_of_summable_dist hsum).tendsto_limUnder
  have hcont (T : ℕ) : ContinuousOn g (Iic (T : ℝ≥0)) := by
    obtain ⟨N, hN⟩ := eventually_atTop.1 (hstep T)
    have hu : TendstoUniformlyOn f g atTop (Iic (T : ℝ≥0)) := by
      rw [Metric.tendstoUniformlyOn_iff]
      intro ε hε
      have hzero : Tendsto (fun n => 2 * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
        simpa only [mul_zero] using
          (tendsto_pow_atTop_nhds_zero_of_lt_one
            (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).const_mul (2 : ℝ)
      filter_upwards [eventually_ge_atTop N, hzero.eventually_lt_const hε] with n hn hεn
      intro t htT
      have hs (k : ℕ) :
          dist (f (k + n) t) (f (k + 1 + n) t) ≤ (1 / 2 : ℝ) ^ n * (1 / 2 : ℝ) ^ k := by
        rw [show k + 1 + n = (k + n) + 1 from by omega]
        calc
          _ ≤ (1 / 2 : ℝ) ^ (k + n) :=
            hN (k + n) (hn.trans (Nat.le_add_left n k)) t htT
          _ = _ := by rw [pow_add, mul_comm]
      have he := dist_le_of_le_geometric_of_tendsto₀ (1 / 2) ((1 / 2 : ℝ) ^ n)
        (by norm_num) hs ((ht t).comp (tendsto_add_atTop_nat n))
      simp only [zero_add] at he
      rw [dist_comm]
      exact (he.trans_eq (by ring)).trans_lt hεn
    exact hu.continuousOn (Eventually.of_forall fun n => (hc n).continuousOn).frequently
  refine ⟨continuous_iff_continuousAt.2 (fun t => ?_), ht⟩
  obtain ⟨N, hN⟩ := exists_nat_gt t
  exact (hcont N t hN.le).continuousAt (Iic_mem_nhds hN)

end InteractingSLE.WFS
