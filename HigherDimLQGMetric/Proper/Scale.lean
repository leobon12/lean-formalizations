import HigherDimLQGMetric.Proper.Normalize
import HigherDimLQGMetric.Sphere.Var
import Mathlib.Probability.Moments.Variance

/-!
# The large-scale sphere-average increment is negligible compared with logarithmic drift

Chebyshev suffices here: its variance is `log t + O(1)`, whereas the deterministic
drift of the sharp normalizer is proportional to `log t`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
  [IsProbabilityMeasure P] (h : Ω → DistRd d)

/-- Chebyshev bound uniform in the base radius. -/
theorem proper_exists_increment_bound (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P)
    {Q : ℝ} (hQ : 0 < Q) :
    ∃ K : ℝ, ∀ n : ℕ, 0 < n → ∀ R : ℝ, 0 < R →
      P {ω | Q / 2 * n ≤ sphereAvg (h ω) R 0 -
        sphereAvg (h ω) (Real.exp n * R) 0} ≤
        ENNReal.ofReal (((n : ℝ) + K) / (Q / 2 * n) ^ 2) := by
  obtain ⟨K, hK⟩ := exists_abs_variance_sphereAvg_sub_sub_log_le hd 0
  refine ⟨K, fun n hn R hR => ?_⟩
  let X : Ω → ℝ := fun ω => sphereAvg (h ω) R 0 -
    sphereAvg (h ω) (Real.exp n * R) 0
  have he : 0 < Real.exp (n : ℝ) := Real.exp_pos _
  have hbig : 0 < Real.exp (n : ℝ) * R := mul_pos he hR
  have hrbig : R ≤ Real.exp (n : ℝ) * R := by
    have hE : 1 ≤ Real.exp (n : ℝ) := by
      have := Real.add_one_le_exp (n : ℝ)
      have : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
      linarith
    nlinarith
  have hvar := hK hh hR hrbig (0 : Rd d) 0 (by simp)
  have hlog : Real.log ((Real.exp (n : ℝ) * R) / R) = (n : ℝ) := by
    rw [mul_div_cancel_right₀ _ hR.ne', Real.log_exp]
  rw [hlog] at hvar
  have hvar' : Var[X; P] ≤ (n : ℝ) + K := by
    dsimp [X]
    linarith [le_abs_self (Var[(fun ω => sphereAvg (h ω) R 0 -
      sphereAvg (h ω) (Real.exp n * R) 0); P] - n)]
  have hgauss := hh.hasGaussianLaw_sphereAvg_sub hd hR hbig (0 : Rd d) 0
  have hX : MemLp X 2 P := hgauss.1.memLp_two
  have hc : 0 < Q / 2 * (n : ℝ) := by
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    positivity
  calc
    P {ω | Q / 2 * n ≤ X ω}
        ≤ P {ω | Q / 2 * n ≤ |X ω - P[X]|} := by
          refine measure_mono fun ω hω => ?_
          change Q / 2 * n ≤ |X ω - P[X]|
          have hmean : P[X] = 0 := hgauss.2
          rw [hmean, sub_zero]
          exact hω.trans (le_abs_self (X ω))
    _ ≤ ENNReal.ofReal (Var[X; P] / (Q / 2 * n) ^ 2) :=
      meas_ge_le_variance_div_sq hX hc
    _ ≤ ENNReal.ofReal (((n : ℝ) + K) / (Q / 2 * n) ^ 2) := by
      exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hvar' (sq_nonneg _))

/-- The Chebyshev bound tends to zero at an integer sequence of logarithmic scales. -/
theorem proper_ratio_tendsto_zero {Q : ℝ} (hQ : 0 < Q) (K : ℝ) :
    Tendsto (fun n : ℕ => (((n : ℝ) + 1) + K) /
      (Q / 2 * ((n : ℝ) + 1)) ^ 2) atTop (𝓝 0) := by
  have hrec : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hsum : Tendsto (fun n : ℕ =>
      (1 : ℝ) / ((n : ℝ) + 1) + K * ((1 : ℝ) / ((n : ℝ) + 1)) ^ 2)
      atTop (𝓝 0) := by
    simpa only [mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero] using
      hrec.add (tendsto_const_nhds.mul (hrec.pow 2))
  have hlim : Tendsto (fun n : ℕ =>
      (4 / Q ^ 2) * ((1 : ℝ) / ((n : ℝ) + 1) +
        K * ((1 : ℝ) / ((n : ℝ) + 1)) ^ 2)) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_const_nhds.mul hsum : Tendsto _ _ _)
  convert hlim using 1
  · funext n
    have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
    have hQ' : Q ≠ 0 := hQ.ne'
    field_simp
    ring

/-- Given a desired growth factor and failure probability, choose one large logarithmic scale.
The choice is uniform in the base radius. -/
theorem proper_exists_large_step (hd : 2 ≤ d) (hh : IsWholeSpaceLGF h P)
    {ξ Q : ℝ} (hξ : 0 < ξ) (hQ : 0 < Q)
    {a B ε : ℝ} (ha : 0 < a) (hε : 0 < ε) (tMin : ℝ) :
    ∃ n : ℕ, 0 < n ∧ tMin < Real.exp n ∧
      B < a * Real.exp (ξ * Q / 2 * n) ∧
      ∀ R : ℝ, 0 < R →
        P {ω | Q / 2 * n ≤ sphereAvg (h ω) R 0 -
          sphereAvg (h ω) (Real.exp n * R) 0} < ENNReal.ofReal ε := by
  obtain ⟨K, hK⟩ := proper_exists_increment_bound P h hd hh hQ
  have hratio := proper_ratio_tendsto_zero hQ K
  have hsmall : ∀ᶠ n : ℕ in atTop,
      (((n : ℝ) + 1) + K) / (Q / 2 * ((n : ℝ) + 1)) ^ 2 < ε :=
    hratio.eventually (Iio_mem_nhds hε)
  have hcoef : 0 < ξ * Q / 2 := by positivity
  have hshift : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hscaled : Tendsto (fun n : ℕ => ξ * Q / 2 * ((n : ℝ) + 1)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hcoef hshift
  have hexp : Tendsto (fun n : ℕ => Real.exp (ξ * Q / 2 * ((n : ℝ) + 1)))
      atTop atTop := Real.tendsto_exp_atTop.comp hscaled
  have hlarge : Tendsto (fun n : ℕ =>
      a * Real.exp (ξ * Q / 2 * ((n : ℝ) + 1))) atTop atTop := by
    exact Filter.Tendsto.const_mul_atTop ha hexp
  have hbig : ∀ᶠ n : ℕ in atTop,
      B < a * Real.exp (ξ * Q / 2 * ((n : ℝ) + 1)) :=
    hlarge.eventually_gt_atTop B
  have hbase : Tendsto (fun n : ℕ => Real.exp ((n : ℝ) + 1)) atTop atTop :=
    Real.tendsto_exp_atTop.comp hshift
  have ht : ∀ᶠ n : ℕ in atTop, tMin < Real.exp ((n : ℝ) + 1) :=
    hbase.eventually_gt_atTop tMin
  obtain ⟨n, hnsmall, hnbig, hnt⟩ := (hsmall.and (hbig.and ht)).exists
  refine ⟨n + 1, Nat.succ_pos _, ?_, ?_, ?_⟩
  · simpa only [Nat.cast_add, Nat.cast_one] using hnt
  · simpa only [Nat.cast_add, Nat.cast_one] using hnbig
  · intro R hR
    have hb := hK (n + 1) (Nat.succ_pos _) R hR
    exact hb.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hε).2 (by
      simpa only [Nat.cast_add, Nat.cast_one] using hnsmall))

end HigherDimLQGMetric
