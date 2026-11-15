/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import MathFin.Probability.Brownian.QuadraticVariationL2
import MathFin.Probability.Brownian.Ito.ItoIsometryAdapted
import InteractingSLE.Stochastic.LocalTime.Grid

/-!
# Moments of Brownian increments on a uniform grid

Packet PROVE-TANAKA. For a pre-Brownian `B` and the uniform partition `t_k` of `[s, t]` into `n`
cells of length `h = (t - s)/n`:

* `integrable_increment_pow`: every power of an increment is integrable;
* `integral_sum_increment_sq`: `E ∑ (ΔB_k)² = n h`;
* `integral_sum_increment_pow4`: `E ∑ (ΔB_k)⁴ = 3 n h²` (from MathFin's
  `QuadraticVariationL2.integral_increment_pow4`), which tends to `0`;
* elementary inequalities `abs_le_add_pow4`, `sq_le_add_pow4`, `mul_sq_le_pow4_add` that bound a
  single increment, or an increment on a "bad" event, by the fourth-power sum.

The maximal increment is never formed: every use bounds one increment (selected by nonnegative
weights of total mass at most one) by `η + ∑ (ΔB_k)⁴ / η³`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set MathFin
open scoped NNReal Topology

namespace InteractingSLE.LocalTime

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-! ### Elementary inequalities -/

lemma abs_le_add_pow4 {η : ℝ} (hη : 0 < η) (x : ℝ) : |x| ≤ η + x ^ 4 / η ^ 3 := by
  have h4 : 0 ≤ x ^ 4 / η ^ 3 := by positivity
  rcases le_or_gt |x| η with h | h
  · linarith
  · have hx3 : η ^ 3 ≤ |x| ^ 3 := pow_le_pow_left₀ hη.le h.le 3
    have : |x| ≤ x ^ 4 / η ^ 3 := by
      have hx4 : x ^ 4 = |x| * |x| ^ 3 := by
        rw [show |x| * |x| ^ 3 = |x| ^ 4 by ring, pow_abs,
          abs_of_nonneg (by positivity : (0 : ℝ) ≤ x ^ 4)]
      rw [le_div_iff₀ (by positivity), hx4]
      exact mul_le_mul_of_nonneg_left hx3 (abs_nonneg x)
    linarith

lemma sq_le_add_pow4 {η : ℝ} (hη : 0 < η) (x : ℝ) : x ^ 2 ≤ η ^ 2 + x ^ 4 / η ^ 2 := by
  have h4 : 0 ≤ x ^ 4 / η ^ 2 := by positivity
  rcases le_or_gt (x ^ 2) (η ^ 2) with h | h
  · linarith
  · have : x ^ 2 ≤ x ^ 4 / η ^ 2 := by
      rw [le_div_iff₀ (by positivity), show x ^ 4 = x ^ 2 * x ^ 2 by ring]
      exact mul_le_mul_of_nonneg_left h.le (by positivity)
    have : 0 ≤ η ^ 2 := by positivity
    linarith

/-- `y x² ≤ x⁴ / c + c y` for `0 ≤ y ≤ 1` and `c > 0`. -/
lemma mul_sq_le_pow4_add {c y : ℝ} (hc : 0 < c) (hy0 : 0 ≤ y) (hy1 : y ≤ 1) (x : ℝ) :
    y * x ^ 2 ≤ x ^ 4 / c + c * y := by
  have h4 : 0 ≤ x ^ 4 / c := by positivity
  rcases le_or_gt (x ^ 2) c with h | h
  · nlinarith
  · have : x ^ 2 ≤ x ^ 4 / c := by
      rw [le_div_iff₀ hc, show x ^ 4 = x ^ 2 * x ^ 2 by ring]
      exact mul_le_mul_of_nonneg_left h.le (by positivity)
    have : y * x ^ 2 ≤ x ^ 2 := mul_le_of_le_one_left (by positivity) hy1
    nlinarith

/-- With nonnegative weights of total mass at most one, `∑ w_k |x_k| ≤ η + ∑ x_k⁴ / η³`. -/
lemma sum_weight_abs_le {η : ℝ} (hη : 0 < η) {n : ℕ} {w x : ℕ → ℝ} (hw : ∀ k, 0 ≤ w k)
    (hw1 : ∑ k ∈ Finset.range n, w k ≤ 1) :
    ∑ k ∈ Finset.range n, w k * |x k| ≤ η + (∑ k ∈ Finset.range n, x k ^ 4) / η ^ 3 := by
  set Q := η + (∑ k ∈ Finset.range n, x k ^ 4) / η ^ 3
  have hQ : ∀ k ∈ Finset.range n, |x k| ≤ Q := fun k hk => by
    refine (abs_le_add_pow4 hη (x k)).trans ?_
    simp only [Q]
    gcongr
    exact Finset.single_le_sum (f := fun k => x k ^ 4) (fun _ _ => by positivity) hk
  have hQ0 : 0 ≤ Q := by positivity
  calc ∑ k ∈ Finset.range n, w k * |x k| ≤ ∑ k ∈ Finset.range n, w k * Q :=
        Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left (hQ k hk) (hw k)
    _ = (∑ k ∈ Finset.range n, w k) * Q := by rw [Finset.sum_mul]
    _ ≤ 1 * Q := by gcongr
    _ = Q := one_mul Q

/-- With nonnegative weights of total mass at most one, `∑ w_k x_k² ≤ η² + ∑ x_k⁴ / η²`. -/
lemma sum_weight_sq_le {η : ℝ} (hη : 0 < η) {n : ℕ} {w x : ℕ → ℝ} (hw : ∀ k, 0 ≤ w k)
    (hw1 : ∑ k ∈ Finset.range n, w k ≤ 1) :
    ∑ k ∈ Finset.range n, w k * x k ^ 2 ≤ η ^ 2 + (∑ k ∈ Finset.range n, x k ^ 4) / η ^ 2 := by
  set Q := η ^ 2 + (∑ k ∈ Finset.range n, x k ^ 4) / η ^ 2
  have hQ : ∀ k ∈ Finset.range n, x k ^ 2 ≤ Q := fun k hk => by
    refine (sq_le_add_pow4 hη (x k)).trans ?_
    simp only [Q]
    gcongr
    exact Finset.single_le_sum (f := fun k => x k ^ 4) (fun _ _ => by positivity) hk
  have hQ0 : 0 ≤ Q := by positivity
  calc ∑ k ∈ Finset.range n, w k * x k ^ 2 ≤ ∑ k ∈ Finset.range n, w k * Q :=
        Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_left (hQ k hk) (hw k)
    _ = (∑ k ∈ Finset.range n, w k) * Q := by rw [Finset.sum_mul]
    _ ≤ 1 * Q := by gcongr
    _ = Q := one_mul Q

/-! ### Moments -/

lemma integrable_increment_pow (hB : IsPreBrownianReal B μ) (t₀ t₁ : ℝ≥0) {p : ℕ}
    (hp : p ≠ 0) : Integrable (fun ω => (B t₁ ω - B t₀ ω) ^ p) μ := by
  have hm : MemLp (fun ω => B t₁ ω - B t₀ ω) p μ :=
    (hB.hasLaw_sub t₁ t₀).memLp (memLp_id_gaussianReal p)
  refine (hm.integrable_norm_pow hp).mono' (hm.1.pow p) (Eventually.of_forall fun ω => ?_)
  simp [norm_pow]

lemma integrable_increment (hB : IsPreBrownianReal B μ) (t₀ t₁ : ℝ≥0) :
    Integrable (fun ω => B t₁ ω - B t₀ ω) μ := by
  simpa using integrable_increment_pow hB t₀ t₁ one_ne_zero

lemma integral_sum_increment_sq (hB : IsPreBrownianReal B μ) {s t : ℝ≥0} (hst : s ≤ t)
    (n : ℕ) :
    ∫ ω, ∑ k ∈ Finset.range n, (B (unifPartIcc s t n (k + 1)) ω - B (unifPartIcc s t n k) ω) ^ 2
      ∂μ = n * (((t : ℝ) - s) / n) := by
  rw [integral_finsetSum _ fun k _ => integrable_increment_pow hB _ _ two_ne_zero]
  have : ∀ k ∈ Finset.range n, ∫ ω, (B (unifPartIcc s t n (k + 1)) ω -
      B (unifPartIcc s t n k) ω) ^ 2 ∂μ = ((t : ℝ) - s) / n := fun k _ => by
    rw [ItoIsometryAdapted.integral_increment_sq hB (unifPartIcc_mono s t n (Nat.le_succ k)),
      unifPartIcc_succ_sub hst]
  rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

lemma integral_sum_increment_pow4 (hB : IsPreBrownianReal B μ) {s t : ℝ≥0} (hst : s ≤ t)
    (n : ℕ) :
    ∫ ω, ∑ k ∈ Finset.range n, (B (unifPartIcc s t n (k + 1)) ω - B (unifPartIcc s t n k) ω) ^ 4
      ∂μ = n * (3 * (((t : ℝ) - s) / n) ^ 2) := by
  rw [integral_finsetSum _ fun k _ => integrable_increment_pow hB _ _ (by norm_num)]
  have : ∀ k ∈ Finset.range n, ∫ ω, (B (unifPartIcc s t n (k + 1)) ω -
      B (unifPartIcc s t n k) ω) ^ 4 ∂μ = 3 * (((t : ℝ) - s) / n) ^ 2 := fun k _ => by
    rw [QuadraticVariationL2.integral_increment_pow4 hB (unifPartIcc_mono s t n (Nat.le_succ k)),
      unifPartIcc_succ_sub hst]
  rw [Finset.sum_congr rfl this, Finset.sum_const, Finset.card_range, nsmul_eq_mul]

lemma tendsto_integral_sum_increment_pow4 (hB : IsPreBrownianReal B μ) {s t : ℝ≥0}
    (hst : s ≤ t) :
    Tendsto (fun n : ℕ => ∫ ω, ∑ k ∈ Finset.range n,
      (B (unifPartIcc s t n (k + 1)) ω - B (unifPartIcc s t n k) ω) ^ 4 ∂μ) atTop (𝓝 0) := by
  have h : ∀ᶠ n : ℕ in atTop, n * (3 * (((t : ℝ) - s) / n) ^ 2) = 3 * ((t : ℝ) - s) ^ 2 / n := by
    filter_upwards [eventually_ne_atTop 0] with n hn
    field_simp
  refine (Filter.Tendsto.congr' (EventuallyEq.symm ?_)
    (tendsto_const_div_atTop_nhds_zero_nat (3 * ((t : ℝ) - s) ^ 2)))
  filter_upwards [h] with n hn
  rw [integral_sum_increment_pow4 hB hst, hn]

end InteractingSLE.LocalTime
