/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedLawRemainder
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum

/-!
# Almost sure dyadic error estimates

Packet PROVE-ZHAN-GT4-A22. Summability improves the existing probability
limits to almost sure limits along the entire dyadic sequence. This permits
path-dependent Taylor bounds and countable localization of coefficients.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

open Girsanov

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {B w : ℝ≥0 → Ω → ℝ}

/-- Summable first moments imply almost sure convergence to zero. -/
theorem seed_ae_tendsto_zero_of_summable_integral_norm {f : ℕ → Ω → ℝ}
    (hi : ∀ n, Integrable (f n) P)
    (hs : Summable (fun n => ∫ ω, ‖f n ω‖ ∂P)) :
    ∀ᵐ ω ∂P, Tendsto (fun n => f n ω) atTop (𝓝 0) := by
  have hsum : ∑' n, eLpNorm (f n) 1 P ≠ ∞ := by
    simp_rw [eLpNorm_one_eq_lintegral_enorm,
      ← ofReal_integral_norm_eq_lintegral_enorm (hi _)]
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => integral_nonneg fun _ => norm_nonneg _) hs]
    exact ENNReal.ofReal_ne_top
  filter_upwards [summable_norm_of_tsum_eLpNorm_ne_top (p := 1) le_rfl
    (fun n => (hi n).aestronglyMeasurable) hsum] with ω hω
  exact tendsto_zero_iff_norm_tendsto_zero.2 hω.tendsto_atTop_zero

/-- The cubic errors vanish almost surely, without passage to a subsequence. -/
theorem seedCubicError_tendsto_ae (hB : IsFilteredBrownianReal 𝓕 B P) (t : ℝ≥0) :
    ∀ᵐ ω ∂P, Tendsto (fun n => seedCubicError B n t ω) atTop (𝓝 0) := by
  have hi (n : ℕ) : Integrable (seedCubicError B n t) P :=
    integrable_finsetSum _ fun k _ => hB.integrable_abs_incr_pow
      (min_le_min_right t (grid_mono n (Nat.le_succ k))) 3
  have hpos (n : ℕ) (ω : Ω) : 0 ≤ seedCubicError B n t ω :=
    Finset.sum_nonneg fun _ _ => pow_nonneg (abs_nonneg _) _
  have hrate (n : ℕ) : Real.sqrt ((1 : ℝ) / 2 ^ n) = Real.sqrt (1 / 2) ^ n := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [pow_succ, show (1 : ℝ) / (2 ^ n * 2) = (1 / 2 ^ n) * (1 / 2) by ring,
        Real.sqrt_mul (by positivity), ih, pow_succ]
  have hq : ‖Real.sqrt (1 / 2)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact (Real.sqrt_lt (by norm_num) (by norm_num)).2 (by norm_num)
  apply seed_ae_tendsto_zero_of_summable_integral_norm hi
  apply Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
    (fun n => ?_) ((summable_geometric_of_norm_lt_one hq).mul_left
      (QuantumZipper.gaussianAbsMoment 3 * t))
  simpa only [Real.norm_eq_abs, abs_of_nonneg (hpos _ _), hrate] using
    integral_seedCubicError_le hB n t

/-- The square-integrability bound needed for the quadratic sums. -/
theorem seedQuadraticError_memLp (hB : IsFilteredPreBrownian B 𝓕 P)
    (hw : StronglyAdapted 𝓕 w) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ u ω, |w u ω| ≤ C) (n : ℕ) (t : ℝ≥0) :
    MemLp (seedQuadraticError B w n t) 2 P := by
  unfold seedQuadraticError
  refine memLp_finsetSum _ fun k _ => ?_
  have hY := MathFin.QuadraticVariationL2.memLp_increment_sq_centered_two
    hB.toIsPreBrownianReal (min (grid n k) t) (min (grid n (k + 1)) t)
    (((min (grid n (k + 1)) t : ℝ≥0) : ℝ) - min (grid n k) t)
  exact MemLp.mono (hY.const_mul C)
    (((hw _).mono (𝓕.le _)).aestronglyMeasurable.mul hY.aestronglyMeasurable)
    (Eventually.of_forall fun ω => by
      simp only [Real.norm_eq_abs, abs_mul, abs_of_nonneg hC]
      exact mul_le_mul_of_nonneg_right (hb _ ω) (abs_nonneg _))

/-- Bounded adapted quadratic errors vanish almost surely on the full grid. -/
theorem seedQuadraticError_tendsto_ae (hB : IsFilteredPreBrownian B 𝓕 P)
    (hw : StronglyAdapted 𝓕 w) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ u ω, |w u ω| ≤ C) (t : ℝ≥0) :
    ∀ᵐ ω ∂P, Tendsto (fun n => seedQuadraticError B w n t ω) atTop (𝓝 0) := by
  have hi (n : ℕ) : Integrable (fun ω => seedQuadraticError B w n t ω ^ 2) P := by
    simpa only [Pi.mul_def, sq] using (seedQuadraticError_memLp hB hw hC hb n t).integrable_mul
      (seedQuadraticError_memLp hB hw hC hb n t)
  have hs : Summable (fun n => ∫ ω, ‖seedQuadraticError B w n t ω ^ 2‖ ∂P) := by
    apply Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
      (fun n => ?_) ((summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 2 : ℝ)‖ < 1)).mul_left
        (2 * C ^ 2 * t))
    have heq : (fun ω => ‖seedQuadraticError B w n t ω ^ 2‖) =
        fun ω => seedQuadraticError B w n t ω ^ 2 :=
      funext fun ω => Real.norm_of_nonneg (sq_nonneg _)
    rw [heq]
    simpa only [div_pow, one_pow, div_eq_mul_inv, one_mul, inv_pow] using
      integral_sq_seedQuadraticError_le hB hw hC hb n t
  filter_upwards [seed_ae_tendsto_zero_of_summable_integral_norm hi hs] with ω hω
  apply tendsto_zero_iff_norm_tendsto_zero.2
  simpa only [Real.sqrt_zero, Real.sqrt_sq_eq_abs, Real.norm_eq_abs] using hω.sqrt

end InteractingSLE.ZhanGT4
