/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedLawQuadratic

/-!
# The dyadic quadratic error tends to zero

Packet PROVE-ZHAN-GT4-A22. These are the clamped partitions used by
`Girsanov.stochIntegral`, with the original Brownian filtration.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

open Girsanov

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {B w : ℝ≥0 → Ω → ℝ}

/-- The weighted centered quadratic error on the clamped dyadic grid. -/
def seedQuadraticError (B w : ℝ≥0 → Ω → ℝ) (n : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range (cells n), w (min (grid n k) t) ω *
    ((B (min (grid n (k + 1)) t) ω - B (min (grid n k) t) ω) ^ 2 -
      ((min (grid n (k + 1)) t : ℝ) - (min (grid n k) t : ℝ)))

/-- Every clamped grid cell has length at most the dyadic mesh. -/
theorem seed_grid_sub_le (n k : ℕ) (t : ℝ≥0) :
    (min (grid n (k + 1)) t : ℝ) - min (grid n k) t ≤ 1 / 2 ^ n := by
  have hg : (grid n (k + 1) : ℝ) - grid n k = 1 / 2 ^ n := by
    simp only [coe_grid, Nat.cast_add, Nat.cast_one]
    ring
  simp only [NNReal.coe_min]
  rw [← hg]
  rcases le_total (grid n (k + 1) : ℝ) t with h | h
  · have hk : (grid n k : ℝ) ≤ grid n (k + 1) := by
      exact_mod_cast grid_mono n (Nat.le_succ k)
    rw [min_eq_left h, min_eq_left (hk.trans h)]
  · rw [min_eq_right h]
    rcases le_total (grid n k : ℝ) t with hk | hk
    · rw [min_eq_left hk]; linarith
    · rw [min_eq_right hk]; linarith [show (grid n k : ℝ) ≤ grid n (k + 1) by
        exact_mod_cast grid_mono n (Nat.le_succ k)]

/-- The variance rate is `2 C² t / 2ⁿ`, also for the final partial cell. -/
theorem integral_sq_seedQuadraticError_le (hB : IsFilteredPreBrownian B 𝓕 P)
    (hw : StronglyAdapted 𝓕 w) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ u ω, |w u ω| ≤ C) (n : ℕ) (t : ℝ≥0) :
    ∫ ω, seedQuadraticError B w n t ω ^ 2 ∂P ≤ 2 * C ^ 2 * t / 2 ^ n := by
  let π : ℕ → ℝ≥0 := fun k => min (grid n k) t
  have hπ : Monotone π := fun i j hij => min_le_min_right t (grid_mono n hij)
  have hh := integral_sq_seed_quadratic_le hB hπ (fun k => (hw (π k)).measurable)
    hC (fun k ω => hb (π k) ω) (cells n)
  change (∫ ω, seedQuadraticError B w n t ω ^ 2 ∂P) ≤ _ at hh
  refine hh.trans ?_
  have hstep (k : ℕ) : C ^ 2 * (2 * ((π (k + 1) : ℝ) - π k) ^ 2) ≤
      (2 * C ^ 2 / 2 ^ n) * ((π (k + 1) : ℝ) - π k) := by
    have h0 : 0 ≤ (π (k + 1) : ℝ) - π k := sub_nonneg.2 (by exact_mod_cast hπ (Nat.le_succ k))
    have hg : (π (k + 1) : ℝ) - π k ≤ 1 / 2 ^ n := by
      simpa only [π, NNReal.coe_min] using seed_grid_sub_le n k t
    have h1 := mul_le_mul_of_nonneg_left hg h0
    calc _ ≤ (2 * C ^ 2) * (((π (k + 1) : ℝ) - π k) * (1 / 2 ^ n)) := by
          nlinarith [mul_le_mul_of_nonneg_left h1
            (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg C))]
      _ = _ := by ring
  calc (∑ k ∈ Finset.range (cells n), C ^ 2 * (2 * ((π (k + 1) : ℝ) - π k) ^ 2))
      ≤ ∑ k ∈ Finset.range (cells n), (2 * C ^ 2 / 2 ^ n) * ((π (k + 1) : ℝ) - π k) :=
        Finset.sum_le_sum fun k _ => hstep k
    _ = (2 * C ^ 2 / 2 ^ n) * ((π (cells n) : ℝ) - π 0) := by
      rw [← Finset.mul_sum]
      congr 1
      exact Finset.sum_range_sub (fun k => (π k : ℝ)) (cells n)
    _ ≤ _ := by
      simp only [π, grid_zero, zero_min, NNReal.coe_zero, sub_zero]
      have := mul_le_mul_of_nonneg_left
        (show (min (grid n (cells n)) t : ℝ) ≤ t by exact_mod_cast min_le_right _ _)
        (show 0 ≤ 2 * C ^ 2 / 2 ^ n by positivity)
      simpa only [NNReal.coe_min, div_mul_eq_mul_div] using this

/-- The dyadic quadratic errors converge to zero in probability. -/
theorem tendstoInMeasure_seedQuadraticError (hB : IsFilteredPreBrownian B 𝓕 P)
    (hw : StronglyAdapted 𝓕 w) {C : ℝ} (hC : 0 ≤ C)
    (hb : ∀ u ω, |w u ω| ≤ C) (t : ℝ≥0) :
    TendstoInMeasure P (fun n => seedQuadraticError B w n t) atTop (fun _ => (0 : ℝ)) := by
  have : IsProbabilityMeasure P := hB.isGaussianProcess.isProbabilityMeasure
  have hm (n : ℕ) : MemLp (seedQuadraticError B w n t) 2 P := by
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
  apply tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero
    (fun n => (hm n).aestronglyMeasurable) stronglyMeasurable_const.aestronglyMeasurable
  have hr : Tendsto (fun n : ℕ => 2 * C ^ 2 * t / (2 : ℝ) ^ n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  have hs := ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hr.sqrt)
  simp only [Real.sqrt_zero, ENNReal.ofReal_zero] at hs
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hs (fun _ => bot_le)
  intro n
  simp only [Pi.sub_def, sub_zero]
  rw [eLpNorm_two_eq_sqrt (hm n)]
  exact ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt (integral_sq_seedQuadraticError_le hB hw hC hb n t))

end InteractingSLE.ZhanGT4
