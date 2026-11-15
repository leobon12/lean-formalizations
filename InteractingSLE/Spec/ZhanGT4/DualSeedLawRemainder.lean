/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedLawMesh
import InteractingSLE.Stochastic.ItoAdapted

/-!
# Cubic errors and dominated Taylor remainders

Packet PROVE-ZHAN-GT4-A22. The existing random-field Taylor estimate has
an error `C |ΔB|³ + R`. This file removes both terms in probability on the
dyadic partitions of the general-filtration stochastic integral.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

open Girsanov

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}

/-- The cubic Brownian increments over the clamped dyadic partition. -/
def seedCubicError (B : ℝ≥0 → Ω → ℝ) (n : ℕ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  ∑ k ∈ Finset.range (cells n),
    |B (min (grid n (k + 1)) t) ω - B (min (grid n k) t) ω| ^ 3

/-- The cubic sum has mean at most `m₃ t sqrt(2⁻ⁿ)`. -/
theorem integral_seedCubicError_le (hB : IsFilteredBrownianReal 𝓕 B P) (n : ℕ) (t : ℝ≥0) :
    ∫ ω, seedCubicError B n t ω ∂P ≤
      QuantumZipper.gaussianAbsMoment 3 * t * Real.sqrt (1 / 2 ^ n) := by
  let π : ℕ → ℝ≥0 := fun k => min (grid n k) t
  have hπ : Monotone π := fun i j hij => min_le_min_right t (grid_mono n hij)
  have hm := QuantumZipper.gaussianAbsMoment_nonneg 3
  unfold seedCubicError
  rw [integral_finsetSum _ fun k _ => hB.integrable_abs_incr_pow (hπ (Nat.le_succ k)) 3]
  have hstep (k : ℕ) : (∫ ω, |B (π (k + 1)) ω - B (π k) ω| ^ 3 ∂P) ≤
      (QuantumZipper.gaussianAbsMoment 3 * Real.sqrt (1 / 2 ^ n)) *
        ((π (k + 1) : ℝ) - π k) := by
    have h0 : 0 ≤ (π (k + 1) : ℝ) - π k := sub_nonneg.2 (by exact_mod_cast hπ (Nat.le_succ k))
    have hg : (π (k + 1) : ℝ) - π k ≤ 1 / 2 ^ n := by
      simpa only [π, NNReal.coe_min] using seed_grid_sub_le n k t
    calc _ ≤ QuantumZipper.gaussianAbsMoment 3 *
          (((π (k + 1) : ℝ) - π k) * Real.sqrt ((π (k + 1) : ℝ) - π k)) :=
            hB.integral_abs_incr_pow_three_le (hπ (Nat.le_succ k))
      _ ≤ QuantumZipper.gaussianAbsMoment 3 *
          (((π (k + 1) : ℝ) - π k) * Real.sqrt (1 / 2 ^ n)) := by gcongr
      _ = _ := by ring
  calc (∑ k ∈ Finset.range (cells n), ∫ ω, |B (π (k + 1)) ω - B (π k) ω| ^ 3 ∂P)
      ≤ ∑ k ∈ Finset.range (cells n),
          (QuantumZipper.gaussianAbsMoment 3 * Real.sqrt (1 / 2 ^ n)) *
            ((π (k + 1) : ℝ) - π k) := Finset.sum_le_sum fun k _ => hstep k
    _ = (QuantumZipper.gaussianAbsMoment 3 * Real.sqrt (1 / 2 ^ n)) *
        ((π (cells n) : ℝ) - π 0) := by
      rw [← Finset.mul_sum]
      congr 1
      exact Finset.sum_range_sub (fun k => (π k : ℝ)) (cells n)
    _ ≤ _ := by
      have he : (π (cells n) : ℝ) - π 0 ≤ t := by
        simp only [π, grid_zero, zero_min, NNReal.coe_zero, sub_zero, NNReal.coe_min]
        exact min_le_right _ _
      nlinarith [mul_le_mul_of_nonneg_left he (mul_nonneg hm (Real.sqrt_nonneg (1 / 2 ^ n)))]

/-- Any measurable error bounded by a cubic sum and a bounded pathwise
vanishing remainder tends to zero in probability. -/
theorem tendstoInMeasure_seedTaylorError (hB : IsFilteredBrownianReal 𝓕 B P)
    {E R : ℕ → Ω → ℝ} (hE : ∀ n, Measurable (E n)) (hR : ∀ n, Measurable (R n))
    {C K : ℝ} (hC : 0 ≤ C) (t : ℝ≥0)
    (hR0 : ∀ n ω, 0 ≤ R n ω) (hRb : ∀ n ω, R n ω ≤ K)
    (hRl : ∀ ω, Tendsto (fun n => R n ω) atTop (𝓝 0))
    (he : ∀ n ω, |E n ω| ≤ C * seedCubicError B n t ω + R n ω) :
    TendstoInMeasure P E atTop (fun _ => (0 : ℝ)) := by
  have : IsProbabilityMeasure P := hB.isProbabilityMeasure'
  have hRi (n : ℕ) : Integrable (R n) P := (integrable_const K).mono' (hR n).aestronglyMeasurable
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (hR0 n ω)]; exact hRb n ω)
  have hCi (n : ℕ) : Integrable (seedCubicError B n t) P :=
    integrable_finsetSum _ fun k _ => hB.integrable_abs_incr_pow
      (min_le_min_right t (grid_mono n (Nat.le_succ k))) 3
  have hEi (n : ℕ) : Integrable (E n) P :=
    ((hCi n).const_mul C |>.add (hRi n)).mono' (hE n).aestronglyMeasurable
      (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs]; exact he n ω)
  have hIR : Tendsto (fun n => ∫ ω, R n ω ∂P) atTop (𝓝 0) := by
    simpa only [integral_zero] using tendsto_integral_of_dominated_convergence (fun _ => K)
      (fun n => (hR n).aestronglyMeasurable) (integrable_const (μ := P) K)
      (fun n => Eventually.of_forall fun ω => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hR0 n ω)]; exact hRb n ω)
      (Eventually.of_forall hRl)
  have hmesh : Tendsto (fun n : ℕ => (1 : ℝ) / 2 ^ n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop_atTop_of_one_lt (by norm_num))
  have hu : Tendsto (fun n => C *
      (QuantumZipper.gaussianAbsMoment 3 * t * Real.sqrt (1 / 2 ^ n)) + ∫ ω, R n ω ∂P)
      atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero, mul_zero, add_zero] using
      (((hmesh.sqrt).const_mul (QuantumZipper.gaussianAbsMoment 3 * t)).const_mul C).add hIR
  have hL1 : Tendsto (fun n => ∫ ω, |E n ω| ∂P) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => integral_nonneg fun ω => abs_nonneg _) (fun n => ?_) hu
    calc (∫ ω, |E n ω| ∂P) ≤ ∫ ω, C * seedCubicError B n t ω + R n ω ∂P :=
          integral_mono (hEi n).abs (((hCi n).const_mul C).add (hRi n)) (he n)
      _ = C * (∫ ω, seedCubicError B n t ω ∂P) + ∫ ω, R n ω ∂P := by
          rw [integral_add ((hCi n).const_mul C) (hRi n), integral_const_mul]
      _ ≤ _ := by gcongr; exact integral_seedCubicError_le hB n t
  apply tendstoInMeasure_of_tendsto_eLpNorm one_ne_zero
    (fun n => (hE n).aestronglyMeasurable) stronglyMeasurable_const.aestronglyMeasurable
  simpa only [Pi.sub_def, sub_zero, eLpNorm_one_eq_lintegral_enorm,
    ← ofReal_integral_norm_eq_lintegral_enorm (hEi _), Real.norm_eq_abs, ENNReal.ofReal_zero,
    Function.comp_def] using
    ENNReal.continuous_ofReal.continuousAt.tendsto.comp hL1

end InteractingSLE.ZhanGT4
