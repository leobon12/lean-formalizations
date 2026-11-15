/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedImagePrepare

/-!
# The seeded stochastic integral at the entrance

Packet PROVE-ZHAN-GT4-A22. The discrete Itô isometry from the landed port
bounds the general-filtration Riemann integral by `C sqrt(t)` in L².
Consequently the stochastic term vanishes in probability at time zero.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

open Girsanov

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ} {B θ : ℝ≥0 → Ω → ℝ}

/-- The discrete stochastic sums satisfy the sharp bounded-integrand
second-moment estimate, even when the partition ends before `t`. -/
theorem integral_sq_seedRiemann_le (hB : IsFilteredPreBrownian B 𝓕 P)
    (hm : StronglyAdapted 𝓕 θ) {C : ℝ} (hb : ∀ u ω, |θ u ω| ≤ C)
    (n : ℕ) (t : ℝ≥0) : ∫ ω, riemannSum B θ n t ω ^ 2 ∂P ≤ C ^ 2 * t := by
  have hi : ∀ j, MemLp (θ (grid n j)) 2 P := fun j =>
    memLp_two_of_bdd ((hm _).mono (𝓕.le _)).aestronglyMeasurable (hb _)
  have he := integral_sq_sum_clamp hB (grid_mono n) (fun j => (hm _).measurable) hi 0 t (cells n)
  simp_rw [← riemannSum_eq_sum_clamp] at he
  rw [he]
  have hmom : ∀ j, (∫ ω, θ (grid n j) ω ^ 2 ∂P) ≤ C ^ 2 := by
    intro j
    calc (∫ ω, θ (grid n j) ω ^ 2 ∂P) ≤ ∫ _ω : Ω, C ^ 2 ∂P :=
        integral_mono_ae (hi j).integrable_sq (integrable_const _) (ae_of_all _ fun ω => by
          simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hb (grid n j) ω) 2)
      _ = C ^ 2 := by simp
  calc (∑ j ∈ Finset.range (cells n), (∫ ω, θ (grid n j) ω ^ 2 ∂P) *
        (((clamp 0 t (grid n (j + 1)) : ℝ≥0) : ℝ) - clamp 0 t (grid n j)))
      ≤ ∑ j ∈ Finset.range (cells n), C ^ 2 *
        (((clamp 0 t (grid n (j + 1)) : ℝ≥0) : ℝ) - clamp 0 t (grid n j)) := by
          apply Finset.sum_le_sum
          intro j _
          exact mul_le_mul_of_nonneg_right (hmom j)
            (sub_nonneg.2 (by exact_mod_cast clamp_mono 0 t (grid_mono n (Nat.le_succ j))))
    _ = C ^ 2 * ((clamp 0 t (grid n (cells n)) : ℝ) - clamp 0 t (grid n 0)) := by
      rw [← Finset.mul_sum]
      congr 1
      exact Finset.sum_range_sub (fun j => (clamp 0 t (grid n j) : ℝ)) (cells n)
    _ ≤ C ^ 2 * t := by
      simp only [grid_zero, clamp_zero_left, zero_min, NNReal.coe_zero, sub_zero]
      exact mul_le_mul_of_nonneg_left (by exact_mod_cast min_le_right (grid n (cells n)) t) (sq_nonneg _)

/-- The general-filtration Itô integral has the entrance L² bound. -/
theorem eLpNorm_seedStochIntegral_le (hB : IsFilteredPreBrownian B 𝓕 P)
    (hm : StronglyAdapted 𝓕 θ) {C : ℝ} (hb : ∀ u ω, |θ u ω| ≤ C)
    (hreg : IsRiemannRegular P θ) (t : ℝ≥0) :
    eLpNorm (stochIntegral P 𝓕 B θ t) 2 P ≤ ENNReal.ofReal (Real.sqrt (C ^ 2 * t)) := by
  apply eLpNorm_le_of_tendstoInMeasure
    (f := fun n => riemannSum B θ n t) (Eventually.of_forall fun n => ?_)
    (tendstoInMeasure_riemannSum hB hm hb hreg t)
    (fun n => (memLp_riemannSum hB hm hb n t).aestronglyMeasurable)
  rw [eLpNorm_two_eq_sqrt (memLp_riemannSum hB hm hb n t)]
  exact ENNReal.ofReal_le_ofReal (Real.sqrt_le_sqrt (integral_sq_seedRiemann_le hB hm hb n t))

/-- No extra entrance stochastic-integral hypothesis is needed: bounded
noise makes its integral converge to zero in probability as time decreases. -/
theorem tendstoInMeasure_seedStochIntegral_zero (hB : IsFilteredPreBrownian B 𝓕 P)
    (hm : StronglyAdapted 𝓕 θ) {C : ℝ} (hb : ∀ u ω, |θ u ω| ≤ C)
    (hreg : IsRiemannRegular P θ) {u : ℕ → ℝ≥0} (hu : Tendsto u atTop (𝓝 0)) :
    TendstoInMeasure P (fun n => stochIntegral P 𝓕 B θ (u n)) atTop (fun _ => (0 : ℝ)) := by
  apply tendstoInMeasure_of_tendsto_eLpNorm two_ne_zero
    (fun n => (memLp_stochIntegral hB hm hb hreg (u n)).aestronglyMeasurable)
    stronglyMeasurable_const.aestronglyMeasurable
  have hlim : Tendsto (fun n => ENNReal.ofReal (Real.sqrt (C ^ 2 * (u n : ℝ)))) atTop (𝓝 0) := by
    have hcoe := NNReal.continuous_coe.continuousAt.tendsto.comp hu
    simpa only [Function.comp_def, NNReal.coe_zero, mul_zero, Real.sqrt_zero, ENNReal.ofReal_zero] using
      ENNReal.continuous_ofReal.continuousAt.tendsto.comp
        ((Real.continuous_sqrt.continuousAt.tendsto).comp (hcoe.const_mul (C ^ 2)))
  simpa only [Pi.sub_def, sub_zero] using
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim (fun _ => bot_le)
      (fun n => eLpNorm_seedStochIntegral_le hB hm hb hreg (u n))

end InteractingSLE.ZhanGT4
