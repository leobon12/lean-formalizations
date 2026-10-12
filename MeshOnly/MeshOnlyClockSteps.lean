import MeshOnly.MeshOnlyHeatUniformization

/-! Expected drift of the actual absorbed uniformized chain. These finite-time
identities will be averaged at a Poisson count in the local clock estimate. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace BouRabeeGwynne.FiniteConductanceNetwork

variable {V : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]

private lemma clock_integral_bind_finite (p : PMF V) (κ : V → PMF V) (f : V → ℝ) :
    (∫ w, f w ∂(p.bind κ).toMeasure) =
      ∑ v, (p v).toReal * (∫ w, f w ∂(κ v).toMeasure) := by
  have hpoint (w : V) : ((p.bind κ) w).toReal =
      ∑ v, (p v).toReal * (κ v w).toReal := by
    rw [PMF.bind_apply, tsum_fintype,
      ENNReal.toReal_sum (fun v _ ↦ ENNReal.mul_ne_top (p.apply_ne_top v)
        ((κ v).apply_ne_top w))]
    simp only [ENNReal.toReal_mul]
  simp only [PMF.integral_eq_sum, smul_eq_mul, hpoint, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  ring

variable (N : FiniteConductanceNetwork V)

lemma integral_uniformizedStepPMF_increment (m : V → ℝ) (hm : ∀ v, 0 < m v)
    (S : Set V) (f : V → ℝ) {v : V} (hv : v ∈ S) :
    (∫ w, (f w - f v) ∂(N.uniformizedStepPMF m hm S v).toMeasure) =
      N.massGenerator m f v / N.uniformizationRate m := by
  rw [PMF.integral_eq_sum]
  simp only [uniformizedStepPMF_apply,
    ENNReal.toReal_ofReal (N.uniformizedTransition_nonneg m hm S v _), smul_eq_mul]
  apply (eq_div_iff (N.uniformizationRate_pos m hm).ne').mpr
  simpa only [mul_comm] using N.uniformizedTransition_generator m hm S f hv

lemma integral_uniformizedStepPMF_le_of_generator_le (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (S : Set V) (f : V → ℝ) {b : ℝ} (hb : 0 ≤ b)
    (hf : ∀ v ∈ S, N.massGenerator m f v ≤ b) (v : V) :
    (∫ w, f w ∂(N.uniformizedStepPMF m hm S v).toMeasure) ≤
      f v + b / N.uniformizationRate m := by
  by_cases hv : v ∈ S
  · have h := N.integral_uniformizedStepPMF_increment m hm S f hv
    rw [integral_sub Integrable.of_finite Integrable.of_finite] at h
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul] at h
    have hle := div_le_div_of_nonneg_right (hf v hv)
      (N.uniformizationRate_pos m hm).le
    linarith
  · rw [N.uniformizedStepPMF_of_not_mem m hm S hv, PMF.toMeasure_pure,
      integral_dirac]
    exact le_add_of_nonneg_right (div_nonneg hb (N.uniformizationRate_pos m hm).le)

/-- A generator upper bound gives the exact linear-in-step expectation bound.
There is no stopping-time or exit-integrability assumption. -/
theorem integral_uniformizedNStepPMF_le_of_generator_le (m : V → ℝ)
    (hm : ∀ v, 0 < m v) (S : Set V) (f : V → ℝ) {b : ℝ} (hb : 0 ≤ b)
    (hf : ∀ v ∈ S, N.massGenerator m f v ≤ b) (n : ℕ) (v : V) :
    (∫ w, f w ∂(N.uniformizedNStepPMF m hm S n v).toMeasure) ≤
      f v + (n : ℝ) * (b / N.uniformizationRate m) := by
  induction n generalizing v with
  | zero =>
    simp only [uniformizedNStepPMF, PMF.toMeasure_pure, integral_dirac,
      Nat.cast_zero, zero_mul, add_zero, le_refl]
  | succ n ih =>
    rw [uniformizedNStepPMF, clock_integral_bind_finite]
    calc
      _ ≤ ∑ w, (N.uniformizedStepPMF m hm S v w).toReal *
          (f w + (n : ℝ) * (b / N.uniformizationRate m)) := by
        exact Finset.sum_le_sum fun w _ =>
          mul_le_mul_of_nonneg_left (ih w) ENNReal.toReal_nonneg
      _ = (∫ w, f w ∂(N.uniformizedStepPMF m hm S v).toMeasure) +
          (n : ℝ) * (b / N.uniformizationRate m) := by
        have hsum := PMF.integral_eq_sum (N.uniformizedStepPMF m hm S v)
          (fun w => f w + (n : ℝ) * (b / N.uniformizationRate m))
        simp only [smul_eq_mul] at hsum
        rw [← hsum]
        simp only [integral_add Integrable.of_finite Integrable.of_finite,
          integral_const, probReal_univ, smul_eq_mul, one_mul]
      _ ≤ (f v + b / N.uniformizationRate m) +
          (n : ℝ) * (b / N.uniformizationRate m) :=
        by linarith only [N.integral_uniformizedStepPMF_le_of_generator_le m hm S f hb hf v]
      _ = f v + ((n + 1 : ℕ) : ℝ) * (b / N.uniformizationRate m) := by
        push_cast
        ring

end BouRabeeGwynne.FiniteConductanceNetwork
