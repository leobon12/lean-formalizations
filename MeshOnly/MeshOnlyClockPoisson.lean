import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! The Poisson clock has its actual mean, including rate zero. Averaging a
finite-chain drift estimate therefore introduces only the elapsed time. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal NNReal

set_option backward.isDefEq.respectTransparency false

namespace BouRabeeGwynne.MeshOnlyClock

/-- First moment of the actual Poisson coefficients; no positive-rate premise. -/
lemma hasSum_poisson_first_moment (r : ℝ≥0) :
    HasSum (fun n : ℕ =>
      (Real.exp (-(r : ℝ)) * (r : ℝ)^n / n.factorial) * (n : ℝ)) (r : ℝ) := by
  have hshift : HasSum (fun n : ℕ =>
      (Real.exp (-(r : ℝ)) * (r : ℝ)^(n+1) / (n+1).factorial) * ((n+1 : ℕ) : ℝ))
      (r : ℝ) := by
    have heq : (fun n : ℕ =>
        (Real.exp (-(r : ℝ)) * (r : ℝ)^(n+1) / (n+1).factorial) * ((n+1 : ℕ) : ℝ)) =
        (fun n : ℕ => (r : ℝ) *
          (Real.exp (-(r : ℝ)) * (r : ℝ)^n / n.factorial)) := by
      funext n
      rw [pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      have hn : (n : ℝ) + 1 ≠ 0 := by positivity
      have hfact : (n.factorial : ℝ) ≠ 0 := by positivity
      field_simp
      <;> ring
    rw [heq]
    simpa only [mul_one] using (hasSum_one_poissonMeasure r).mul_left (r : ℝ)
  simpa only [Nat.cast_zero, mul_zero, zero_add] using
    (HasSum.zero_add (f := fun n : ℕ =>
      (Real.exp (-(r : ℝ)) * (r : ℝ)^n / n.factorial) * (n : ℝ)) hshift)

lemma integrable_poisson_natCast (r : ℝ≥0) :
    Integrable (fun n : ℕ => (n : ℝ)) (poissonMeasure r) := by
  apply integrable_poissonMeasure_iff.mpr
  simpa only [Real.norm_natCast] using (hasSum_poisson_first_moment r).summable

lemma integral_poisson_natCast (r : ℝ≥0) :
    (∫ n : ℕ, (n : ℝ) ∂poissonMeasure r) = (r : ℝ) := by
  rw [integral_poissonMeasure]
  simpa only [smul_eq_mul] using (hasSum_poisson_first_moment r).tsum_eq

variable {V : Type*} [Fintype V] [MeasurableSpace V] [MeasurableSingletonClass V]

/-- The expected value under a genuine PMF mixture is the convergent mixture
of its expected values. Finite destination space supplies integrability. -/
lemma hasSum_integral_bind (p : PMF ℕ) (κ : ℕ → PMF V) (f : V → ℝ) :
    HasSum (fun n => (p n).toReal * (∫ v, f v ∂(κ n).toMeasure))
      (∫ v, f v ∂(p.bind κ).toMeasure) := by
  have hmeasure : (p.bind κ).toMeasure =
      Measure.sum (fun n => p n • (κ n).toMeasure) := by
    ext s hs
    simp only [PMF.toMeasure_bind_apply p κ s hs, Measure.sum_apply _ hs,
      Measure.smul_apply, smul_eq_mul]
  have hint : Integrable f (Measure.sum (fun n => p n • (κ n).toMeasure)) := by
    rw [← hmeasure]
    exact Integrable.of_finite
  have h := hasSum_integral_measure hint
  rw [← hmeasure] at h
  simpa only [integral_smul_measure, smul_eq_mul] using h

/-- A linear bound after each step is averaged at the actual independent
Poisson horizon. -/
theorem integral_poisson_bind_le (r : ℝ≥0) (κ : ℕ → PMF V) (f : V → ℝ)
    (a b : ℝ)
    (h : ∀ n, (∫ v, f v ∂(κ n).toMeasure) ≤ a + (n : ℝ) * b) :
    (∫ v, f v ∂((poissonMeasure r).toPMF.bind κ).toMeasure) ≤ a + (r : ℝ) * b := by
  have hcoeff (n : ℕ) : ((poissonMeasure r).toPMF n).toReal =
      Real.exp (-(r : ℝ)) * (r : ℝ)^n / n.factorial := by
    rw [Measure.toPMF_apply]
    exact poissonMeasure_real_singleton r n
  have hsum := hasSum_integral_bind (poissonMeasure r).toPMF κ f
  simp only [hcoeff] at hsum
  have hupper : HasSum (fun n : ℕ =>
      (Real.exp (-(r : ℝ)) * (r : ℝ)^n / n.factorial) * (a + (n : ℝ)*b))
      (a + (r : ℝ)*b) := by
    have heq : (fun n : ℕ =>
        (Real.exp (-(r : ℝ)) * (r : ℝ)^n / n.factorial) * (a + (n : ℝ)*b)) =
        (fun n : ℕ =>
          (Real.exp (-(r : ℝ)) * (r : ℝ)^n / n.factorial) * a +
          ((Real.exp (-(r : ℝ)) * (r : ℝ)^n / n.factorial) * (n : ℝ)) * b) := by
      funext n
      ring
    rw [heq]
    simpa only [one_mul] using ((hasSum_one_poissonMeasure r).mul_right a).add
      ((hasSum_poisson_first_moment r).mul_right b)
  apply hasSum_le _ hsum hupper
  intro n
  exact mul_le_mul_of_nonneg_left (h n) (by positivity)

end BouRabeeGwynne.MeshOnlyClock
