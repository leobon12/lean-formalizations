import HigherDimLQGMetric.Frozen.LogCovRd
import HigherDimLQGMetric.Frozen.TestRd0
import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Log-energy seminorm and Cameron–Martin bounds

The analytic interface for the covariance of the whole-space log-correlated field.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

variable {d : ℕ}

/-- The square root of the logarithmic covariance of a test function with itself. -/
def logNorm (φ : TestRd d) : ℝ := Real.sqrt (logCovRd φ φ)

/-- A dual Cameron–Martin bound on all mean-zero test functions. -/
def IsCMBounded (F : Rd d → ℝ) (C : ℝ) : Prop :=
  ∀ φ : TestRd0 d, |∫ x, F x * φ.1 x| ≤ C * logNorm φ.1

theorem logNorm_nonneg (φ : TestRd d) : 0 ≤ logNorm φ := Real.sqrt_nonneg _

private theorem integrable_mul_test {F : Rd d → ℝ} (hF : Continuous F)
    (φ : TestRd d) : Integrable (fun x => F x * φ x) :=
  (hF.mul φ.continuous).integrable_of_hasCompactSupport φ.hasCompactSupport.mul_left

/-- The Cameron–Martin bound is stable under finite sums. -/
theorem IsCMBounded.sum {ι : Type*} (s : Finset ι) {F : ι → Rd d → ℝ} {C : ι → ℝ}
    (hcont : ∀ i ∈ s, Continuous (F i)) (hF : ∀ i ∈ s, IsCMBounded (F i) (C i)) :
    IsCMBounded (fun x => ∑ i ∈ s, F i x) (∑ i ∈ s, C i) := by
  intro φ
  have hint : ∀ i ∈ s, Integrable (fun x => F i x * φ.1 x) :=
    fun i hi => integrable_mul_test (hcont i hi) φ.1
  calc
    |∫ x, (∑ i ∈ s, F i x) * φ.1 x| = |∑ i ∈ s, ∫ x, F i x * φ.1 x| := by
      simp_rw [Finset.sum_mul]
      rw [integral_finsetSum s hint]
    _ ≤ ∑ i ∈ s, |∫ x, F i x * φ.1 x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, C i * logNorm φ.1 :=
      Finset.sum_le_sum fun i hi => hF i hi φ
    _ = (∑ i ∈ s, C i) * logNorm φ.1 := (Finset.sum_mul ..).symm

/-- Adding a constant does not affect mean-zero pairings. -/
theorem IsCMBounded.add_const {F : Rd d → ℝ} {C : ℝ} (hF : IsCMBounded F C)
    (hcont : Continuous F) (c : ℝ) : IsCMBounded (fun x => F x + c) C := by
  intro φ
  have hiF := integrable_mul_test hcont φ.1
  have hiφ : Integrable (φ.1 : Rd d → ℝ) :=
    φ.1.continuous.integrable_of_hasCompactSupport φ.1.hasCompactSupport
  have heq : (∫ x, (F x + c) * φ.1 x) = ∫ x, F x * φ.1 x := by
    simp_rw [add_mul]
    rw [integral_add hiF (hiφ.const_mul c), integral_const_mul, φ.2]
    ring
  rw [heq]
  exact hF φ

/-- Subtracting a constant does not affect mean-zero pairings. -/
theorem IsCMBounded.sub_const {F : Rd d → ℝ} {C : ℝ} (hF : IsCMBounded F C)
    (hcont : Continuous F) (c : ℝ) : IsCMBounded (fun x => F x - c) C := by
  simpa only [sub_eq_add_neg] using hF.add_const hcont (-c)

/-- Constants do not change the Cameron–Martin bound. -/
theorem isCMBounded_add_const_iff {F : Rd d → ℝ} (hcont : Continuous F) (C c : ℝ) :
    IsCMBounded (fun x => F x + c) C ↔ IsCMBounded F C := by
  constructor
  · intro h
    have h' := h.sub_const (hcont.add continuous_const) c
    simpa only [add_sub_cancel_right] using h'
  · intro h
    exact h.add_const hcont c

/-- Scalar multiplication scales the dual bound by the absolute value. -/
theorem IsCMBounded.mul_const {F : Rd d → ℝ} {C : ℝ} (hF : IsCMBounded F C)
    (a : ℝ) : IsCMBounded (fun x => a * F x) (|a| * C) := by
  intro φ
  have heq : (∫ x, (a * F x) * φ.1 x) = a * ∫ x, F x * φ.1 x := by
    simp_rw [mul_assoc]
    rw [integral_const_mul]
  rw [heq, abs_mul]
  calc
    |a| * |∫ x, F x * φ.1 x| ≤ |a| * (C * logNorm φ.1) :=
      mul_le_mul_of_nonneg_left (hF φ) (abs_nonneg _)
    _ = (|a| * C) * logNorm φ.1 := by ring

end HigherDimLQGMetric
