import QuantumZipper.Proofs.Zipper.D3PlusN2FMVarPsiDef
import Mathlib.Analysis.SpecialFunctions.Integrals.PosLogEqCircleAverage
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# N2Z-FMVAR-PSI, part 1: the formula for `fmPsi` off the unit circle

`fmPsi y = π Re y` for `‖y‖ < 1` and `fmPsi y = π Re y / ‖y‖²` for `‖y‖ > 1`.

Own elementary proof (the classical Fourier expansion of `log |1 - z e^{iθ}|`, using
`log|1 - z| = -Re Σ z^k/k`): expand
`-log ‖1 - c e^{±iθ}‖ = Re Σ_{n ≥ 1} (c e^{±iθ})^n / n` (mathlib's
`Complex.hasSum_taylorSeries_neg_log`), integrate termwise against `cos θ`
(`intervalIntegral.hasSum_intervalIntegral_of_summable_norm`), and only `n = 1` survives.
-/

noncomputable section

open MeasureTheory Set Filter Topology
open scoped Real

namespace QuantumZipper
namespace D3Plus

lemma fmPsi_intExp (k : ℤ) :
    ∫ θ in (0 : ℝ)..(2 * π), Complex.exp ((k : ℂ) * Complex.I * (θ : ℂ)) =
      if k = 0 then (2 * π : ℂ) else 0 := by
  split_ifs with hk
  · subst hk; simp
  · have hc : (k : ℂ) * Complex.I ≠ 0 := mul_ne_zero (by exact_mod_cast hk) Complex.I_ne_zero
    rw [integral_exp_mul_complex hc]
    have : Complex.exp ((k : ℂ) * Complex.I * ((2 * π : ℝ) : ℂ)) = 1 := by
      rw [← Complex.exp_int_mul_two_pi_mul_I k]; congr 1; push_cast; ring
    rw [this]; simp

lemma fmPsi_intCosExp (m : ℤ) :
    ∫ θ in (0 : ℝ)..(2 * π), (Real.cos θ : ℂ) * Complex.exp ((m : ℂ) * Complex.I * (θ : ℂ)) =
      (if m + 1 = 0 then (π : ℂ) else 0) + (if m - 1 = 0 then (π : ℂ) else 0) := by
  have h : ∀ θ : ℝ, (Real.cos θ : ℂ) * Complex.exp ((m : ℂ) * Complex.I * (θ : ℂ)) =
      (1 / 2 : ℂ) * Complex.exp (((m + 1 : ℤ) : ℂ) * Complex.I * (θ : ℂ)) +
      (1 / 2 : ℂ) * Complex.exp (((m - 1 : ℤ) : ℂ) * Complex.I * (θ : ℂ)) := by
    intro θ
    have e1 : Complex.exp ((θ : ℂ) * Complex.I) * Complex.exp ((m : ℂ) * Complex.I * (θ : ℂ)) =
        Complex.exp (((m + 1 : ℤ) : ℂ) * Complex.I * (θ : ℂ)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    have e2 : Complex.exp (-(θ : ℂ) * Complex.I) * Complex.exp ((m : ℂ) * Complex.I * (θ : ℂ)) =
        Complex.exp (((m - 1 : ℤ) : ℂ) * Complex.I * (θ : ℂ)) := by
      rw [← Complex.exp_add]; congr 1; push_cast; ring
    have hc := Complex.two_cos (θ : ℂ)
    rw [Complex.ofReal_cos]
    linear_combination (1 / 2 : ℂ) * e1 + (1 / 2 : ℂ) * e2 +
      (1 / 2 : ℂ) * Complex.exp ((m : ℂ) * Complex.I * (θ : ℂ)) * hc
  simp_rw [h]
  rw [intervalIntegral.integral_add ((by fun_prop : Continuous fun θ : ℝ =>
      (1 / 2 : ℂ) * Complex.exp (((m + 1 : ℤ) : ℂ) * Complex.I * (θ : ℂ))).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun θ : ℝ =>
      (1 / 2 : ℂ) * Complex.exp (((m - 1 : ℤ) : ℂ) * Complex.I * (θ : ℂ))).intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    fmPsi_intExp, fmPsi_intExp]
  split_ifs <;> ring

lemma fmPsi_norm_exp (t : ℝ) (s : ℤ) : ‖Complex.exp ((s : ℂ) * Complex.I * (t : ℂ))‖ = 1 := by
  rw [show (s : ℂ) * Complex.I * (t : ℂ) = ((s * t : ℝ) : ℂ) * Complex.I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- Termwise integration of `-log ‖1 - c e^{isθ}‖ = Re Σ (c e^{isθ})^n / n` against `cos θ`. -/
lemma fmPsi_series (c : ℂ) (hc : ‖c‖ < 1) (s : ℤ) (hs : s = 1 ∨ s = -1) :
    ∫ θ in (0 : ℝ)..(2 * π),
      Real.cos θ * -Real.log ‖1 - c * Complex.exp ((s : ℂ) * Complex.I * (θ : ℂ))‖ =
      π * c.re := by
  have hzn : ∀ θ : ℝ, ‖c * Complex.exp ((s : ℂ) * Complex.I * (θ : ℂ))‖ = ‖c‖ := by
    intro θ; rw [norm_mul, fmPsi_norm_exp, mul_one]
  let g : ℕ → C(ℝ, ℝ) := fun n => ⟨fun θ => ((Real.cos θ : ℂ) *
      ((c * Complex.exp ((s : ℂ) * Complex.I * (θ : ℂ))) ^ n / n)).re,
      Complex.continuous_re.comp (by fun_prop)⟩
  have hbd : ∀ n : ℕ, ∀ θ : ℝ, ‖((Real.cos θ : ℂ) *
      ((c * Complex.exp ((s : ℂ) * Complex.I * (θ : ℂ))) ^ n / n)).re‖ ≤ ‖c‖ ^ n := by
    intro n θ
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 : |Real.cos θ| ≤ 1 := Real.abs_cos_le_one θ
    have h2 : ‖(c * Complex.exp ((s : ℂ) * Complex.I * (θ : ℂ))) ^ n / (n : ℂ)‖ ≤ ‖c‖ ^ n := by
      rw [norm_div, norm_pow, hzn]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · apply div_le_self (by positivity)
        rw [Complex.norm_natCast]; exact_mod_cast hn
    calc |Real.cos θ| * _ ≤ 1 * ‖c‖ ^ n := by
          apply mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
      _ = ‖c‖ ^ n := one_mul _
  have hsum : Summable fun n : ℕ =>
      ‖(g n).restrict (⟨uIcc (0 : ℝ) (2 * π), isCompact_uIcc⟩ : TopologicalSpace.Compacts ℝ)‖ := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_)
      (summable_geometric_of_lt_one (norm_nonneg c) hc)
    exact (ContinuousMap.norm_le _ (by positivity)).2 fun x => hbd n x
  have H := intervalIntegral.hasSum_intervalIntegral_of_summable_norm hsum
  have hpt : ∀ θ : ℝ, ∑' n : ℕ, g n θ =
      Real.cos θ * -Real.log ‖1 - c * Complex.exp ((s : ℂ) * Complex.I * (θ : ℂ))‖ := by
    intro θ
    have := (Complex.hasSum_re ((Complex.hasSum_taylorSeries_neg_log
      (by rw [hzn]; exact hc : ‖c * Complex.exp ((s : ℂ) * Complex.I * (θ : ℂ))‖ < 1)).mul_left
      (Real.cos θ : ℂ))).tsum_eq
    simp only [g, ContinuousMap.coe_mk]
    rw [this, Complex.re_ofReal_mul, Complex.neg_re, Complex.log_re]
  have hterm : ∀ n : ℕ, ∫ θ in (0 : ℝ)..(2 * π), g n θ = if n = 1 then π * c.re else 0 := by
    intro n
    have hcont : Continuous fun θ : ℝ => (Real.cos θ : ℂ) *
        ((c * Complex.exp ((s : ℂ) * Complex.I * (θ : ℂ))) ^ n / n) := by fun_prop
    have hre := intervalIntegral.intervalIntegral_re (μ := volume) (a := 0) (b := 2 * π)
      (hcont.intervalIntegrable 0 (2 * π))
    simp only [g, ContinuousMap.coe_mk]
    refine hre.trans ?_
    have hpt' : ∀ θ : ℝ, (Real.cos θ : ℂ) *
        ((c * Complex.exp ((s : ℂ) * Complex.I * (θ : ℂ))) ^ n / n) =
        (c ^ n / n) * ((Real.cos θ : ℂ) *
          Complex.exp (((s * n : ℤ) : ℂ) * Complex.I * (θ : ℂ))) := by
      intro θ
      rw [mul_pow, ← Complex.exp_nat_mul,
        show (n : ℂ) * ((s : ℂ) * Complex.I * (θ : ℂ)) =
          ((s * n : ℤ) : ℂ) * Complex.I * (θ : ℂ) by push_cast; ring]
      ring
    simp_rw [hpt']
    rw [intervalIntegral.integral_const_mul, fmPsi_intCosExp]
    rcases hs with rfl | rfl <;> split_ifs <;> (try omega) <;> simp_all <;> ring
  have H' : HasSum (fun n : ℕ => ∫ θ in (0 : ℝ)..(2 * π), g n θ) (π * c.re) := by
    simp_rw [hterm]; exact hasSum_ite_eq 1 _
  rw [H'.unique H]
  exact (intervalIntegral.integral_congr fun θ _ => hpt θ).symm

/-- `fmPsi y = π Re y` inside the unit disc. -/
lemma fmPsi_of_norm_lt_one (y : ℂ) (hy : ‖y‖ < 1) : fmPsi y = π * y.re := by
  unfold fmPsi
  rw [← fmPsi_series y hy (-1) (Or.inr rfl)]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  have he : Complex.exp ((θ : ℂ) * Complex.I) *
      Complex.exp (((-1 : ℤ) : ℂ) * Complex.I * (θ : ℂ)) = 1 := by
    rw [← Complex.exp_add]; push_cast; ring_nf; exact Complex.exp_zero
  have hy' : y - Complex.exp ((θ : ℂ) * Complex.I) = -Complex.exp ((θ : ℂ) * Complex.I) *
      (1 - y * Complex.exp (((-1 : ℤ) : ℂ) * Complex.I * (θ : ℂ))) := by
    linear_combination (-y) * he
  rw [hy', norm_mul, norm_neg, Complex.norm_exp_ofReal_mul_I, one_mul]

/-- `fmPsi y = π Re y / ‖y‖²` outside the closed unit disc. -/
lemma fmPsi_of_one_lt_norm (y : ℂ) (hy : 1 < ‖y‖) : fmPsi y = π * y.re / ‖y‖ ^ 2 := by
  have hy0 : y ≠ 0 := by rintro rfl; norm_num at hy
  have hc : ‖y⁻¹‖ < 1 := by rw [norm_inv]; exact inv_lt_one_of_one_lt₀ hy
  have hne : ∀ θ : ℝ, 1 - y⁻¹ * Complex.exp (((1 : ℤ) : ℂ) * Complex.I * (θ : ℂ)) ≠ 0 := by
    intro θ h
    have h1 : y⁻¹ * Complex.exp (((1 : ℤ) : ℂ) * Complex.I * (θ : ℂ)) = 1 := by
      linear_combination -h
    have := congrArg norm h1
    rw [norm_mul, fmPsi_norm_exp, mul_one, norm_one] at this
    linarith
  have hpt : ∀ θ : ℝ, Real.cos θ * -Real.log ‖y - Complex.exp ((θ : ℂ) * Complex.I)‖ =
      -Real.log ‖y‖ * Real.cos θ + Real.cos θ *
        -Real.log ‖1 - y⁻¹ * Complex.exp (((1 : ℤ) : ℂ) * Complex.I * (θ : ℂ))‖ := by
    intro θ
    have h1 : y - Complex.exp ((θ : ℂ) * Complex.I) =
        y * (1 - y⁻¹ * Complex.exp (((1 : ℤ) : ℂ) * Complex.I * (θ : ℂ))) := by
      push_cast; field_simp
    rw [h1, norm_mul, Real.log_mul (norm_ne_zero_iff.2 hy0) (norm_ne_zero_iff.2 (hne θ))]
    ring
  unfold fmPsi
  rw [intervalIntegral.integral_congr fun θ _ => hpt θ]
  have hcont : Continuous fun θ : ℝ => Real.cos θ *
      -Real.log ‖1 - y⁻¹ * Complex.exp (((1 : ℤ) : ℂ) * Complex.I * (θ : ℂ))‖ :=
    Real.continuous_cos.mul (Continuous.neg (Continuous.log (by fun_prop)
      fun θ => norm_ne_zero_iff.2 (hne θ)))
  rw [intervalIntegral.integral_add ((by fun_prop : Continuous fun θ : ℝ =>
      -Real.log ‖y‖ * Real.cos θ).intervalIntegrable _ _) (hcont.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, integral_cos, fmPsi_series _ hc 1 (Or.inl rfl),
    Complex.inv_re, Complex.normSq_eq_norm_sq]
  simp [Real.sin_two_pi]
  ring

end D3Plus
end QuantumZipper
