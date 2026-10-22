import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Elementary exponential bookkeeping for Lemma 3.2 and Proposition 3.3 (packet P7)

The depth conditions of Lemma 3.2 and Proposition 3.3 are of the form `n ≥ C Λ` with the logarithmic bracket
`Λ = 1 + log(1 + R) + log e⁻¹ + log q⁻¹` (`p7Lam`). Every failure probability and every deterministic error is
bounded by `K exp(a Λ - r n)`; `p7_mul_exp_le_exp` turns `log K + t ≤ r` into `K e^{-r} ≤ e^{-t}`, and the bracket
facts (`p7Lam_spec`) give `1 + R, e⁻¹, q⁻¹ ≤ e^Λ` and `e^{-Λ} ≤ q`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGContinuity

/-- `K e^{-r} ≤ e^{-t}` as soon as `log K + t ≤ r` (`K > 0`). -/
theorem p7_mul_exp_le_exp {K t r : ℝ} (hK : 0 < K) (h : Real.log K + t ≤ r) :
    K * Real.exp (-r) ≤ Real.exp (-t) := by
  calc K * Real.exp (-r) = Real.exp (Real.log K + -r) := by
        rw [Real.exp_add, Real.exp_log hK]
    _ ≤ Real.exp (-t) := Real.exp_le_exp.mpr (by linarith)

/-- `a ≤ |a| Λ` for `Λ ≥ 1`. -/
theorem p7_le_abs_mul {a Λ : ℝ} (hΛ : 1 ≤ Λ) : a ≤ |a| * Λ := by
  have h1 : a ≤ |a| := le_abs_self a
  have h2 : |a| ≤ |a| * Λ := le_mul_of_one_le_right (abs_nonneg a) hΛ
  linarith

/-- `x ≤ e^Λ` from `log x ≤ Λ` (`x > 0`). -/
theorem p7_le_exp_of_log_le {x Λ : ℝ} (hx : 0 < x) (h : Real.log x ≤ Λ) : x ≤ Real.exp Λ := by
  calc x = Real.exp (Real.log x) := (Real.exp_log hx).symm
    _ ≤ Real.exp Λ := Real.exp_le_exp.mpr h

/-- `e^{-Λ} ≤ q` from `log q⁻¹ ≤ Λ` (`q > 0`). -/
theorem p7_exp_neg_le_of_log_inv_le {q Λ : ℝ} (hq : 0 < q) (h : Real.log q⁻¹ ≤ Λ) :
    Real.exp (-Λ) ≤ q := by
  have hq' : Real.exp (-Real.log q⁻¹) = q := by
    rw [Real.log_inv, neg_neg, Real.exp_log hq]
  calc Real.exp (-Λ) ≤ Real.exp (-Real.log q⁻¹) := Real.exp_le_exp.mpr (by linarith)
    _ = q := hq'

/-- The logarithmic bracket `1 + log(1 + R) + log e⁻¹ + log q⁻¹` of the depth conditions. -/
def p7Lam (R e q : ℝ) : ℝ := 1 + Real.log (1 + R) + Real.log e⁻¹ + Real.log q⁻¹

/-- The bracket dominates each of its terms and `1`. -/
theorem p7Lam_spec {R e q : ℝ} (hR : 0 ≤ R) (he : 0 < e) (he1 : e ≤ 1) (hq : 0 < q) (hq1 : q ≤ 1) :
    1 ≤ p7Lam R e q ∧ Real.log (1 + R) ≤ p7Lam R e q ∧ Real.log e⁻¹ ≤ p7Lam R e q ∧
      Real.log q⁻¹ ≤ p7Lam R e q := by
  have hlR : 0 ≤ Real.log (1 + R) := Real.log_nonneg (by linarith)
  have hle : 0 ≤ Real.log e⁻¹ := Real.log_nonneg (one_le_inv_iff₀.mpr ⟨he, he1⟩)
  have hlq : 0 ≤ Real.log q⁻¹ := Real.log_nonneg (one_le_inv_iff₀.mpr ⟨hq, hq1⟩)
  unfold p7Lam
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

end HigherDimLQGContinuity
