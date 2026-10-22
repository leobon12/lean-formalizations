import HigherDimLQGMetric.LogEnergy.Basic
import HigherDimLQGMetric.LGF.Invariance

/-!
# Affine invariance of Cameron–Martin bounds

The logarithmic covariance changes by a constant under dilation, and mean-zero
test functions remove that constant.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory
open HigherDimLFPP (Rd)

namespace HigherDimLQGMetric

variable {d : ℕ}

private theorem logNorm_testAffinePull (φ : TestRd d) (hφ0 : ∫ x, φ x = 0)
    {r : ℝ} (hr : 0 < r) (z : Rd d) :
    logNorm (testAffinePull r z φ) = r ^ d * logNorm φ := by
  rw [logNorm, logCovRd_testAffinePull φ φ hφ0 hr z]
  have hpow : r ^ (2 * d) = (r ^ d) ^ 2 := by ring
  rw [hpow, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (pow_nonneg hr.le _)]
  rfl

/-- Translation and positive dilation leave the critical dual Cameron–Martin bound unchanged. -/
theorem IsCMBounded.comp_affine {F : Rd d → ℝ} {C : ℝ} (hF : IsCMBounded F C)
    (_hcont : Continuous F) {r : ℝ} (hr : 0 < r) (z : Rd d) :
    IsCMBounded (fun x => F (r⁻¹ • (x - z))) C := by
  intro φ
  let ψ : TestRd d := testAffinePull r⁻¹ ((-r⁻¹) • z) φ.1
  have hψ0 : ∫ x, ψ x = 0 := integral_testAffinePull_eq_zero _ _ φ.2
  have hcomp : testAffinePull r z ψ = φ.1 := by
    dsimp [ψ]
    rw [testAffinePull_testAffinePull]
    have hrne : r ≠ 0 := hr.ne'
    have hprod : r * r⁻¹ = 1 := mul_inv_cancel₀ hrne
    have hz : r • ((-r⁻¹) • z) + z = 0 := by
      rw [smul_smul, mul_neg, hprod, neg_one_smul, neg_add_cancel]
    rw [hprod, hz, testAffinePull_one_zero, ContinuousLinearMap.id_apply]
  have hnorm : logNorm φ.1 = r ^ d * logNorm ψ := by
    rw [← hcomp]
    exact logNorm_testAffinePull ψ hψ0 hr z
  have hpair : (∫ x, F (r⁻¹ • (x - z)) * φ.1 x) =
      r ^ d * ∫ x, F x * ψ x := by
    have h := integral_testAffinePull_mul ψ hr z (fun x => F (r⁻¹ • (x - z)))
    simp only [hcomp, add_sub_cancel_right, smul_smul, inv_mul_cancel₀ hr.ne', one_smul] at h
    simpa only [mul_comm] using h
  rw [hpair, abs_mul, abs_of_pos (pow_pos hr _), hnorm]
  calc
    r ^ d * |∫ x, F x * ψ x| ≤ r ^ d * (C * logNorm ψ) :=
      mul_le_mul_of_nonneg_left (hF ⟨ψ, hψ0⟩) (pow_nonneg hr.le _)
    _ = C * (r ^ d * logNorm ψ) := by ring

end HigherDimLQGMetric
