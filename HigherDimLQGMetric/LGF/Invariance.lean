import HigherDimLQGMetric.Field.LGFPlusCont
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic

/-!
# Translation and scale invariance of the whole-space LGF modulo constants (packet F2, target 3)

Source: `source/higher-dimensional-lqg-metric.pdf` l. 50–56 ([1] §1.1): the law of the whole-space
log-correlated field modulo additive constants is invariant under `x ↦ r x + z` (`r > 0`); MA0 §5.2
block A1 ("translation/scale invariance of the LGF modulo constants").

* `logCovRd_dim_zero`: in dimension `0` every log covariance vanishes;
* `logCovRd_affine`: for `r > 0`, `z ∈ ℝ^d` and `∫ ψ = 0`,
  `logCovRd φ((· - z)/r) ψ((· - z)/r) = r^{2d} logCovRd φ ψ` (change of variables in both integrals;
  the `log r` term dies because `ψ` has mean zero);
* `logCovRd_testAffinePull`: the same identity for the frozen pullback `testAffinePull`;
* `IsWholeSpaceLGF.affineComp`: `h(r · + z)` is again a whole-space LGF for `r > 0`.

Port of LQGMetric's `Field/GFFInvariance.lean` (`logCov_affine`, `IsWholePlaneGFF.affineComp`) from
`ℂ` (Jacobian `r²`) to `ℝ^d` (Jacobian `r^d`), with F1's change of variables
`integral_comp_affinePt` (ruling M10).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- In dimension `0` every log covariance vanishes: `‖x - y‖ = 0` and `log 0 = 0`. -/
theorem logCovRd_dim_zero (φ ψ : Rd 0 → ℝ) : logCovRd φ ψ = 0 := by
  unfold logCovRd
  have h : ∀ x y : Rd 0, φ x * (-Real.log ‖x - y‖) * ψ y = 0 := fun x y => by
    rw [Subsingleton.elim x y, sub_self, norm_zero, Real.log_zero, neg_zero, mul_zero, zero_mul]
  simp only [h, integral_zero]

/-- `∫ (a + b) = ∫ b` when `a` is integrable with `∫ a = 0` (both sides vanish if `b` is not
integrable). -/
theorem integral_add_of_integral_eq_zero {a b : Rd d → ℝ} (ha : Integrable a)
    (ha0 : ∫ x, a x = 0) : ∫ x, (a x + b x) = ∫ x, b x := by
  by_cases hb : Integrable b
  · rw [integral_add ha hb, ha0, zero_add]
  · have hab : ¬ Integrable (fun x => a x + b x) := fun h => hb
      ((h.sub ha).congr (ae_of_all _ fun x => by simp))
    rw [integral_undef hab, integral_undef hb]

/-- `∫ F = r^d ∫ F(r · + z)` for `r > 0`. -/
theorem integral_eq_pow_mul_integral_comp_affinePt (F : Rd d → ℝ) {r : ℝ} (hr : 0 < r)
    (z : Rd d) : ∫ y, F y = r ^ d * ∫ v, F (r • v + z) := by
  rw [integral_comp_affinePt F hr z, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]

/-- **Affine invariance of the log covariance on mean-zero functions**: for `r > 0` and `∫ ψ = 0`,
`logCovRd φ((· - z)/r) ψ((· - z)/r) = r^{2d} logCovRd φ ψ`. -/
theorem logCovRd_affine (φ ψ : Rd d → ℝ) (hψ : Integrable ψ) (hψ0 : ∫ y, ψ y = 0) {r : ℝ}
    (hr : 0 < r) (z : Rd d) :
    logCovRd (fun x => φ (r⁻¹ • (x - z))) (fun y => ψ (r⁻¹ • (y - z))) =
      r ^ (2 * d) * logCovRd φ ψ := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rw [logCovRd_dim_zero, logCovRd_dim_zero, mul_zero]
  have : NeZero d := ⟨hd.ne'⟩
  have hc : ∀ u : Rd d, r⁻¹ • (r • u + z - z) = u := fun u => by
    rw [add_sub_cancel_right, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
  have hinner : ∀ u : Rd d, ∫ y, φ (r⁻¹ • (r • u + z - z)) * (-Real.log ‖r • u + z - y‖) *
      ψ (r⁻¹ • (y - z)) = r ^ d * ∫ v, φ u * (-Real.log ‖u - v‖) * ψ v := by
    intro u
    rw [integral_eq_pow_mul_integral_comp_affinePt _ hr z]
    congr 1
    simp only [hc]
    have hae : (fun v => φ u * (-Real.log ‖r • u + z - (r • v + z)‖) * ψ v) =ᵐ[volume]
        fun v => φ u * (-Real.log r) * ψ v + φ u * (-Real.log ‖u - v‖) * ψ v := by
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 (measure_singleton u)] with v hv
      have huv : ‖u - v‖ ≠ 0 := by
        rw [norm_ne_zero_iff, sub_ne_zero]
        exact fun h => hv (h ▸ rfl)
      rw [show r • u + z - (r • v + z) = r • (u - v) by rw [smul_sub]; abel, norm_smul,
        Real.norm_eq_abs, abs_of_pos hr, Real.log_mul hr.ne' huv]
      ring
    have hint : Integrable fun v => φ u * (-Real.log r) * ψ v := hψ.const_mul _
    have hint0 : ∫ v, φ u * (-Real.log r) * ψ v = 0 := by
      rw [integral_const_mul, hψ0, mul_zero]
    rw [integral_congr_ae hae, integral_add_of_integral_eq_zero hint hint0]
  unfold logCovRd
  rw [integral_eq_pow_mul_integral_comp_affinePt _ hr z]
  simp only [hinner, integral_const_mul]
  ring

/-- `logCovRd` of affine pullbacks of test functions (`ψ` mean zero, `r > 0`). -/
theorem logCovRd_testAffinePull (φ ψ : TestRd d) (hψ0 : ∫ y, ψ y = 0) {r : ℝ} (hr : 0 < r)
    (z : Rd d) :
    logCovRd (testAffinePull r z φ) (testAffinePull r z ψ) = r ^ (2 * d) * logCovRd φ ψ := by
  have e : ∀ χ : TestRd d, ((testAffinePull r z χ : TestRd d) : Rd d → ℝ) =
      fun x => χ (r⁻¹ • (x - z)) := fun χ => funext fun x => testAffinePull_apply hr.ne' z χ x
  rw [e, e]
  exact logCovRd_affine _ _ (integrable_testOn ψ) hψ0 hr z

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- **Scale and translation invariance modulo constants** (target 3): if `h` is a whole-space LGF
then so is `h(r · + z)` for every `r > 0` and `z ∈ ℝ^d`. -/
theorem IsWholeSpaceLGF.affineComp {h : Ω → DistRd d} (hh : IsWholeSpaceLGF h P) {r : ℝ}
    (hr : 0 < r) (z : Rd d) : IsWholeSpaceLGF (fun ω => affineComp r z (h ω)) P where
  measurable := Measurable.affineComp hh.measurable r z
  gaussian := by
    have := (hh.gaussian.comp_right (testAffinePull0 r z)).smul (fun _ => (r ^ d)⁻¹)
    have e : (fun (φ : TestRd0 d) ω => HigherDimLQGMetric.affineComp r z (h ω) φ.1) =
        fun t ω => (r ^ d)⁻¹ • ((fun (φ : TestRd0 d) ω => h ω φ.1) ∘ testAffinePull0 r z) t ω := by
      funext φ ω
      simp only [affineComp_apply, Function.comp_apply, testAffinePull0_val, smul_eq_mul]
    rw [e]
    exact this
  centered := fun φ => by
    simp only [affineComp_apply]
    rw [integral_const_mul]
    have := hh.centered (testAffinePull0 r z φ)
    simp only [testAffinePull0_val] at this
    rw [this, mul_zero]
  covariance_eq := fun φ ψ => by
    simp only [affineComp_apply]
    rw [covariance_const_mul_left, covariance_const_mul_right]
    have := hh.covariance_eq (testAffinePull0 r z φ) (testAffinePull0 r z ψ)
    simp only [testAffinePull0_val] at this
    rw [this, logCovRd_testAffinePull φ.1 ψ.1 ψ.2 hr z]
    have hrd : r ^ d ≠ 0 := pow_ne_zero _ hr.ne'
    rw [pow_mul', sq]
    field_simp

end HigherDimLQGMetric
