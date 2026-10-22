import HigherDimLQGMetric.Kernel.CovLogMoment

/-! A quantitative logarithmic energy bound for a finite measure. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

private theorem abs_log_norm_sub_bound {d : ℕ} (x y : Rd d) :
    |Real.log ‖x - y‖| ≤
      max 0 (-Real.log ‖x - y‖) +
        Real.log (2 + ‖x‖) + Real.log (2 + ‖y‖) := by
  have hx : 0 ≤ Real.log (2 + ‖x‖) :=
    Real.log_nonneg (by nlinarith [norm_nonneg x])
  have hy : 0 ≤ Real.log (2 + ‖y‖) :=
    Real.log_nonneg (by nlinarith [norm_nonneg y])
  have hnorm : ‖x - y‖ ≤ ‖x‖ + ‖y‖ := norm_sub_le _ _
  have hmul : ‖x - y‖ ≤ (2 + ‖x‖) * (2 + ‖y‖) := by
    nlinarith [norm_nonneg x, norm_nonneg y,
      mul_nonneg (norm_nonneg x) (norm_nonneg y)]
  have hlog : Real.log ‖x - y‖ ≤
      Real.log (2 + ‖x‖) + Real.log (2 + ‖y‖) := by
    rw [← Real.log_mul (by positivity : 2 + ‖x‖ ≠ 0)
      (by positivity : 2 + ‖y‖ ≠ 0)]
    by_cases hxy : x = y
    · subst y
      simp only [sub_self, norm_zero, Real.log_zero]
      exact Real.log_nonneg (by nlinarith [norm_nonneg x])
    · exact Real.log_le_log (norm_sub_pos_iff.mpr hxy) hmul
  by_cases h : Real.log ‖x - y‖ ≤ 0
  · rw [abs_of_nonpos h]
    have hmax : -Real.log ‖x - y‖ ≤ max 0 (-Real.log ‖x - y‖) :=
      le_max_right _ _
    linarith
  · rw [abs_of_pos (lt_of_not_ge h)]
    have hmax : 0 ≤ max 0 (-Real.log ‖x - y‖) := le_max_left _ _
    linarith

/-- Uniform absolute log energy from a linear small-ball estimate and a log moment. -/
theorem l6a_abs_log_energy_le {d : ℕ}
    {lam : Measure (Rd d)} [IsFiniteMeasure lam] {A : ℝ} (hA : 0 ≤ A)
    (hball : ∀ z : Rd d, ∀ s > 0, lam.real (Metric.closedBall z s) ≤ A * s)
    (hmoment : Integrable (fun z : Rd d => Real.log (2 + ‖z‖)) lam) :
    (∫ p : Rd d × Rd d, |Real.log ‖p.1 - p.2‖| ∂(lam.prod lam)) ≤
      A * lam.real univ +
        2 * lam.real univ *
          (∫ z : Rd d, Real.log (2 + ‖z‖) ∂lam) := by
  let N : Rd d × Rd d → ℝ := fun p => max 0 (-Real.log ‖p.1 - p.2‖)
  let W : Rd d → ℝ := fun z => Real.log (2 + ‖z‖)
  have hlog : Integrable (fun p : Rd d × Rd d => Real.log ‖p.1 - p.2‖)
      (lam.prod lam) :=
    integrable_log_norm_sub_of_smallBall_logMoment hA hball hmoment
  have hN : Integrable N (lam.prod lam) := (integrable_const 0).sup hlog.neg
  have hAbs : Integrable (fun p : Rd d × Rd d => |Real.log ‖p.1 - p.2‖|)
      (lam.prod lam) := by
    convert hlog.norm using 1
    funext p
    exact Real.norm_eq_abs _
  have hW : Integrable W lam := hmoment
  have hEnv : Integrable (fun p : Rd d × Rd d => N p + W p.1 + W p.2)
      (lam.prod lam) :=
    ((hN.add (hW.comp_fst lam)).add (hW.comp_snd lam))
  have hNle : (∫ p : Rd d × Rd d, N p ∂(lam.prod lam)) ≤
      A * lam.real univ := by
    have hpt (x : Rd d) :
        (∫⁻ y, ENNReal.ofReal (N (x, y)) ∂lam) ≤ ENNReal.ofReal A := by
      exact HigherDimLFPP.FieldAux.lintegral_log_inv_le hA hball x
    have hle : ENNReal.ofReal (∫ p : Rd d × Rd d, N p ∂(lam.prod lam)) ≤
        ENNReal.ofReal (A * lam.real univ) := by
      rw [ofReal_integral_eq_lintegral_ofReal hN
        (ae_of_all _ fun p => le_max_left _ _)]
      rw [lintegral_prod _ (by fun_prop)]
      calc
        (∫⁻ x, ∫⁻ y, ENNReal.ofReal (N (x, y)) ∂lam ∂lam) ≤
            ∫⁻ _x, ENNReal.ofReal A ∂lam := lintegral_mono hpt
        _ = ENNReal.ofReal (A * lam.real univ) := by
          rw [lintegral_const]
          simp only [measureReal_def]
          rw [ENNReal.ofReal_mul hA]
          simp
    exact (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg hA measureReal_nonneg)).1 hle
  have hEnvEq : (∫ p : Rd d × Rd d,
      N p + W p.1 + W p.2 ∂(lam.prod lam)) =
      (∫ p : Rd d × Rd d, N p ∂(lam.prod lam)) +
        2 * lam.real univ * (∫ z : Rd d, W z ∂lam) := by
    have h1 : (∫ p : Rd d × Rd d,
        (N p + W p.1) + W p.2 ∂(lam.prod lam)) =
        (∫ p : Rd d × Rd d, N p + W p.1 ∂(lam.prod lam)) +
          ∫ p : Rd d × Rd d, W p.2 ∂(lam.prod lam) :=
      integral_add (hN.add (hW.comp_fst lam)) (hW.comp_snd lam)
    have h2 : (∫ p : Rd d × Rd d, N p + W p.1 ∂(lam.prod lam)) =
        (∫ p : Rd d × Rd d, N p ∂(lam.prod lam)) +
          ∫ p : Rd d × Rd d, W p.1 ∂(lam.prod lam) :=
      integral_add hN (hW.comp_fst lam)
    rw [h1, h2, integral_fun_fst, integral_fun_snd]
    simp only [smul_eq_mul]
    ring
  calc
    (∫ p : Rd d × Rd d, |Real.log ‖p.1 - p.2‖| ∂(lam.prod lam)) ≤
        ∫ p : Rd d × Rd d, N p + W p.1 + W p.2 ∂(lam.prod lam) :=
      integral_mono hAbs hEnv (fun p => abs_log_norm_sub_bound p.1 p.2)
    _ = (∫ p : Rd d × Rd d, N p ∂(lam.prod lam)) +
        2 * lam.real univ * (∫ z : Rd d, W z ∂lam) := hEnvEq
    _ ≤ A * lam.real univ +
        2 * lam.real univ * (∫ z : Rd d, Real.log (2 + ‖z‖) ∂lam) := by
      simpa only [W] using add_le_add hNle le_rfl

end HigherDimLQGMetric
