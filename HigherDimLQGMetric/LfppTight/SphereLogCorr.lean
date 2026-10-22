import HigherDimLQGMetric.Sphere.Var

/-! The elementary logarithmic growth estimate for the sphere log covariance. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- `L(c) = ∬ log|u-v+c|⁻¹ dσ₁(u)dσ₁(v)`, written using the
already-formalized sphere potential. -/
def l6a_sphereLogCorr (d : ℕ) (c : Rd d) : ℝ :=
  ∫ u, sphPot d (u + c) ∂(unitSphereProb d)

theorem l6a_continuous_sphereLogCorr (d : ℕ) (hd : 2 ≤ d) :
    Continuous (l6a_sphereLogCorr d) := by
  have hs : ∀ᵐ u ∂(unitSphereProb d), u ∈ Metric.closedBall (0 : Rd d) 1 := by
    filter_upwards [ae_unitSphereProb_norm_le d] with u hu
    simpa only [Metric.mem_closedBall, dist_zero_right] using hu
  have hre : (unitSphereProb d).restrict (Metric.closedBall (0 : Rd d) 1) =
      unitSphereProb d := Measure.restrict_eq_self_of_ae_mem hs
  have hfunc : Continuous (fun p : Rd d × Rd d => sphPot d (p.2 + p.1)) :=
    (continuous_sphPot hd).comp (continuous_snd.add continuous_fst)
  have hc := continuous_parametric_integral_of_continuous
    (μ := unitSphereProb d) (f := fun c u => sphPot d (u + c)) hfunc
    (isCompact_closedBall (0 : Rd d) 1)
  rw [hre] at hc
  exact hc

/-- Growth of the sphere log covariance; this is the bound used to dominate
the two kernel integrals in MA5 A7(2). -/
theorem l6a_abs_sphereLogCorr_le (d : ℕ) (hd : 2 ≤ d) (c : Rd d) :
    |l6a_sphereLogCorr d c| ≤ 2 ^ d + Real.log (‖c‖ + 2) := by
  letI : IsProbabilityMeasure (unitSphereProb d) :=
    isProbabilityMeasure_unitSphereProb (by omega : 1 ≤ d)
  have hb : ∀ᵐ u ∂(unitSphereProb d),
      ‖sphPot d (u + c)‖ ≤ 2 ^ d + Real.log (‖c‖ + 2) := by
    filter_upwards [ae_unitSphereProb_norm_eq_one d] with u hu
    rw [Real.norm_eq_abs]
    have ht := norm_add_le u c
    have hlog : Real.log (‖u + c‖ + 1) ≤ Real.log (‖c‖ + 2) :=
      Real.log_le_log (by positivity) (by linarith)
    exact (abs_sphPot_le hd (u + c)).trans (add_le_add_right hlog _)
  have h := norm_integral_le_of_norm_le_const hb
  simpa only [l6a_sphereLogCorr, Real.norm_eq_abs, probReal_univ, mul_one] using h

/-- A separated two-variable envelope for the logarithmic covariance. -/
theorem l6a_abs_sphereLogCorr_sub_le (d : ℕ) (hd : 2 ≤ d)
    (a b : Rd d) :
    |l6a_sphereLogCorr d (a - b)| ≤
      2 ^ d + Real.log (2 + ‖a‖) + Real.log (2 + ‖b‖) := by
  have hnorm : ‖a - b‖ ≤ ‖a‖ + ‖b‖ := norm_sub_le a b
  have hmul : ‖a - b‖ + 2 ≤ (2 + ‖a‖) * (2 + ‖b‖) := by
    nlinarith [norm_nonneg a, norm_nonneg b, mul_nonneg (norm_nonneg a) (norm_nonneg b)]
  have hlog : Real.log (‖a - b‖ + 2) ≤
      Real.log (2 + ‖a‖) + Real.log (2 + ‖b‖) := by
    rw [← Real.log_mul (by positivity : 2 + ‖a‖ ≠ 0)
      (by positivity : 2 + ‖b‖ ≠ 0)]
    exact Real.log_le_log (by positivity) hmul
  linarith [l6a_abs_sphereLogCorr_le d hd (a - b)]

end HigherDimLQGMetric
