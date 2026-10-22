import HigherDimLQGContinuity.Continuum.Scaling
import HigherDimLQGContinuity.Fatou.Basic
import HigherDimLQGContinuity.Fatou.Main

/-!
# Continuum crossing moments

The unit crossing moment from the Fatou passage and the exact scaling law give
moments of annular crossings at all centers and radii.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

theorem l2_measurable_cross {d : ℕ} {D : DistRd d → ContMetric d}
    (hD : Measurable D) (z : Rd d) (a b : ℝ) :
    Measurable (fun g => acrossDist (rho D g) z a b) := by
  exact (fatou_continuous_across z a b).measurable.comp
    (measurable_subtype_coe.comp (measurable_rho hD))

theorem l2_measurable_invCrossPow {d : ℕ} {D : DistRd d → ContMetric d}
    (hD : Measurable D) (z : Rd d) (a b q : ℝ) :
    Measurable (fun g => (acrossDist (rho D g) z a b)⁻¹ ^ q) :=
  (ENNReal.continuous_rpow_const.measurable.comp measurable_inv).comp
    (l2_measurable_cross hD z a b)

theorem l2_lintegral_gauss_factor_sq {d : ℕ} (hd : 2 ≤ d)
    {r : ℝ} (hr : 0 < r) (z : Rd d) (ξ q : ℝ) :
    (∫⁻ g, (ENNReal.ofReal (Real.exp (-q * ξ * sphereAvg g r z))) ^ (2 : ℝ)
      ∂(normLGFLaw d)) =
      ENNReal.ofReal
        (Real.exp (Var[fun g : DistRd d => sphereAvg g r z; normLGFLaw d] *
          (-2 * q * ξ) ^ 2 / 2)) := by
  have heq (g : DistRd d) :
      (ENNReal.ofReal (Real.exp (-q * ξ * sphereAvg g r z))) ^ (2 : ℝ) =
        ENNReal.ofReal (Real.exp ((-2 * q * ξ) * sphereAvg g r z)) := by
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by norm_num : 0 ≤ (2 : ℝ))]
    congr 1
    rw [← Real.exp_mul]
    congr 1
    ring
  simp_rw [heq]
  exact l2_lintegral_exp_sphereAvg hd hr z (-2 * q * ξ)

/-- Cauchy–Schwarz transfers the unit inverse crossing moment to one scaled shell. -/
theorem l2_cross_scaled_moment {d : ℕ} (hd : 2 ≤ d)
    {ξ : ℝ} (hξ : 0 < ξ) {D : DistRd d → ContMetric d}
    (hD : IsStrongExpMetric d ξ (distExp d ξ) D)
    {r : ℝ} (hr : 0 < r) (z : Rd d) {q : ℝ} (hq : 0 < q) :
    (∫⁻ g, (acrossDist (rho D g) z r (2 * r))⁻¹ ^ q ∂(normLGFLaw d)) ≤
      (ENNReal.ofReal (r ^ (ξ * distExp d ξ)))⁻¹ ^ q *
        (ENNReal.ofReal
          (Real.exp (Var[fun g : DistRd d => sphereAvg g r z; normLGFLaw d] *
            (-2 * q * ξ) ^ 2 / 2))) ^ (1 / 2 : ℝ) *
        (∫⁻ g, (acrossDist (rho D g) 0 1 2)⁻¹ ^ (2 * q) ∂(normLGFLaw d)) ^
          (1 / 2 : ℝ) := by
  let f : DistRd d → ℝ≥0∞ := fun g =>
    ENNReal.ofReal (Real.exp (-q * ξ * sphereAvg g r z))
  let h : DistRd d → ℝ≥0∞ := fun g =>
    (acrossDist (rho D (recentre 1 r z g)) 0 1 2)⁻¹ ^ q
  have hf : Measurable f := by
    dsimp [f]
    exact ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp
        (measurable_const.mul (measurable_sphereAvg_left r z)))
  have hh : Measurable h := by
    dsimp [h]
    exact (l2_measurable_invCrossPow hD.measurable 0 1 2 q).comp
      (measurable_recentre 1 r z)
  have hscale := l2_across_scaling hd hξ hD hr z 1 2
  have hpoint : ∀ᵐ g ∂(normLGFLaw d),
      (acrossDist (rho D g) z r (2 * r))⁻¹ ^ q =
        (ENNReal.ofReal (r ^ (ξ * distExp d ξ)))⁻¹ ^ q * f g * h g := by
    filter_upwards [hscale] with g hg
    have hs : ENNReal.ofReal (scaleS d ξ 1 r z g) ≠ 0 :=
      (ENNReal.ofReal_pos.mpr (scaleS_pos d ξ 1 hr z g)).ne'
    have hg' : acrossDist (rho D g) z r (2 * r) =
        ENNReal.ofReal (scaleS d ξ 1 r z g) *
          acrossDist (rho D (recentre 1 r z g)) 0 1 2 := by
      simpa only [mul_one, mul_comm r 2] using hg
    rw [hg', ENNReal.mul_inv (Or.inl hs) (Or.inl ENNReal.ofReal_ne_top),
      ENNReal.mul_rpow_of_nonneg _ _ hq.le, l2_scaleS_inv_rpow ξ q hξ hq.le hr z g]
  calc
    (∫⁻ g, (acrossDist (rho D g) z r (2 * r))⁻¹ ^ q ∂(normLGFLaw d)) =
        ∫⁻ g, (ENNReal.ofReal (r ^ (ξ * distExp d ξ)))⁻¹ ^ q * f g * h g
          ∂(normLGFLaw d) := lintegral_congr_ae hpoint
    _ = (ENNReal.ofReal (r ^ (ξ * distExp d ξ)))⁻¹ ^ q *
        (∫⁻ g, f g * h g ∂(normLGFLaw d)) := by
      simpa only [Pi.mul_apply, mul_assoc] using
        (lintegral_const_mul
          ((ENNReal.ofReal (r ^ (ξ * distExp d ξ)))⁻¹ ^ q) (hf.mul hh))
    _ ≤ (ENNReal.ofReal (r ^ (ξ * distExp d ξ)))⁻¹ ^ q *
        ((∫⁻ g, f g ^ (2 : ℝ) ∂(normLGFLaw d)) ^ (1 / 2 : ℝ) *
        (∫⁻ g, h g ^ (2 : ℝ) ∂(normLGFLaw d)) ^ (1 / 2 : ℝ)) := by
      gcongr
      exact ENNReal.lintegral_mul_le_Lp_mul_Lq (normLGFLaw d)
        Real.HolderConjugate.two_two hf.aemeasurable hh.aemeasurable
    _ = _ := by
      rw [l2_lintegral_gauss_factor_sq hd hr z ξ q]
      have hrec : (∫⁻ g, h g ^ (2 : ℝ) ∂(normLGFLaw d)) =
          ∫⁻ g, (acrossDist (rho D g) 0 1 2)⁻¹ ^ (2 * q) ∂(normLGFLaw d) := by
        have heq (g : DistRd d) : h g ^ (2 : ℝ) =
            (acrossDist (rho D (recentre 1 r z g)) 0 1 2)⁻¹ ^ (2 * q) := by
          dsimp [h]
          rw [← ENNReal.rpow_mul]
          congr 1
          ring
        simp_rw [heq]
        exact l2_lintegral_recentre hd hr z _
          (l2_measurable_invCrossPow hD.measurable 0 1 2 (2 * q))
      rw [hrec]
      exact (mul_assoc _ _ _).symm

/-- The unit inverse moment of packet L1 gives one constant for all parameters in the window. -/
theorem continuum_scaled_invCross {d : ℕ} (hd : 3 ≤ d) {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (hC1 : ConvUpperMomentShape d κ) (hC2 : ConvInvCrossShape d κ)
    {b μ : ℝ} (hb : 0 < b) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    {q : ℝ} (hq : 0 < q) :
    ∃ C : ℝ, ∀ ξ : ℝ, UHyp d κ b μ ξ →
      ∀ D : DistRd d → ContMetric d,
        IsStrongExpMetric d ξ (distExp d ξ) D →
        ∀ (z : Rd d) (r : ℝ), 0 < r →
          (∫⁻ g, (acrossDist (rho D g) z r (2 * r))⁻¹ ^ q
            ∂(normLGFLaw d)) ≤
          (ENNReal.ofReal (r ^ (ξ * distExp d ξ)))⁻¹ ^ q *
            (ENNReal.ofReal
              (Real.exp (Var[fun g : DistRd d => sphereAvg g r z; normLGFLaw d] *
                (-2 * q * ξ) ^ 2 / 2))) ^ (1 / 2 : ℝ) *
            (ENNReal.ofReal C) ^ (1 / 2 : ℝ) := by
  obtain ⟨C, hC⟩ := continuum_invCross hd hκ hC1 hC2 hb hμ hμ1
    (0 : Rd d) (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) < 2)
    (by linarith : 0 < 2 * q)
  refine ⟨C, fun ξ hξ D hD z r hr => ?_⟩
  exact (l2_cross_scaled_moment (show 2 ≤ d by omega) hξ.base.xi_pos hD hr z hq).trans (by
    gcongr
    exact hC ξ hξ D hD)

end HigherDimLQGContinuity
