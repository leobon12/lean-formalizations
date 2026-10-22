import HigherDimLQGContinuity.Fatou.Log
import HigherDimLQGMetric.Sharp.ShellScaling

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd e₁)

/-- Multiplication by the mean-log normalization preserves the upper envelope. -/
theorem fatou_rho_upper {d : ℕ} {D : DistRd d → ContMetric d}
    {M C A p σ R : ℝ} (hM : |logMean D| ≤ M)
    {H : DistRd d → ℝ} (hHm : Measurable H) (hH1 : ∀ g, 1 ≤ H g)
    (hHmom : ∫⁻ g, ENNReal.ofReal (H g ^ p) ∂(normLGFLaw d) ≤
      ENNReal.ofReal (C * (1 + R) ^ A))
    (hHpt : ∀ᵐ g ∂(normLGFLaw d), ∀ z ∈ closedBall (0 : Rd d) R,
      ∀ s ∈ Ioc (0 : ℝ) 1,
        internalDiamRd (D g) (ball z s) (ball z (2 * s)) ≤
          ENNReal.ofReal (H g * s ^ σ)) :
    ∃ H' : DistRd d → ℝ, Measurable H' ∧ (∀ g, 1 ≤ H' g) ∧
      (∫⁻ g, ENNReal.ofReal (H' g ^ p) ∂(normLGFLaw d) ≤
        ENNReal.ofReal ((Real.exp M ^ p * C) * (1 + R) ^ A)) ∧
      ∀ᵐ g ∂(normLGFLaw d), ∀ z ∈ closedBall (0 : Rd d) R,
        ∀ s ∈ Ioc (0 : ℝ) 1,
          internalDiamRd (rho D g) (ball z s) (ball z (2 * s)) ≤
            ENNReal.ofReal (H' g * s ^ σ) := by
  let E := Real.exp M
  have hM0 : 0 ≤ M := (abs_nonneg _).trans hM
  have hE1 : 1 ≤ E := by simpa only [E, Real.exp_zero] using Real.exp_le_exp.mpr hM0
  have hEpos : 0 < E := lt_of_lt_of_le zero_lt_one hE1
  have ha : Real.exp (-logMean D) ≤ E :=
    Real.exp_le_exp.mpr ((neg_le_iff_add_nonneg).2 (by linarith [neg_abs_le (logMean D)]))
  refine ⟨fun g => E * H g, hHm.const_mul E, fun g => ?_, ?_, ?_⟩
  · nlinarith [hH1 g]
  · have heq (g : DistRd d) : (E * H g) ^ p = E ^ p * H g ^ p :=
      Real.mul_rpow hEpos.le (by linarith [hH1 g])
    calc
      (∫⁻ g, ENNReal.ofReal ((E * H g) ^ p) ∂(normLGFLaw d)) =
          ∫⁻ g, ENNReal.ofReal (E ^ p) * ENNReal.ofReal (H g ^ p) ∂(normLGFLaw d) := by
        congr 1
        funext g
        rw [heq, ENNReal.ofReal_mul (Real.rpow_nonneg hEpos.le _)]
      _ = ENNReal.ofReal (E ^ p) *
          (∫⁻ g, ENNReal.ofReal (H g ^ p) ∂(normLGFLaw d)) :=
        lintegral_const_mul _ ((hHm.pow_const p).ennreal_ofReal)
      _ ≤ ENNReal.ofReal (E ^ p) * ENNReal.ofReal (C * (1 + R) ^ A) := by gcongr
      _ = ENNReal.ofReal ((E ^ p * C) * (1 + R) ^ A) := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hEpos.le _)]
        congr 1
        ring
  · filter_upwards [hHpt] with g hg z hz s hs
    have hsp : 0 ≤ s ^ σ := Real.rpow_nonneg hs.1.le _
    have hprod : 0 ≤ H g * s ^ σ := mul_nonneg (by linarith [hH1 g]) hsp
    calc
      internalDiamRd (rho D g) (ball z s) (ball z (2 * s)) =
          ENNReal.ofReal (Real.exp (-logMean D)) *
            internalDiamRd (D g) (ball z s) (ball z (2 * s)) :=
        fatou_internalDiam_smul (D g) (Real.exp_pos _) _ _
      _ ≤ ENNReal.ofReal (Real.exp (-logMean D)) *
          ENNReal.ofReal (H g * s ^ σ) := by gcongr; exact hg z hz s hs
      _ ≤ ENNReal.ofReal E * ENNReal.ofReal (H g * s ^ σ) := by gcongr
      _ = ENNReal.ofReal ((E * H g) * s ^ σ) := by
        rw [← ENNReal.ofReal_mul hEpos.le]
        congr 1
        ring

/-- The inverse crossing moment changes by a controlled deterministic factor. -/
theorem fatou_rho_invCross {d : ℕ} {D : DistRd d → ContMetric d}
    {M C q a c : ℝ} (hD : Measurable D) (hM : |logMean D| ≤ M) (hq : 0 < q)
    (z : Rd d)
    (hJ : ∫⁻ g, (acrossDist (D g) z a c)⁻¹ ^ q ∂(normLGFLaw d) ≤
      ENNReal.ofReal C) :
    ∫⁻ g, (acrossDist (rho D g) z a c)⁻¹ ^ q ∂(normLGFLaw d) ≤
      ENNReal.ofReal (Real.exp M ^ q * C) := by
  let k := Real.exp (-logMean D)
  have hk : 0 < k := Real.exp_pos _
  have hcoef : (ENNReal.ofReal k)⁻¹ ^ q ≤ ENNReal.ofReal (Real.exp M ^ q) := by
    calc
      (ENNReal.ofReal k)⁻¹ ^ q = ENNReal.ofReal (k⁻¹ ^ q) := by
        have h1 : ENNReal.ofReal (k⁻¹) = (ENNReal.ofReal k)⁻¹ :=
          ENNReal.ofReal_inv_of_pos hk
        have h2 : ENNReal.ofReal (k⁻¹ ^ q) = (ENNReal.ofReal (k⁻¹)) ^ q :=
          (ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.mpr hk.le) hq.le).symm
        rw [h2, h1]
      _ ≤ ENNReal.ofReal (Real.exp M ^ q) := by
        apply ENNReal.ofReal_le_ofReal
        apply Real.rpow_le_rpow (inv_nonneg.mpr hk.le) _ hq.le
        change (Real.exp (-logMean D))⁻¹ ≤ Real.exp M
        calc
          (Real.exp (-logMean D))⁻¹ = Real.exp (logMean D) := by
            rw [Real.exp_neg, inv_inv]
          _ ≤ Real.exp M :=
            Real.exp_le_exp.mpr (le_trans (le_abs_self _) hM)
  calc
    (∫⁻ g, (acrossDist (rho D g) z a c)⁻¹ ^ q ∂(normLGFLaw d)) =
        ∫⁻ g, (ENNReal.ofReal k)⁻¹ ^ q *
          (acrossDist (D g) z a c)⁻¹ ^ q ∂(normLGFLaw d) := by
      congr 1
      funext g
      change (acrossDist ((D g).smul k hk) z a c)⁻¹ ^ q = _
      rw [acrossDist_smul hk,
        ENNReal.mul_inv (Or.inl (ENNReal.ofReal_pos.mpr hk).ne')
          (Or.inl ENNReal.ofReal_ne_top),
        ENNReal.mul_rpow_of_nonneg _ _ hq.le]
    _ = (ENNReal.ofReal k)⁻¹ ^ q *
        (∫⁻ g, (acrossDist (D g) z a c)⁻¹ ^ q ∂(normLGFLaw d)) := by
      rw [lintegral_const_mul]
      exact ((ENNReal.continuous_rpow_const.measurable.comp
        (measurable_inv.comp
          ((fatou_continuous_across z a c).measurable.comp
            (measurable_subtype_coe.comp hD)))))
    _ ≤ ENNReal.ofReal (Real.exp M ^ q) * ENNReal.ofReal C := by gcongr
    _ = ENNReal.ofReal (Real.exp M ^ q * C) := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (Real.exp_pos _).le _)]

end HigherDimLQGContinuity
