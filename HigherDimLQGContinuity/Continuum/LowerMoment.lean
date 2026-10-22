import HigherDimLQGContinuity.Continuum.LowerDet
import HigherDimLQGContinuity.Param.Lipschitz

/-! Small-scale crossing moments for the continuum lower modulus. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

theorem l2_log_norm_le {d : ℕ} {R : ℝ} (hR : 1 ≤ R)
    {z : Rd d} (hz : ‖z‖ ≤ R + 2) :
    max 0 (Real.log ‖z‖) ≤ Real.log (R + 3) := by
  have hRp : 0 < R + 3 := by linarith
  have hR1 : 1 ≤ R + 3 := by linarith
  have hlog0 : 0 ≤ Real.log (R + 3) := Real.log_nonneg hR1
  apply max_le hlog0
  by_cases hz0 : ‖z‖ = 0
  · simp [hz0, hlog0]
  · have hzp : 0 < ‖z‖ := lt_of_le_of_ne (norm_nonneg z) (Ne.symm hz0)
    exact Real.log_le_log hzp (by linarith)

theorem l2_gauss_small {d : ℕ} {z : Rd d} {b q r ξ R K : ℝ}
    (hb : 0 < b) (hξ : 0 ≤ ξ) (hξb : ξ ≤ b)
    (hr : 0 < r) (hr1 : r ≤ 1) (hR : 1 ≤ R)
    (hv : Var[fun g : DistRd d => sphereAvg g r z; normLGFLaw d] ≤
      Real.log (1 / r) + 2 * Real.log (R + 3) + K) :
    (ENNReal.ofReal
      (Real.exp (Var[fun g : DistRd d => sphereAvg g r z; normLGFLaw d] *
        (-2 * q * ξ) ^ 2 / 2))) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (Real.exp (q ^ 2 * b ^ 2 * max 0 K) *
        (1 / r) ^ (q ^ 2 * b ^ 2) * (R + 3) ^ (2 * q ^ 2 * b ^ 2)) := by
  have hvar : 0 ≤ Var[fun g : DistRd d => sphereAvg g r z; normLGFLaw d] :=
    variance_nonneg _ _
  have hξ2 : ξ ^ 2 ≤ b ^ 2 := by nlinarith
  have hq2 : 0 ≤ q ^ 2 := sq_nonneg _
  have hinv : 0 < 1 / r := by positivity
  have hR3 : 0 < R + 3 := by linarith
  have hlogs : 0 ≤ Real.log (1 / r) := Real.log_nonneg ((one_le_div hr).2 hr1)
  have hlogR : 0 ≤ Real.log (R + 3) := Real.log_nonneg (by linarith)
  have hvar' : Var[fun g : DistRd d => sphereAvg g r z; normLGFLaw d] ≤
      Real.log (1 / r) + 2 * Real.log (R + 3) + max 0 K := by
    linarith [le_max_right (0 : ℝ) K]
  have hmain :
      (Var[fun g : DistRd d => sphereAvg g r z; normLGFLaw d] *
        (-2 * q * ξ) ^ 2 / 2) * (1 / 2 : ℝ) ≤
        q ^ 2 * b ^ 2 * (Real.log (1 / r) + 2 * Real.log (R + 3) + max 0 K) := by
    have hsum : 0 ≤ Real.log (1 / r) + 2 * Real.log (R + 3) + max 0 K := by positivity
    nlinarith [mul_nonneg (sub_nonneg.mpr hvar') (mul_nonneg hq2 (sq_nonneg ξ)),
      mul_nonneg (sub_nonneg.mpr hξ2) (mul_nonneg hq2 hsum)]
  have hreal : Real.exp ((Var[fun g : DistRd d => sphereAvg g r z; normLGFLaw d] *
      (-2 * q * ξ) ^ 2 / 2) * (1 / 2 : ℝ)) ≤
      Real.exp (q ^ 2 * b ^ 2 * max 0 K) *
        (1 / r) ^ (q ^ 2 * b ^ 2) * (R + 3) ^ (2 * q ^ 2 * b ^ 2) := by
    rw [Real.rpow_def_of_pos hinv, Real.rpow_def_of_pos hR3,
      ← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [hmain]
  rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by norm_num : 0 ≤ (1 / 2 : ℝ)),
    ← Real.exp_mul]
  exact ENNReal.ofReal_le_ofReal hreal

theorem l2_small_power {r a q e : ℝ} (hr : 0 < r) :
    ((r ^ a)⁻¹) ^ q * (1 / r) ^ e = r ^ (-(a * q + e)) := by
  rw [one_div, ← Real.rpow_neg hr.le a,
    ← Real.rpow_neg_eq_inv_rpow r e,
    ← Real.rpow_mul hr.le, ← Real.rpow_add hr]
  congr 1
  ring

/-- Uniform inverse-crossing moments at small radii and bounded centers. -/
theorem continuum_smallCross_moment {d : ℕ} (hd : 3 ≤ d) {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (hC1 : ConvUpperMomentShape d κ) (hC2 : ConvInvCrossShape d κ)
    {b μ q : ℝ} (hb : 0 < b) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hq : 0 < q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : ℝ, UHyp d κ b μ ξ →
      ∀ D : DistRd d → ContMetric d,
        IsStrongExpMetric d ξ (distExp d ξ) D →
        ∀ (R : ℝ), 1 ≤ R → ∀ (z : Rd d), ‖z‖ ≤ R + 2 →
          ∀ (r : ℝ), 0 < r → r ≤ 1 →
            (∫⁻ g, (acrossDist (rho D g) z r (2 * r))⁻¹ ^ q
              ∂(normLGFLaw d)) ≤
              ENNReal.ofReal (C * r ^ (-(q * (1 + Real.sqrt (2 * d) * b) + q ^ 2 * b ^ 2)) *
                (R + 3) ^ (2 * q ^ 2 * b ^ 2)) := by
  obtain ⟨C₀, hC₀⟩ := continuum_scaled_invCross hd hκ hC1 hC2 hb hμ hμ1 hq
  obtain ⟨K₀, hK₀⟩ := exists_variance_sphereAvg_pinLaw_le (show 2 ≤ d by omega)
  let B : ℝ := max 1 C₀
  let E : ℝ := Real.exp (q ^ 2 * b ^ 2 * max 0 K₀)
  let C : ℝ := E * B ^ (1 / 2 : ℝ)
  have hB : 0 ≤ B := (zero_le_one.trans (le_max_left _ _))
  have hC₀B : C₀ ≤ B := le_max_right _ _
  have hC : 0 ≤ C := by dsimp [C, E]; positivity
  refine ⟨C, hC, fun ξ hξ D hD R hR z hz r hr hr1 => ?_⟩
  have hξpos : 0 < ξ := hξ.base.xi_pos
  let a : ℝ := 1 + Real.sqrt (2 * d) * b
  let e : ℝ := q ^ 2 * b ^ 2
  let f : ℝ := 2 * q ^ 2 * b ^ 2
  have hphi : ξ * distExp d ξ ≤ a := by
    have hh := phiXi_le_one_add_sqrt_mul (show 2 ≤ d by omega) hξpos.le
    rw [phiXi_of_pos hξpos] at hh
    dsimp [a]
    have hroot : 0 ≤ Real.sqrt (2 * d) := Real.sqrt_nonneg _
    nlinarith [hξ.le_b]
  have hvar : Var[fun g : DistRd d => sphereAvg g r z; normLGFLaw d] ≤
      Real.log (1 / r) + 2 * Real.log (R + 3) + K₀ := by
    have hh := (hK₀ one_pos hr z).1 hr1
    rw [pinLaw_one (show 2 ≤ d by omega)] at hh
    have hnorm := l2_log_norm_le hR hz
    simp only [div_one] at hh
    linarith
  have hgauss := l2_gauss_small (q := q) (R := R) (K := K₀)
    hb hξpos.le hξ.le_b hr hr1 hR hvar
  have hinv : (ENNReal.ofReal (r ^ (ξ * distExp d ξ)))⁻¹ ^ q ≤
      (ENNReal.ofReal (r ^ a))⁻¹ ^ q := by
    have hpow : r ^ a ≤ r ^ (ξ * distExp d ξ) :=
      Real.rpow_le_rpow_of_exponent_ge hr hr1 hphi
    exact ENNReal.rpow_le_rpow
      (ENNReal.inv_le_inv.mpr (ENNReal.ofReal_le_ofReal hpow)) hq.le
  have hCpow : (ENNReal.ofReal C₀) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (B ^ (1 / 2 : ℝ)) := by
    calc
      (ENNReal.ofReal C₀) ^ (1 / 2 : ℝ) ≤
          (ENNReal.ofReal B) ^ (1 / 2 : ℝ) := by gcongr
      _ = ENNReal.ofReal (B ^ (1 / 2 : ℝ)) := by
        rw [ENNReal.ofReal_rpow_of_nonneg hB (by norm_num : 0 ≤ (1 / 2 : ℝ))]
  have hmain := hC₀ ξ hξ D hD z r hr
  calc
    (∫⁻ g, (acrossDist (rho D g) z r (2 * r))⁻¹ ^ q ∂(normLGFLaw d)) ≤
        (ENNReal.ofReal (r ^ (ξ * distExp d ξ)))⁻¹ ^ q *
          (ENNReal.ofReal
            (Real.exp (Var[fun g : DistRd d => sphereAvg g r z; normLGFLaw d] *
              (-2 * q * ξ) ^ 2 / 2))) ^ (1 / 2 : ℝ) *
          (ENNReal.ofReal C₀) ^ (1 / 2 : ℝ) := hmain
    _ ≤ (ENNReal.ofReal (r ^ a))⁻¹ ^ q *
        ENNReal.ofReal (E * (1 / r) ^ e * (R + 3) ^ f) *
        ENNReal.ofReal (B ^ (1 / 2 : ℝ)) := by gcongr
    _ = ENNReal.ofReal (C * r ^ (-(a * q + e)) * (R + 3) ^ f) := by
      rw [← ENNReal.ofReal_inv_of_pos (Real.rpow_pos_of_pos hr a),
        ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.mpr (Real.rpow_nonneg hr.le a)) hq.le,
        ← ENNReal.ofReal_mul (Real.rpow_nonneg (inv_nonneg.mpr (Real.rpow_nonneg hr.le a)) _),
        ← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg (inv_nonneg.mpr
          (Real.rpow_nonneg hr.le a)) _) (by positivity : 0 ≤ E * (1 / r) ^ e * (R + 3) ^ f))]
      congr 1
      have hrearrange : ((r ^ a)⁻¹) ^ q * (E * (1 / r) ^ e * (R + 3) ^ f) *
          B ^ (1 / 2 : ℝ) = C * (((r ^ a)⁻¹) ^ q * (1 / r) ^ e) * (R + 3) ^ f := by
        dsimp [C]
        ring
      rw [hrearrange]
      rw [l2_small_power hr]
    _ = ENNReal.ofReal (C * r ^ (-(q * (1 + Real.sqrt (2 * d) * b) + q ^ 2 * b ^ 2)) *
          (R + 3) ^ (2 * q ^ 2 * b ^ 2)) := by
      dsimp [a, e, f]
      congr 2
      ring_nf

/-- Each weighted shell contributes at most order `r^(d+1)` to the inverse envelope. -/
theorem continuum_weightedCross_moment {d : ℕ} (hd : 3 ≤ d) {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (hC1 : ConvUpperMomentShape d κ) (hC2 : ConvInvCrossShape d κ)
    {b μ q β : ℝ} (hb : 0 < b) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hq : 0 < q)
    (hβ : 1 ≤ q * (β - 1 - Real.sqrt (2 * d) * b) - q ^ 2 * b ^ 2 - d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : ℝ, UHyp d κ b μ ξ →
      ∀ D : DistRd d → ContMetric d,
        IsStrongExpMetric d ξ (distExp d ξ) D →
        ∀ (R : ℝ), 1 ≤ R → ∀ (z : Rd d), ‖z‖ ≤ R + 2 →
          ∀ (r : ℝ), 0 < r → r ≤ 1 →
            (∫⁻ g, (ENNReal.ofReal (r ^ β) *
              (acrossDist (rho D g) z r (2 * r))⁻¹) ^ q
              ∂(normLGFLaw d)) ≤
              ENNReal.ofReal (C * (R + 3) ^ (2 * q ^ 2 * b ^ 2) *
                r ^ ((d : ℝ) + 1)) := by
  obtain ⟨C, hC0, hC⟩ := continuum_smallCross_moment hd hκ hC1 hC2 hb hμ hμ1 hq
  refine ⟨C, hC0, fun ξ hξ D hD R hR z hz r hr hr1 => ?_⟩
  let a : ℝ := q * (1 + Real.sqrt (2 * d) * b) + q ^ 2 * b ^ 2
  let f : ℝ := 2 * q ^ 2 * b ^ 2
  let lam : ℝ := β * q - a
  have hlam : (d : ℝ) + 1 ≤ lam := by
    dsimp [lam, a]
    linarith
  have hpow : r ^ (β * q) * r ^ (-a) ≤ r ^ ((d : ℝ) + 1) := by
    have heq : r ^ (β * q) * r ^ (-a) = r ^ lam := by
      rw [← Real.rpow_add hr]
      congr 1
    rw [heq]
    exact Real.rpow_le_rpow_of_exponent_ge hr hr1 hlam
  have hsmall := hC ξ hξ D hD R hR z hz r hr hr1
  have hmeas := l2_measurable_invCrossPow hD.measurable z r (2 * r) q
  have heq (g : DistRd d) :
      (ENNReal.ofReal (r ^ β) *
        (acrossDist (rho D g) z r (2 * r))⁻¹) ^ q =
      ENNReal.ofReal (r ^ (β * q)) *
        (acrossDist (rho D g) z r (2 * r))⁻¹ ^ q := by
    rw [ENNReal.mul_rpow_of_nonneg _ _ hq.le,
      ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hr.le β) hq.le,
      ← Real.rpow_mul hr.le]
  simp_rw [heq]
  calc
    (∫⁻ g, ENNReal.ofReal (r ^ (β * q)) *
      (acrossDist (rho D g) z r (2 * r))⁻¹ ^ q ∂(normLGFLaw d)) =
        ENNReal.ofReal (r ^ (β * q)) *
          (∫⁻ g, (acrossDist (rho D g) z r (2 * r))⁻¹ ^ q ∂(normLGFLaw d)) :=
      lintegral_const_mul _ hmeas
    _ ≤ ENNReal.ofReal (r ^ (β * q)) *
        ENNReal.ofReal (C * r ^ (-a) * (R + 3) ^ f) := by
      gcongr
    _ ≤ ENNReal.ofReal (C * (R + 3) ^ f * r ^ ((d : ℝ) + 1)) := by
      rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hr.le _)]
      apply ENNReal.ofReal_le_ofReal
      have hCR : 0 ≤ C * (R + 3) ^ f := by positivity
      calc
        r ^ (β * q) * (C * r ^ (-a) * (R + 3) ^ f) =
            (C * (R + 3) ^ f) * (r ^ (β * q) * r ^ (-a)) := by ring
        _ ≤ (C * (R + 3) ^ f) * r ^ ((d : ℝ) + 1) :=
          mul_le_mul_of_nonneg_left hpow hCR

end HigherDimLQGContinuity
