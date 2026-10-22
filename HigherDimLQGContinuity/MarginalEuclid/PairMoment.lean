import HigherDimLQGContinuity.MarginalEuclid.ExpMoment
import HigherDimLQGContinuity.MarginalEuclid.GaussianFactor
import GaussianLQG.LQG.Scaling

/-!
# Pairwise moments of the normalized metric

The exact scaling identity, Cauchy–Schwarz, the Gaussian moment generating
function, and the log-unit exponential moment give a power bound at a pair.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd e₁)

private theorem n5_pair_scalar (r R ξ q φ Z : ℝ) (hr : 0 < r) (hR : 0 < R) (hq : 0 ≤ q) :
    (r ^ φ * Real.exp (ξ * Z) * R) ^ q ≤
      r ^ (q * φ) * Real.exp (q * ξ * Z) * Real.exp (q * |Real.log R|) := by
  have hpow : (r ^ φ * Real.exp (ξ * Z) * R) ^ q =
      r ^ (q * φ) * Real.exp (q * ξ * Z) * Real.exp (q * Real.log R) := by
    rw [Real.mul_rpow (mul_nonneg (Real.rpow_pos_of_pos hr _).le (Real.exp_pos _).le)
      hR.le, Real.mul_rpow (Real.rpow_pos_of_pos hr _).le (Real.exp_pos _).le,
      ← Real.rpow_mul hr.le]
    rw [Real.rpow_def_of_pos hR]
    rw [← Real.exp_mul]
    congr 1 <;> ring_nf
  rw [hpow]
  have hh : q * Real.log R ≤ q * |Real.log R| :=
    mul_le_mul_of_nonneg_left (le_abs_self _) hq
  exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hh)
    (mul_nonneg (Real.rpow_pos_of_pos hr _).le (Real.exp_pos _).le)

/-- Exponential moments transport through recentring at the unit pin. -/
theorem n5_lintegral_recentre_logRho_exp {d : ℕ} (hd : 3 ≤ d)
    {D : DistRd d → ContMetric d} (hD : Measurable D)
    {r : ℝ} (hr : 0 < r) (x u : Rd d) (lam : ℝ) :
    (∫⁻ g, ENNReal.ofReal
      (Real.exp (lam * |Real.log ((rho D (recentre 1 r x g)).1 (0, u))|)) ∂(normLGFLaw d)) =
    ∫⁻ g, ENNReal.ofReal
      (Real.exp (lam * |Real.log ((rho D g).1 (0, u))|)) ∂(normLGFLaw d) := by
  let F : DistRd d → ℝ≥0∞ := fun g => ENNReal.ofReal
    (Real.exp (lam * |Real.log ((rho D g).1 (0, u))|))
  have hF : Measurable F := by
    exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_const.mul (continuous_abs.measurable.comp
        (measurable_log_rho_apply hD _))))
  rw [← pinLaw_one (by omega : 2 ≤ d)]
  rw [← lintegral_map hF (measurable_recentre 1 r x)]
  rw [recentre_law (by omega : 2 ≤ d) one_pos one_pos hr x]

/-- A raw pair-moment bound before inserting the variance estimate. -/
theorem n5_lintegral_rho_pow_raw {d : ℕ} (hd : 3 ≤ d)
    {ξ : ℝ} (hξ : 0 < ξ) {D : DistRd d → ContMetric d}
    (hD : IsStrongExpMetric d ξ (distExp d ξ) D)
    {r : ℝ} (hr : 0 < r) (x u : Rd d) (hu : ‖u‖ = 1)
    {q : ℝ} (hq : 0 < q)
    (hF : ∫⁻ g, ENNReal.ofReal
      (Real.exp (2 * q * |Real.log ((rho D (recentre 1 r x g)).1 (0, u))|))
        ∂(normLGFLaw d) ≤ 2) :
    ∫⁻ g, ENNReal.ofReal ((rho D g).1 (x, x + r • u) ^ q) ∂(normLGFLaw d) ≤
      ENNReal.ofReal (r ^ (q * phiXi d ξ)) *
        ENNReal.ofReal (Real.exp
          (Var[fun g : DistRd d => sphereAvg g r x; normLGFLaw d] * (q * ξ) ^ 2)) *
        ENNReal.ofReal (Real.sqrt 2) := by
  let Z : DistRd d → ℝ := fun g => sphereAvg g r x
  let Y : DistRd d → ℝ := fun g =>
    Real.log ((rho D (recentre 1 r x g)).1 (0, u))
  have hZ : Measurable Z := measurable_sphereAvg_left r x
  have hY : Measurable Y :=
    (measurable_log_rho_apply hD.measurable _).comp (measurable_recentre 1 r x)
  have hRpos (g : DistRd d) : 0 < (rho D (recentre 1 r x g)).1 (0, u) := by
    apply (rho D (recentre 1 r x g)).apply_pos
    intro he
    have : u = 0 := he.symm
    simp [this] at hu
  have hpoint : ∀ᵐ g ∂(normLGFLaw d),
      ENNReal.ofReal ((rho D g).1 (x, x + r • u) ^ q) ≤
        ENNReal.ofReal (r ^ (q * phiXi d ξ)) *
          (ENNReal.ofReal (Real.exp (q * ξ * Z g)) *
            ENNReal.ofReal (Real.exp (q * |Y g|))) := by
    filter_upwards [rho_pair_repr hd hξ hD hr x u] with g hg
    rw [hg]
    have hreal := n5_pair_scalar r ((rho D (recentre 1 r x g)).1 (0, u)) ξ q
      (phiXi d ξ) (Z g) hr (hRpos g) hq.le
    apply (ENNReal.ofReal_le_ofReal hreal).trans_eq
    change ENNReal.ofReal
      (r ^ (q * phiXi d ξ) * Real.exp (q * ξ * Z g) * Real.exp (q * |Y g|)) = _
    rw [show r ^ (q * phiXi d ξ) * Real.exp (q * ξ * Z g) *
        Real.exp (q * |Y g|) = r ^ (q * phiXi d ξ) *
          (Real.exp (q * ξ * Z g) * Real.exp (q * |Y g|)) by ring]
    rw [ENNReal.ofReal_mul (Real.rpow_pos_of_pos hr _).le,
      ENNReal.ofReal_mul (Real.exp_pos _).le]
  have hgauss : (∫⁻ g, ENNReal.ofReal (Real.exp (q * ξ * Z g)) ^ (2 : ℝ)
      ∂(normLGFLaw d)) =
      ENNReal.ofReal (Real.exp
        (Var[Z; normLGFLaw d] * (2 * q * ξ) ^ 2 / 2)) := by
    have hh := lintegral_exp_mul_pair_sphereAvg hd hr x (2 * q * ξ)
    calc
      (∫⁻ g, ENNReal.ofReal (Real.exp (q * ξ * Z g)) ^ (2 : ℝ)
          ∂(normLGFLaw d)) =
          ∫⁻ g, ENNReal.ofReal (Real.exp (2 * q * ξ * Z g)) ∂(normLGFLaw d) := by
        apply lintegral_congr
        intro g
        rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _)]
        congr 1
        calc
          Real.exp (q * ξ * Z g) ^ (2 : ℝ) = Real.exp (2 * (q * ξ * Z g)) := by
            rw [Real.rpow_two]
            exact (Real.exp_nat_mul (q * ξ * Z g) 2).symm
          _ = Real.exp (2 * q * ξ * Z g) := by congr 1; ring
      _ = _ := hh
  have hCS := GaussianLQG.lintegral_mul_le_sqrt_mul_sqrt (normLGFLaw d)
    (f := fun g => ENNReal.ofReal (Real.exp (q * ξ * Z g)))
    (g := fun g => ENNReal.ofReal (Real.exp (q * |Y g|)))
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_const.mul hZ))).aemeasurable
    (ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp
      (measurable_const.mul (continuous_abs.measurable.comp hY)))).aemeasurable
  have hF2 : (∫⁻ g, ENNReal.ofReal (Real.exp (q * |Y g|)) ^ (2 : ℝ)
      ∂(normLGFLaw d)) ≤ 2 := by
    calc
      (∫⁻ g, ENNReal.ofReal (Real.exp (q * |Y g|)) ^ (2 : ℝ)
          ∂(normLGFLaw d)) =
          ∫⁻ g, ENNReal.ofReal (Real.exp (2 * q * |Y g|)) ∂(normLGFLaw d) := by
        apply lintegral_congr
        intro g
        rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _)]
        congr 1
        calc
          Real.exp (q * |Y g|) ^ (2 : ℝ) = Real.exp (2 * (q * |Y g|)) := by
            rw [Real.rpow_two]
            exact (Real.exp_nat_mul (q * |Y g|) 2).symm
          _ = Real.exp (2 * q * |Y g|) := by congr 1; ring
      _ ≤ 2 := hF
  have hgauss_sqrt :
      (ENNReal.ofReal (Real.exp (Var[Z; normLGFLaw d] * (2 * q * ξ) ^ 2 / 2))) ^
        (1 / 2 : ℝ) =
        ENNReal.ofReal (Real.exp (Var[Z; normLGFLaw d] * (q * ξ) ^ 2)) := by
    rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _)]
    rw [← Real.exp_mul]
    congr 1
    ring_nf
  calc
    ∫⁻ g, ENNReal.ofReal ((rho D g).1 (x, x + r • u) ^ q) ∂(normLGFLaw d)
      ≤ ∫⁻ g, ENNReal.ofReal (r ^ (q * phiXi d ξ)) *
          (ENNReal.ofReal (Real.exp (q * ξ * Z g)) *
            ENNReal.ofReal (Real.exp (q * |Y g|))) ∂(normLGFLaw d) :=
        lintegral_mono_ae hpoint
    _ = ENNReal.ofReal (r ^ (q * phiXi d ξ)) *
          ∫⁻ g, ENNReal.ofReal (Real.exp (q * ξ * Z g)) *
            ENNReal.ofReal (Real.exp (q * |Y g|)) ∂(normLGFLaw d) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal (r ^ (q * phiXi d ξ)) *
          ((∫⁻ g, ENNReal.ofReal (Real.exp (q * ξ * Z g)) ^ (2 : ℝ)
              ∂(normLGFLaw d)) ^ (1 / 2 : ℝ) *
            (∫⁻ g, ENNReal.ofReal (Real.exp (q * |Y g|)) ^ (2 : ℝ)
              ∂(normLGFLaw d)) ^ (1 / 2 : ℝ)) := by gcongr
    _ ≤ ENNReal.ofReal (r ^ (q * phiXi d ξ)) *
          (ENNReal.ofReal (Real.exp
            (Var[Z; normLGFLaw d] * (2 * q * ξ) ^ 2 / 2)) ^ (1 / 2 : ℝ) *
            (2 : ℝ≥0∞) ^ (1 / 2 : ℝ)) := by
        rw [hgauss]
        gcongr
    _ = ENNReal.ofReal (r ^ (q * phiXi d ξ)) *
          ENNReal.ofReal (Real.exp
            (Var[Z; normLGFLaw d] * (q * ξ) ^ 2)) *
          ENNReal.ofReal (Real.sqrt 2) := by
        rw [hgauss_sqrt]
        rw [show (2 : ℝ≥0∞) ^ (1 / 2 : ℝ) = ENNReal.ofReal (Real.sqrt 2) by
          rw [← show ENNReal.ofReal (2 : ℝ) = (2 : ℝ≥0∞) by norm_num]
          rw [ENNReal.ofReal_rpow_of_pos (by norm_num : (0 : ℝ) < 2), Real.sqrt_eq_rpow]]
        ring

/-- Insert the uniform log-unit exponential moment into the pair estimate. -/
theorem n5_lintegral_rho_pow_small {d : ℕ} (hd : 3 ≤ d)
    {ξ₂ C₃ : ℝ} (hExp : 0 < ξ₂ ∧ 1 ≤ C₃ ∧
      ∀ ξ ∈ Ioc (0 : ℝ) ξ₂, Real.sqrt (2 * d) < distExp d ξ →
        ∀ D : DistRd d → ContMetric d, IsStrongExpMetric d ξ (distExp d ξ) D →
          ∀ u : Rd d, ‖u‖ = 1 → ∀ lam : ℝ, 0 ≤ lam →
            lam ≤ (2 * Real.exp 1 * C₃ * ξ)⁻¹ →
              ∫⁻ g, ENNReal.ofReal
                (Real.exp (lam * |Real.log ((rho D g).1 (0, u))|)) ∂(normLGFLaw d) ≤ 2)
    {ξ : ℝ} (hξ : ξ ∈ Ioc (0 : ℝ) ξ₂)
    (hgap : Real.sqrt (2 * d) < distExp d ξ)
    {D : DistRd d → ContMetric d}
    (hD : IsStrongExpMetric d ξ (distExp d ξ) D)
    {r : ℝ} (hr : 0 < r) (x u : Rd d) (hu : ‖u‖ = 1)
    {q : ℝ} (hq : 0 < q)
    (hsmall : 4 * Real.exp 1 * C₃ * q * ξ ≤ 1) :
    ∫⁻ g, ENNReal.ofReal ((rho D g).1 (x, x + r • u) ^ q) ∂(normLGFLaw d) ≤
      ENNReal.ofReal (r ^ (q * phiXi d ξ)) *
        ENNReal.ofReal (Real.exp
          (Var[fun g : DistRd d => sphereAvg g r x; normLGFLaw d] * (q * ξ) ^ 2)) *
        ENNReal.ofReal (Real.sqrt 2) := by
  have hden : 0 < 2 * Real.exp 1 * C₃ * ξ := by
    have := hξ.1
    have : 0 < C₃ := lt_of_lt_of_le zero_lt_one hExp.2.1
    positivity
  have hlam : 2 * q ≤ (2 * Real.exp 1 * C₃ * ξ)⁻¹ := by
    rw [inv_eq_one_div]
    apply (le_div_iff₀ hden).2
    nlinarith [Real.exp_pos 1]
  have hunit := hExp.2.2 ξ hξ hgap D hD u hu (2 * q) (by positivity) hlam
  have hF : ∫⁻ g, ENNReal.ofReal
      (Real.exp (2 * q * |Real.log ((rho D (recentre 1 r x g)).1 (0, u))|))
        ∂(normLGFLaw d) ≤ 2 := by
    rw [n5_lintegral_recentre_logRho_exp hd hD.measurable hr x u (2 * q)]
    exact hunit
  exact n5_lintegral_rho_pow_raw hd hξ.1 hD hr x u hu hq hF

end HigherDimLQGContinuity
