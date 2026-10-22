import HigherDimLQGContinuity.MarginalEuclid.PairMoment
import HigherDimLQGContinuity.Param.Interval

/-! Uniform pairwise moments on bounded sets. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

private theorem n5_max_zero_log_le {t R : ℝ} (ht : 0 ≤ t) (hR : 0 ≤ R)
    (h : t ≤ R) : max 0 (Real.log t) ≤ R := by
  exact max_le hR ((Real.log_le_self ht).trans h)

private theorem n5_variance_le_log_inv {d : ℕ}
    {R : ℝ} (hR : 0 ≤ R) {x : Rd d} (hx : ‖x‖ ≤ R)
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1)
    {K : ℝ} (hK : ∀ {r : ℝ}, 0 < r → ∀ x : Rd d,
      (r ≤ 1 → Var[fun g : DistRd d => sphereAvg g r x; normLGFLaw d] ≤
        Real.log (1 / r) + 2 * max 0 (Real.log ‖x‖) + K) ∧
      (1 ≤ r → Var[fun g : DistRd d => sphereAvg g r x; normLGFLaw d] ≤
        Real.log r + 2 * max 0 (Real.log (‖x‖ / r)) + K)) :
    Var[fun g : DistRd d => sphereAvg g r x; normLGFLaw d] ≤
      Real.log (1 / r) + (2 * R + K) := by
  have hlog := n5_max_zero_log_le (norm_nonneg x) hR hx
  have hh := (hK hr x).1 hr1
  linarith

private theorem n5_pair_power_bound {r ξ q φ α V W : ℝ}
    (hr : 0 < r) (hr1 : r ≤ 1) (hξ : 0 ≤ ξ) (hξ1 : ξ ≤ 1)
    (hq : 0 ≤ q) (hφ : 1 - W * ξ ≤ φ)
    (hsmall : W * ξ + q * ξ ^ 2 ≤ 1 - α)
    (hV : V ≤ W) (hW : 0 ≤ W) :
    r ^ (q * φ) * Real.exp ((Real.log (1 / r) + V) * (q * ξ) ^ 2) ≤
      Real.exp (W * q ^ 2) * r ^ (q * α) := by
  have hlog : 0 ≤ Real.log (1 / r) := Real.log_nonneg (by
    rw [one_le_div hr]; exact hr1)
  have hlogr : Real.log r ≤ 0 := Real.log_nonpos hr.le hr1
  have hbound : q * α ≤ q * φ - (q * ξ) ^ 2 := by
    have ha := mul_le_mul_of_nonneg_left hφ hq
    have hb := mul_le_mul_of_nonneg_left hsmall hq
    nlinarith
  have hVbound : V * (q * ξ) ^ 2 ≤ W * q ^ 2 := by
    have hh : V * (q * ξ) ^ 2 ≤ W * (q * ξ) ^ 2 :=
      mul_le_mul_of_nonneg_right hV (sq_nonneg _)
    have hqξ : q * ξ ≤ q := by nlinarith [mul_nonneg hq (sub_nonneg.mpr hξ1)]
    have hsq : (q * ξ) ^ 2 ≤ q ^ 2 :=
      (sq_le_sq₀ (mul_nonneg hq hξ) hq).2 hqξ
    exact hh.trans (mul_le_mul_of_nonneg_left hsq hW)
  rw [Real.rpow_def_of_pos hr, Real.rpow_def_of_pos hr]
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hlog_inv : Real.log (1 / r) = -Real.log r := by
    rw [one_div, Real.log_inv]
  rw [hlog_inv]
  have hmul : (q * φ - (q * ξ) ^ 2) * Real.log r ≤ q * α * Real.log r :=
    mul_le_mul_of_nonpos_right hbound hlogr
  nlinarith

/-- The small-scale part of the uniform pair-moment bound. -/
theorem n5_pair_moment_le_small_scale {d : ℕ} (hd : 3 ≤ d)
    (hφ : PhiRate d)
    {R q β ξ : ℝ} (hR : 1 ≤ R) (hq : 1 ≤ q)
    {D : DistRd d → ContMetric d} (hD : IsStrongExpMetric d ξ (distExp d ξ) D)
    {ξ₂ C₃ : ℝ} (hExp : 0 < ξ₂ ∧ 1 ≤ C₃ ∧
      ∀ ξ ∈ Ioc (0 : ℝ) ξ₂, Real.sqrt (2 * d) < distExp d ξ →
        ∀ D : DistRd d → ContMetric d, IsStrongExpMetric d ξ (distExp d ξ) D →
          ∀ u : Rd d, ‖u‖ = 1 → ∀ lam : ℝ, 0 ≤ lam →
            lam ≤ (2 * Real.exp 1 * C₃ * ξ)⁻¹ →
              ∫⁻ g, ENNReal.ofReal
                (Real.exp (lam * |Real.log ((rho D g).1 (0, u))|)) ∂(normLGFLaw d) ≤ 2)
    (hξ : ξ ∈ Ioc (0 : ℝ) ξ₂) (hgap : Real.sqrt (2 * d) < distExp d ξ)
    (hξ1 : ξ ≤ 1) (hξφ : ξ ≤ hφ.choose)
    (hsmallExp : 4 * Real.exp 1 * C₃ * q * ξ ≤ 1)
    {K : ℝ} (hK : ∀ {r : ℝ}, 0 < r → ∀ x : Rd d,
      (r ≤ 1 → Var[fun g : DistRd d => sphereAvg g r x; normLGFLaw d] ≤
        Real.log (1 / r) + 2 * max 0 (Real.log ‖x‖) + K) ∧
      (1 ≤ r → Var[fun g : DistRd d => sphereAvg g r x; normLGFLaw d] ≤
        Real.log r + 2 * max 0 (Real.log (‖x‖ / r)) + K))
    {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) (x u : Rd d)
    (hx : ‖x‖ ≤ R) (hu : ‖u‖ = 1)
    (hsmall : (max (Real.sqrt (2 * d)) (max 0 (2 * R + K))) * ξ + q * ξ ^ 2 ≤
      (1 - β) / 4) :
    ∫⁻ g, ENNReal.ofReal ((rho D g).1 (x, x + r • u) ^ q) ∂(normLGFLaw d) ≤
      ENNReal.ofReal
        (Real.sqrt 2 * Real.exp ((max (Real.sqrt (2 * d)) (max 0 (2 * R + K))) * q ^ 2) *
          r ^ (q * (1 - (1 - β) / 4))) := by
  let W := max (Real.sqrt (2 * d)) (max 0 (2 * R + K))
  have hW : 0 ≤ W := le_trans (le_max_left 0 (2 * R + K)) (le_max_right _ _)
  have hV : 2 * R + K ≤ W :=
    le_trans (le_max_right 0 (2 * R + K)) (le_max_right _ _)
  have hphi : 1 - W * ξ ≤ phiXi d ξ := by
    have hh := hφ.choose_spec.2 ξ ⟨hξ.1, hξφ⟩
    rw [← phiXi_of_pos hξ.1] at hh
    have hh' := (abs_le.mp hh).1
    have hW' : Real.sqrt (2 * d) ≤ W := le_max_left _ _
    nlinarith [mul_nonneg (sub_nonneg.mpr hW') hξ.1.le]
  have hsmall' : W * ξ + q * ξ ^ 2 ≤
      1 - (1 - (1 - β) / 4) := by
    dsimp [W] at *
    linarith
  have hvar := n5_variance_le_log_inv (zero_le_one.trans hR) hx hr hr1 hK
  have hreal : r ^ (q * phiXi d ξ) *
      Real.exp (Var[fun g : DistRd d => sphereAvg g r x; normLGFLaw d] *
        (q * ξ) ^ 2) * Real.sqrt 2 ≤
      Real.sqrt 2 * Real.exp (W * q ^ 2) *
        r ^ (q * (1 - (1 - β) / 4)) := by
    have hpow := n5_pair_power_bound hr hr1 hξ.1.le hξ1 (zero_le_one.trans hq) hphi
      hsmall' hV hW
    have hvarmul := mul_le_mul_of_nonneg_right hvar (sq_nonneg (q * ξ))
    have hexp := Real.exp_le_exp.mpr hvarmul
    have hpowpos : 0 ≤ r ^ (q * phiXi d ξ) := (Real.rpow_pos_of_pos hr _).le
    have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    nlinarith [mul_nonneg hpowpos (sub_nonneg.mpr hexp),
      mul_nonneg hsqrt (sub_nonneg.mpr hpow)]
  have hraw := n5_lintegral_rho_pow_small hd hExp hξ hgap hD hr x u hu
    (zero_lt_one.trans_le hq) hsmallExp
  calc
    _ ≤ ENNReal.ofReal (r ^ (q * phiXi d ξ)) *
        ENNReal.ofReal (Real.exp
          (Var[fun g : DistRd d => sphereAvg g r x; normLGFLaw d] * (q * ξ) ^ 2)) *
        ENNReal.ofReal (Real.sqrt 2) := hraw
    _ = ENNReal.ofReal (r ^ (q * phiXi d ξ) *
        Real.exp (Var[fun g : DistRd d => sphereAvg g r x; normLGFLaw d] *
          (q * ξ) ^ 2) * Real.sqrt 2) := by
      rw [ENNReal.ofReal_mul
        (mul_nonneg (Real.rpow_pos_of_pos hr _).le (Real.exp_pos _).le),
        ENNReal.ofReal_mul (Real.rpow_pos_of_pos hr _).le]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

private theorem n5_variance_le_large {d : ℕ}
    {R L : ℝ} (hR : 0 ≤ R)
    {x : Rd d} (hx : ‖x‖ ≤ R) {r : ℝ} (hr : 1 ≤ r) (hrL : r ≤ L)
    {K : ℝ} (hK : ∀ {r : ℝ}, 0 < r → ∀ x : Rd d,
      (r ≤ 1 → Var[fun g : DistRd d => sphereAvg g r x; normLGFLaw d] ≤
        Real.log (1 / r) + 2 * max 0 (Real.log ‖x‖) + K) ∧
      (1 ≤ r → Var[fun g : DistRd d => sphereAvg g r x; normLGFLaw d] ≤
        Real.log r + 2 * max 0 (Real.log (‖x‖ / r)) + K)) :
    Var[fun g : DistRd d => sphereAvg g r x; normLGFLaw d] ≤ L + 2 * R + K := by
  have hrpos : 0 < r := lt_of_lt_of_le zero_lt_one hr
  have hdiv : ‖x‖ / r ≤ R := by
    apply (div_le_iff₀ hrpos).2
    nlinarith [mul_nonneg hR (sub_nonneg.mpr hr)]
  have hlog : max 0 (Real.log (‖x‖ / r)) ≤ R :=
    n5_max_zero_log_le (div_nonneg (norm_nonneg x) hrpos.le) hR hdiv
  have hlogr : Real.log r ≤ L := (Real.log_le_self hrpos.le).trans hrL
  have hh := (hK hrpos x).2 hr
  linarith

private theorem n5_pair_power_bound_large {r ξ q φ L W B : ℝ}
    (hr : 1 ≤ r) (hrL : r ≤ L) (hL : 1 ≤ L)
    (hξ : 0 ≤ ξ) (hξ1 : ξ ≤ 1) (hq : 0 ≤ q)
    (hφ : φ ≤ 1 + W * ξ) (hW : 0 ≤ W)
    (hB : B ≤ W) :
    r ^ (q * φ) * Real.exp (B * (q * ξ) ^ 2) ≤
      L ^ (q * (1 + W)) * Real.exp (W * q ^ 2) := by
  have hphi' : q * φ ≤ q * (1 + W) := by
    have hξW : W * ξ ≤ W := by
      nlinarith [mul_nonneg hW (sub_nonneg.mpr hξ1)]
    nlinarith [mul_nonneg hq (sub_nonneg.mpr hφ)]
  have hexp : B * (q * ξ) ^ 2 ≤ W * q ^ 2 := by
    have hqξ : q * ξ ≤ q := by nlinarith [mul_nonneg hq (sub_nonneg.mpr hξ1)]
    have hsq : (q * ξ) ^ 2 ≤ q ^ 2 :=
      (sq_le_sq₀ (mul_nonneg hq hξ) hq).2 hqξ
    exact (mul_le_mul_of_nonneg_right hB (sq_nonneg _)).trans
      (mul_le_mul_of_nonneg_left hsq hW)
  have hrpow : r ^ (q * φ) ≤ L ^ (q * (1 + W)) := by
    calc
      r ^ (q * φ) ≤ r ^ (q * (1 + W)) :=
        Real.rpow_le_rpow_of_exponent_le hr hphi'
      _ ≤ L ^ (q * (1 + W)) := by
        apply Real.rpow_le_rpow (zero_le_one.trans hr) hrL
        nlinarith
  exact mul_le_mul hrpow (Real.exp_le_exp.mpr hexp) (Real.exp_pos _).le
    (Real.rpow_pos_of_pos (lt_of_lt_of_le zero_lt_one hL) _).le

private theorem n5_pair_moment_le_large_scale {d : ℕ}
    (hφ : PhiRate d) {R L q ξ : ℝ} (hR : 1 ≤ R) (hL : 1 ≤ L) (hq : 1 ≤ q)
    (hξ : 0 < ξ) (hξ1 : ξ ≤ 1) (hξφ : ξ ≤ hφ.choose)
    {D : DistRd d → ContMetric d}
    {K : ℝ} (hK : ∀ {r : ℝ}, 0 < r → ∀ x : Rd d,
      (r ≤ 1 → Var[fun g : DistRd d => sphereAvg g r x; normLGFLaw d] ≤
        Real.log (1 / r) + 2 * max 0 (Real.log ‖x‖) + K) ∧
      (1 ≤ r → Var[fun g : DistRd d => sphereAvg g r x; normLGFLaw d] ≤
        Real.log r + 2 * max 0 (Real.log (‖x‖ / r)) + K))
    {r : ℝ} (hr : 1 ≤ r) (hrL : r ≤ L) (x u : Rd d)
    (hx : ‖x‖ ≤ R)
    (hraw : ∫⁻ g, ENNReal.ofReal ((rho D g).1 (x, x + r • u) ^ q) ∂(normLGFLaw d) ≤
      ENNReal.ofReal (r ^ (q * phiXi d ξ)) *
        ENNReal.ofReal (Real.exp
          (Var[fun g : DistRd d => sphereAvg g r x; normLGFLaw d] * (q * ξ) ^ 2)) *
        ENNReal.ofReal (Real.sqrt 2)) :
    ∫⁻ g, ENNReal.ofReal ((rho D g).1 (x, x + r • u) ^ q) ∂(normLGFLaw d) ≤
      ENNReal.ofReal (Real.sqrt 2 *
        L ^ (q * (1 + max (Real.sqrt (2 * d)) (max 0 (L + 2 * R + K)))) *
        Real.exp ((max (Real.sqrt (2 * d)) (max 0 (L + 2 * R + K))) * q ^ 2)) := by
  let W := max (Real.sqrt (2 * d)) (max 0 (L + 2 * R + K))
  have hW : 0 ≤ W := le_trans (le_max_left 0 (L + 2 * R + K))
    (le_max_right _ _)
  have hV : L + 2 * R + K ≤ W :=
    le_trans (le_max_right 0 (L + 2 * R + K)) (le_max_right _ _)
  have hphi : phiXi d ξ ≤ 1 + W * ξ := by
    have hh := hφ.choose_spec.2 ξ ⟨hξ, hξφ⟩
    rw [← phiXi_of_pos hξ] at hh
    have hh' := (abs_le.mp hh).2
    have hW' : Real.sqrt (2 * d) ≤ W := le_max_left _ _
    nlinarith [mul_nonneg (sub_nonneg.mpr hW') hξ.le]
  have hvar := n5_variance_le_large (zero_le_one.trans hR) hx hr hrL hK
  have hpow := n5_pair_power_bound_large hr hrL hL hξ.le hξ1
    (zero_le_one.trans hq) hphi hW hV
  have hreal : r ^ (q * phiXi d ξ) *
      Real.exp (Var[fun g : DistRd d => sphereAvg g r x; normLGFLaw d] *
        (q * ξ) ^ 2) * Real.sqrt 2 ≤
      Real.sqrt 2 * L ^ (q * (1 + W)) * Real.exp (W * q ^ 2) := by
    have hvarmul := mul_le_mul_of_nonneg_right hvar (sq_nonneg (q * ξ))
    have hexp := Real.exp_le_exp.mpr hvarmul
    have hpowpos : 0 ≤ r ^ (q * phiXi d ξ) := (Real.rpow_pos_of_pos (zero_lt_one.trans_le hr) _).le
    have hsqrt : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
    nlinarith [mul_nonneg hpowpos (sub_nonneg.mpr hexp),
      mul_nonneg hsqrt (sub_nonneg.mpr hpow)]
  calc
    _ ≤ ENNReal.ofReal (r ^ (q * phiXi d ξ)) *
        ENNReal.ofReal (Real.exp
          (Var[fun g : DistRd d => sphereAvg g r x; normLGFLaw d] * (q * ξ) ^ 2)) *
        ENNReal.ofReal (Real.sqrt 2) := hraw
    _ = ENNReal.ofReal (r ^ (q * phiXi d ξ) *
        Real.exp (Var[fun g : DistRd d => sphereAvg g r x; normLGFLaw d] *
          (q * ξ) ^ 2) * Real.sqrt 2) := by
      rw [ENNReal.ofReal_mul
        (mul_nonneg (Real.rpow_pos_of_pos (zero_lt_one.trans_le hr) _).le
          (Real.exp_pos _).le),
        ENNReal.ofReal_mul (Real.rpow_pos_of_pos (zero_lt_one.trans_le hr) _).le]
    _ ≤ _ := ENNReal.ofReal_le_ofReal hreal

private theorem n5_pair_moment_le_scales {d : ℕ} (hd : 3 ≤ d)
    (hφ : PhiRate d)
    {R L q β ξ : ℝ} (hR : 1 ≤ R) (hL : 1 ≤ L) (hq : 1 ≤ q)
    (hβ : 0 < β) (hβ1 : β < 1)
    {D : DistRd d → ContMetric d} (hD : IsStrongExpMetric d ξ (distExp d ξ) D)
    {ξ₂ C₃ : ℝ} (hExp : 0 < ξ₂ ∧ 1 ≤ C₃ ∧
      ∀ ξ ∈ Ioc (0 : ℝ) ξ₂, Real.sqrt (2 * d) < distExp d ξ →
        ∀ D : DistRd d → ContMetric d, IsStrongExpMetric d ξ (distExp d ξ) D →
          ∀ u : Rd d, ‖u‖ = 1 → ∀ lam : ℝ, 0 ≤ lam →
            lam ≤ (2 * Real.exp 1 * C₃ * ξ)⁻¹ →
              ∫⁻ g, ENNReal.ofReal
                (Real.exp (lam * |Real.log ((rho D g).1 (0, u))|)) ∂(normLGFLaw d) ≤ 2)
    (hξ : ξ ∈ Ioc (0 : ℝ) ξ₂) (hgap : Real.sqrt (2 * d) < distExp d ξ)
    (hξ1 : ξ ≤ 1) (hξφ : ξ ≤ hφ.choose)
    (hsmallExp : 4 * Real.exp 1 * C₃ * q * ξ ≤ 1)
    {K : ℝ} (hK : ∀ {r : ℝ}, 0 < r → ∀ x : Rd d,
      (r ≤ 1 → Var[fun g : DistRd d => sphereAvg g r x; normLGFLaw d] ≤
        Real.log (1 / r) + 2 * max 0 (Real.log ‖x‖) + K) ∧
      (1 ≤ r → Var[fun g : DistRd d => sphereAvg g r x; normLGFLaw d] ≤
        Real.log r + 2 * max 0 (Real.log (‖x‖ / r)) + K))
    (hsmall : (max (Real.sqrt (2 * d)) (max 0 (2 * R + K))) * ξ + q * ξ ^ 2 ≤
      (1 - β) / 4)
    {r : ℝ} (hr : 0 < r) (hrL : r ≤ L) (x u : Rd d)
    (hx : ‖x‖ ≤ R) (hu : ‖u‖ = 1) :
    ∫⁻ g, ENNReal.ofReal ((rho D g).1 (x, x + r • u) ^ q) ∂(normLGFLaw d) ≤
      ENNReal.ofReal
        ((Real.sqrt 2 * Real.exp ((max (Real.sqrt (2 * d)) (max 0 (2 * R + K))) * q ^ 2) +
            Real.sqrt 2 * L ^ (q * (1 + max (Real.sqrt (2 * d)) (max 0 (L + 2 * R + K)))) *
              Real.exp ((max (Real.sqrt (2 * d)) (max 0 (L + 2 * R + K))) * q ^ 2)) *
          r ^ (q * (1 - (1 - β) / 4))) := by
  let A := Real.sqrt 2 * Real.exp
    ((max (Real.sqrt (2 * d)) (max 0 (2 * R + K))) * q ^ 2)
  let B := Real.sqrt 2 * L ^
    (q * (1 + max (Real.sqrt (2 * d)) (max 0 (L + 2 * R + K)))) *
    Real.exp ((max (Real.sqrt (2 * d)) (max 0 (L + 2 * R + K))) * q ^ 2)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by
    dsimp [B]
    have : 0 < L := zero_lt_one.trans_le hL
    positivity
  have hrpow : 0 ≤ r ^ (q * (1 - (1 - β) / 4)) :=
    (Real.rpow_pos_of_pos hr _).le
  by_cases hr1 : r ≤ 1
  · have h := n5_pair_moment_le_small_scale hd hφ hR hq hD hExp hξ hgap
      hξ1 hξφ hsmallExp hK hr hr1 x u hx hu hsmall
    change _ ≤ ENNReal.ofReal ((A + B) * r ^ (q * (1 - (1 - β) / 4)))
    apply h.trans
    apply ENNReal.ofReal_le_ofReal
    dsimp [A]
    nlinarith [mul_nonneg hB hrpow]
  · have hr1' : 1 ≤ r := le_of_not_ge hr1
    have hraw := n5_lintegral_rho_pow_small hd hExp hξ hgap hD hr x u hu
      (zero_lt_one.trans_le hq) hsmallExp
    have h := n5_pair_moment_le_large_scale hφ hR hL hq hξ.1 hξ1 hξφ hK
      hr1' hrL x u hx hraw
    change _ ≤ ENNReal.ofReal ((A + B) * r ^ (q * (1 - (1 - β) / 4)))
    apply h.trans
    apply ENNReal.ofReal_le_ofReal
    have hα : 0 ≤ q * (1 - (1 - β) / 4) := by
      have : 0 ≤ q := zero_le_one.trans hq
      nlinarith
    have hpow1 := Real.one_le_rpow hr1' hα
    dsimp [B]
    nlinarith [mul_nonneg hA hrpow, mul_nonneg hB (sub_nonneg.mpr hpow1)]

/-- Pairwise `q`-moments on a fixed Euclidean ball, with a parameter window uniform
over all strong assignments. -/
theorem lintegral_rho_rpow_le_pair_radius {d : ℕ} (hd : 3 ≤ d)
    (hφ : PhiRate d) (hRot : StrongRotLaw d) (hC : ConcentrationStmt d)
    {R L β q : ℝ} (hR : 1 ≤ R) (hL : 1 ≤ L)
    (hβ : 0 < β) (hβ1 : β < 1) (hq : 1 ≤ q) :
    ∃ ξ₄ C₅ : ℝ, 0 < ξ₄ ∧ 0 ≤ C₅ ∧
      ∀ ξ ∈ Ioc (0 : ℝ) ξ₄,
        ∀ D : DistRd d → ContMetric d,
          IsStrongExpMetric d ξ (distExp d ξ) D →
            ∀ x y : Rd d, ‖x‖ ≤ R → dist x y ≤ L →
              ∫⁻ g, ENNReal.ofReal ((rho D g).1 (x, y) ^ q) ∂(normLGFLaw d) ≤
                ENNReal.ofReal (C₅ * (dist x y) ^ (q * (1 - (1 - β) / 4))) := by
  obtain ⟨ξ₂, C₃, hξ₂, hC₃, hExp⟩ := expMoment_logRho_le hd hC hRot
  obtain ⟨K, hK⟩ := exists_pair_sphereAvg_variance_le hd
  let W := max (Real.sqrt (2 * d)) (max 0 (2 * R + K))
  have hW : 0 ≤ W :=
    le_trans (le_max_left 0 (2 * R + K)) (le_max_right _ _)
  let δ := (1 - β) / 4
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let A := 4 * Real.exp 1 * C₃ * q
  have hA : 0 < A := by
    dsimp [A]
    have : 0 < C₃ := zero_lt_one.trans_le hC₃
    have : 0 < q := zero_lt_one.trans_le hq
    positivity
  let B := W + q + 1
  have hB : 0 < B := by dsimp [B]; linarith
  let ξ₄ := min ξ₂ (min (xiCrit d / 2)
    (min hφ.choose (min 1 (min (A + 1)⁻¹ (δ / B)))))
  have hξ₄ : 0 < ξ₄ := by
    dsimp [ξ₄]
    simp only [lt_min_iff]
    constructor
    · exact hξ₂
    constructor
    · have hc := xiCrit_pos (by omega : 2 ≤ d)
      positivity
    constructor
    · exact hφ.choose_spec.1
    constructor
    · norm_num
    constructor
    · positivity
    · positivity
  let C₅ :=
    Real.sqrt 2 * Real.exp (W * q ^ 2) +
      Real.sqrt 2 * L ^ (q * (1 + max (Real.sqrt (2 * d))
        (max 0 (L + 2 * R + K)))) *
        Real.exp ((max (Real.sqrt (2 * d)) (max 0 (L + 2 * R + K))) * q ^ 2)
  have hC₅ : 0 ≤ C₅ := by
    dsimp [C₅]
    have : 0 < L := zero_lt_one.trans_le hL
    positivity
  refine ⟨ξ₄, C₅, hξ₄, hC₅, ?_⟩
  intro ξ hξ D hD x y hx hxy
  have hξ0 : 0 < ξ := hξ.1
  have hξ₂' : ξ ≤ ξ₂ := hξ.2.trans (by dsimp [ξ₄]; exact min_le_left _ _)
  have hξc : ξ ≤ xiCrit d / 2 := by
    calc ξ ≤ ξ₄ := hξ.2
      _ ≤ xiCrit d / 2 := by dsimp [ξ₄]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hξφ : ξ ≤ hφ.choose := by
    calc ξ ≤ ξ₄ := hξ.2
      _ ≤ hφ.choose := by
        dsimp [ξ₄]
        exact le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _) (min_le_left _ _))
  have hξ1 : ξ ≤ 1 := by
    calc ξ ≤ ξ₄ := hξ.2
      _ ≤ 1 := by
        dsimp [ξ₄]
        exact le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _)
            (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hξA : ξ ≤ (A + 1)⁻¹ := by
    calc ξ ≤ ξ₄ := hξ.2
      _ ≤ (A + 1)⁻¹ := by
        dsimp [ξ₄]
        exact le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _)
            (le_trans (min_le_right _ _)
              (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hξB : ξ ≤ δ / B := by
    calc ξ ≤ ξ₄ := hξ.2
      _ ≤ δ / B := by
        dsimp [ξ₄]
        exact le_trans (min_le_right _ _)
          (le_trans (min_le_right _ _)
            (le_trans (min_le_right _ _)
              (le_trans (min_le_right _ _) (min_le_right _ _))))
  have hgap : Real.sqrt (2 * d) < distExp d ξ := by
    apply (sqrt_lt_distExp_iff (by omega : 2 ≤ d) hξ0).2
    have hc := xiCrit_pos (by omega : 2 ≤ d)
    linarith
  have hsmallExp : 4 * Real.exp 1 * C₃ * q * ξ ≤ 1 := by
    have hden : 0 < A + 1 := by linarith
    have hξA' : ξ ≤ 1 / (A + 1) := by simpa only [one_div] using hξA
    have hh := (le_div_iff₀ hden).1 hξA'
    dsimp [A] at *
    nlinarith
  have hsmall : W * ξ + q * ξ ^ 2 ≤ δ := by
    have hh := (le_div_iff₀ hB).1 hξB
    have hq0 : 0 ≤ q := zero_le_one.trans hq
    have hsq : ξ ^ 2 ≤ ξ := by nlinarith [mul_nonneg hξ0.le (sub_nonneg.mpr hξ1)]
    dsimp [B] at hh
    nlinarith [mul_nonneg hq0 (sub_nonneg.mpr hsq)]
  by_cases hxy0 : x = y
  · subst y
    simp only [dist_self, Real.zero_rpow (by nlinarith : (q * (1 - (1 - β) / 4)) ≠ 0),
      mul_zero, ENNReal.ofReal_zero]
    simp [ContMetric.apply_self, Real.zero_rpow (by nlinarith : q ≠ 0)]
  · let r := dist x y
    have hr : 0 < r := dist_pos.mpr hxy0
    let u : Rd d := r⁻¹ • (y - x)
    have hu : ‖u‖ = 1 := by
      dsimp [u]
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, ← dist_eq_norm]
      dsimp [r]
      rw [dist_comm y x]
      exact inv_mul_cancel₀ hr.ne'
    have hy : x + r • u = y := by
      dsimp [u]
      rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
      abel
    have hrL : r ≤ L := hxy
    have hh := n5_pair_moment_le_scales hd hφ hR hL hq hβ hβ1 hD
      ⟨hξ₂, hC₃, hExp⟩ ⟨hξ0, hξ₂'⟩ hgap hξ1 hξφ hsmallExp hK
      (by simpa only [W, δ] using hsmall) hr hrL x u hx hu
    simpa only [r, C₅, W, hy] using hh

/-- The grid-scale pair moment estimate (blueprint `c:lem-pair-moment`). -/
theorem lintegral_rho_rpow_le_pair {d : ℕ} (hd : 3 ≤ d)
    (hφ : PhiRate d) (hRot : StrongRotLaw d) (hC : ConcentrationStmt d)
    {R β q : ℝ} (hR : 1 ≤ R) (hβ : 0 < β) (hβ1 : β < 1) (hq : 1 ≤ q) :
    ∃ ξ₄ C₅ : ℝ, 0 < ξ₄ ∧ 0 ≤ C₅ ∧
      ∀ ξ ∈ Ioc (0 : ℝ) ξ₄,
        ∀ D : DistRd d → ContMetric d,
          IsStrongExpMetric d ξ (distExp d ξ) D →
            ∀ x y : Rd d, ‖x‖ ≤ R → dist x y ≤ Real.sqrt d →
              ∫⁻ g, ENNReal.ofReal ((rho D g).1 (x, y) ^ q) ∂(normLGFLaw d) ≤
                ENNReal.ofReal (C₅ * (dist x y) ^ (q * (1 - (1 - β) / 4))) := by
  have hL : (1 : ℝ) ≤ Real.sqrt d := by
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast (by omega : 1 ≤ d)
    have hd0 : (0 : ℝ) ≤ d := by positivity
    have hs := Real.sq_sqrt hd0
    have hs0 := Real.sqrt_nonneg (d : ℝ)
    nlinarith
  exact lintegral_rho_rpow_le_pair_radius hd hφ hRot hC hR hL hβ hβ1 hq

end HigherDimLQGContinuity
