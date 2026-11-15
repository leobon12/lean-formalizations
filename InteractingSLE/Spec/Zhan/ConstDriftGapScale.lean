/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.UpperPoint

/-!
# The upper-gap diffusion: powers of the scale function from `−∞`

Packet PROVE-ZHAN-A6. Astra, *Formalization proofs and dependency audit* (ruling R35), the scale calculation of
the upper-point diffusion (3.15) `dX = −√κ dB + (tanh(X/2) − σ) dt` (`ig1_formalization_proofs.txt`
L1170–L1219, used at L1441–L1450). With the scale density `w_σ` of `UpperPoint.lean` and `|σ| < 1`, the
scale function from `−∞`, `s(x) = ∫_{−∞}^x w_σ`, is positive and bounded, and for `0 < p ≤ 1` the power
`φ = s^p` is a nonnegative smooth function whose generator is nonpositive:

  `L φ = φ' (tanh(x/2) − σ) + (κ/2) φ'' = (κ/2) p (p − 1) s^{p−2} w_σ² ≤ 0`.

For `p (1 + σ) ≤ κ/4` its derivative dominates `sech(x/2)` on `x ≤ 0`:
`1/(1 + cosh x) ≤ C φ'(x)²`. The reflected function `x ↦ φ_{−σ}(−x)` does the same on `x ≥ 0`
(`ConstDriftGap.lean`).

## Main results

* `scaleLow`, `hasDerivAt_scaleLow`, `scaleLow_pos`, `scaleLow_le` (`s(x) ≤ (A/a) e^{ax}` on `x ≤ 0`);
* `scalePow`, `scalePowD`, `scalePowDD` (`φ`, `φ'`, `φ''`), `hasDerivAt_scalePow`, `hasDerivAt_scalePowD`,
  `contDiff_scalePow`;
* `scalePow_gen_nonpos` (**`L φ ≤ 0`**);
* `exists_inv_one_add_cosh_le_scalePowD` (**`1/(1 + cosh x) ≤ C φ'(x)²` on `x ≤ 0`**);
* `hasDerivAt_tanh`, `lipschitzWith_tanh_half`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory

namespace InteractingSLE

namespace Zhan

/-! ### `tanh` -/

theorem hasDerivAt_tanh (x : ℝ) : HasDerivAt Real.tanh (1 / Real.cosh x ^ 2) x := by
  have hc := (Real.cosh_pos x).ne'
  have h := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) hc
  have e : Real.sinh / Real.cosh = Real.tanh := by
    funext y; rw [Pi.div_apply, Real.tanh_eq_sinh_div_cosh]
  rw [e] at h
  refine h.congr_deriv ?_
  have := Real.cosh_sq_sub_sinh_sq x
  field_simp
  linarith

/-- `x ↦ tanh(x/2)` is `½`-Lipschitz. -/
theorem lipschitzWith_tanh_half : LipschitzWith (1 / 2 : NNReal) fun x : ℝ => Real.tanh (x / 2) := by
  have hd : ∀ x : ℝ, HasDerivAt (fun x : ℝ => Real.tanh (x / 2)) (1 / Real.cosh (x / 2) ^ 2 * (1 / 2)) x := by
    intro x
    have h2 : HasDerivAt (fun x : ℝ => x / 2) (1 / 2) x := by
      simpa using (hasDerivAt_id x).div_const 2
    exact (hasDerivAt_tanh (x / 2)).comp x h2
  refine lipschitzWith_of_nnnorm_deriv_le (fun x => (hd x).differentiableAt) fun x => ?_
  rw [(hd x).deriv, ← NNReal.coe_le_coe, coe_nnnorm, Real.norm_eq_abs]
  have hc : 1 ≤ Real.cosh (x / 2) ^ 2 := by nlinarith [Real.one_le_cosh (x / 2)]
  have h0 : 0 < 1 / Real.cosh (x / 2) ^ 2 := by positivity
  have h1 : 1 / Real.cosh (x / 2) ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; exact hc
  rw [abs_of_pos (by positivity)]
  push_cast
  linarith

/-! ### The scale function from `−∞` -/

variable {κ σ : ℝ}

theorem integrableOn_scaleDensity_Iic_of (hκ : 0 < κ) (hσ : -1 < σ) (x : ℝ) :
    IntegrableOn (scaleDensity κ σ) (Iic x) := by
  rcases le_total x 0 with hx | hx
  · exact (integrableOn_scaleDensity_Iic hκ hσ).mono_set (Iic_subset_Iic.2 hx)
  · have h2 : IntegrableOn (scaleDensity κ σ) (Icc 0 x) :=
      (continuous_scaleDensity κ σ).integrableOn_Icc
    refine ((integrableOn_scaleDensity_Iic hκ hσ).union h2).mono_set fun y hy => ?_
    by_cases h : y ≤ 0
    · exact Or.inl h
    · exact Or.inr ⟨le_of_lt (not_le.1 h), hy⟩

/-- The scale function from `−∞`, `s(x) = ∫_{−∞}^x w_σ`. -/
def scaleLow (κ σ x : ℝ) : ℝ := ∫ y in Iic x, scaleDensity κ σ y

theorem scaleLow_sub (hκ : 0 < κ) (hσ : -1 < σ) (a b : ℝ) :
    scaleLow κ σ b - scaleLow κ σ a = ∫ y in a..b, scaleDensity κ σ y :=
  intervalIntegral.integral_Iic_sub_Iic (integrableOn_scaleDensity_Iic_of hκ hσ a)
    (integrableOn_scaleDensity_Iic_of hκ hσ b)

theorem hasDerivAt_scaleLow (hκ : 0 < κ) (hσ : -1 < σ) (x : ℝ) :
    HasDerivAt (scaleLow κ σ) (scaleDensity κ σ x) x := by
  have h := ((continuous_scaleDensity κ σ).integral_hasStrictDerivAt 0 x).hasDerivAt
  have e : scaleLow κ σ = fun y => scaleLow κ σ 0 + ∫ t in (0 : ℝ)..y, scaleDensity κ σ t := by
    funext y; rw [← scaleLow_sub hκ hσ 0 y]; ring
  rw [e]
  exact h.const_add _

theorem scaleLow_pos (hκ : 0 < κ) (hσ : -1 < σ) (x : ℝ) : 0 < scaleLow κ σ x := by
  have h1 : 0 ≤ scaleLow κ σ (x - 1) :=
    setIntegral_nonneg measurableSet_Iic fun y _ => (scaleDensity_pos κ σ y).le
  have h2 : 0 < ∫ y in (x - 1)..x, scaleDensity κ σ y :=
    intervalIntegral.intervalIntegral_pos_of_pos_on
      ((continuous_scaleDensity κ σ).intervalIntegrable _ _) (fun y _ => scaleDensity_pos κ σ y)
      (by linarith)
  have := scaleLow_sub hκ hσ (x - 1) x
  linarith

/-- **The scale function at `−∞`**: `s(x) ≤ (A/a) e^{ax}` for `x ≤ 0`, `A = 2^{4/κ}`, `a = 2(1 + σ)/κ`. -/
theorem scaleLow_le (hκ : 0 < κ) (hσ : -1 < σ) {x : ℝ} (hx : x ≤ 0) :
    scaleLow κ σ x ≤
      Real.exp (4 / κ * Real.log 2) / (2 * (σ + 1) / κ) * Real.exp (2 * (σ + 1) / κ * x) := by
  set a := 2 * (σ + 1) / κ with ha_def
  have ha : 0 < a := by
    have : 0 < σ + 1 := by linarith
    positivity
  have hint : IntegrableOn (fun y => Real.exp (4 / κ * Real.log 2) * Real.exp (a * y)) (Iic x) :=
    (integrableOn_exp_mul_Iic ha x).const_mul _
  calc scaleLow κ σ x ≤ ∫ y in Iic x, Real.exp (4 / κ * Real.log 2) * Real.exp (a * y) := by
        refine setIntegral_mono_on (integrableOn_scaleDensity_Iic_of hκ hσ x) hint measurableSet_Iic
          fun y hy => ?_
        refine (scaleDensity_le hκ σ y).trans (le_of_eq ?_)
        rw [abs_of_nonpos ((mem_Iic.1 hy).trans hx), ha_def]
        congr 2
        ring
    _ = Real.exp (4 / κ * Real.log 2) / a * Real.exp (a * x) := by
        rw [integral_const_mul, integral_exp_mul_Iic ha]
        ring

theorem contDiff_scaleDensity (κ σ : ℝ) : ContDiff ℝ (⊤ : ℕ∞) (scaleDensity κ σ) := by
  unfold scaleDensity
  refine Real.contDiff_exp.comp (ContDiff.sub (by fun_prop) (contDiff_const.mul ?_))
  exact (Real.contDiff_cosh.comp (by fun_prop)).log fun x => (Real.cosh_pos _).ne'

theorem contDiff_scaleLow (hκ : 0 < κ) (hσ : -1 < σ) : ContDiff ℝ (⊤ : ℕ∞) (scaleLow κ σ) := by
  have hd : deriv (scaleLow κ σ) = scaleDensity κ σ := funext fun x => (hasDerivAt_scaleLow hκ hσ x).deriv
  refine contDiff_infty_iff_deriv.2 ⟨fun x => (hasDerivAt_scaleLow hκ hσ x).differentiableAt, ?_⟩
  rw [hd]
  exact contDiff_scaleDensity κ σ

/-! ### The power `φ = s^p` -/

/-- `φ = s^p`. -/
def scalePow (κ σ p x : ℝ) : ℝ := scaleLow κ σ x ^ p

/-- `φ' = p s^{p−1} w_σ`. -/
def scalePowD (κ σ p x : ℝ) : ℝ := p * scaleLow κ σ x ^ (p - 1) * scaleDensity κ σ x

/-- `φ'' = p (p − 1) s^{p−2} w_σ² + p s^{p−1} w_σ'`. -/
def scalePowDD (κ σ p x : ℝ) : ℝ :=
  p * (p - 1) * scaleLow κ σ x ^ (p - 2) * scaleDensity κ σ x ^ 2 +
    p * scaleLow κ σ x ^ (p - 1) * (scaleDensity κ σ x * (2 * σ / κ - 2 / κ * Real.tanh (x / 2)))

theorem scalePow_nonneg (κ σ p x : ℝ) (hκ : 0 < κ) (hσ : -1 < σ) : 0 ≤ scalePow κ σ p x :=
  (Real.rpow_pos_of_pos (scaleLow_pos hκ hσ x) p).le

theorem hasDerivAt_scalePow (hκ : 0 < κ) (hσ : -1 < σ) (p x : ℝ) :
    HasDerivAt (scalePow κ σ p) (scalePowD κ σ p x) x := by
  have h := (hasDerivAt_scaleLow hκ hσ x).rpow_const (p := p) (Or.inl (scaleLow_pos hκ hσ x).ne')
  refine h.congr_deriv ?_
  simp only [scalePowD]
  ring

theorem hasDerivAt_scalePowD (hκ : 0 < κ) (hσ : -1 < σ) (p x : ℝ) :
    HasDerivAt (scalePowD κ σ p) (scalePowDD κ σ p x) x := by
  have h1 := (hasDerivAt_scaleLow hκ hσ x).rpow_const (p := p - 1)
    (Or.inl (scaleLow_pos hκ hσ x).ne')
  have h2 := (h1.const_mul p).mul (hasDerivAt_scaleDensity κ σ x)
  refine h2.congr_deriv ?_
  simp only [scalePowDD]
  rw [show p - 1 - 1 = p - 2 by ring]
  ring

theorem contDiff_scalePow (hκ : 0 < κ) (hσ : -1 < σ) (p : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (scalePow κ σ p) :=
  (contDiff_scaleLow hκ hσ).rpow_const_of_ne fun x => (scaleLow_pos hκ hσ x).ne'

/-- `L φ = (κ/2) p (p − 1) s^{p−2} w_σ²` (the scale-function terms cancel by (3.16)). -/
theorem scalePow_gen_eq (hκ : 0 < κ) (p x : ℝ) :
    scalePowD κ σ p x * (Real.tanh (x / 2) - σ) + κ / 2 * scalePowDD κ σ p x =
      κ / 2 * (p * (p - 1)) * scaleLow κ σ x ^ (p - 2) * scaleDensity κ σ x ^ 2 := by
  simp only [scalePowD, scalePowDD]
  field_simp
  ring

/-- **`L φ ≤ 0`** for `0 ≤ p ≤ 1`. -/
theorem scalePow_gen_nonpos (hκ : 0 < κ) (hσ : -1 < σ) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : ℝ) :
    scalePowD κ σ p x * (Real.tanh (x / 2) - σ) + κ / 2 * scalePowDD κ σ p x ≤ 0 := by
  rw [scalePow_gen_eq hκ]
  have h1 : p * (p - 1) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hp0 (by linarith)
  have h2 : 0 ≤ scaleLow κ σ x ^ (p - 2) := (Real.rpow_pos_of_pos (scaleLow_pos hκ hσ x) _).le
  have h3 : 0 ≤ κ / 2 := by positivity
  have h4 := mul_nonpos_of_nonneg_of_nonpos h3 h1
  have h5 := mul_nonpos_of_nonpos_of_nonneg h4 h2
  exact mul_nonpos_of_nonpos_of_nonneg h5 (sq_nonneg _)

/-- **The derivative dominates `e^{x/2}` on `x ≤ 0`**: `φ'(x) ≥ p (A/a)^{p−1} e^{x/2}` when `p a ≤ 1/2`,
`A = 2^{4/κ}`, `a = 2(1 + σ)/κ`. -/
theorem le_scalePowD (hκ : 0 < κ) (hσ : -1 < σ) {p : ℝ} (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hpa : p * (2 * (σ + 1) / κ) ≤ 1 / 2) {x : ℝ} (hx : x ≤ 0) :
    p * (Real.exp (4 / κ * Real.log 2) / (2 * (σ + 1) / κ)) ^ (p - 1) * Real.exp (x / 2) ≤
      scalePowD κ σ p x := by
  set a := 2 * (σ + 1) / κ with ha_def
  set A := Real.exp (4 / κ * Real.log 2) with hA
  have ha : 0 < a := by
    have : 0 < σ + 1 := by linarith
    positivity
  have hA0 : 0 < A := Real.exp_pos _
  have hs := scaleLow_pos hκ hσ x
  have hM : scaleLow κ σ x ≤ A / a * Real.exp (a * x) := scaleLow_le hκ hσ hx
  have h1 : (A / a * Real.exp (a * x)) ^ (p - 1) ≤ scaleLow κ σ x ^ (p - 1) :=
    Real.rpow_le_rpow_of_nonpos hs hM (by linarith)
  have h2 : Real.exp (a * x) ≤ scaleDensity κ σ x := by
    refine le_trans (le_of_eq ?_) (le_scaleDensity hκ σ x)
    rw [abs_of_nonpos hx, ha_def]
    congr 1
    ring
  have e : (A / a * Real.exp (a * x)) ^ (p - 1) = (A / a) ^ (p - 1) * Real.exp (a * x * (p - 1)) := by
    rw [Real.mul_rpow (by positivity) (Real.exp_pos _).le, ← Real.exp_mul]
  have h3 : Real.exp (x / 2) ≤ Real.exp (a * x * (p - 1)) * Real.exp (a * x) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.2 ?_
    have := mul_nonneg_of_nonpos_of_nonpos hx (by linarith : p * a - 1 / 2 ≤ 0)
    nlinarith
  have hc0 : 0 ≤ p * (A / a) ^ (p - 1) := by positivity
  calc p * (A / a) ^ (p - 1) * Real.exp (x / 2)
      ≤ p * (A / a) ^ (p - 1) * (Real.exp (a * x * (p - 1)) * Real.exp (a * x)) := by gcongr
    _ = p * (A / a * Real.exp (a * x)) ^ (p - 1) * Real.exp (a * x) := by rw [e]; ring
    _ ≤ p * scaleLow κ σ x ^ (p - 1) * scaleDensity κ σ x := by
        have : 0 ≤ (A / a * Real.exp (a * x)) ^ (p - 1) := by positivity
        gcongr
    _ = scalePowD κ σ p x := rfl

theorem inv_one_add_cosh_le_two_mul_exp {x : ℝ} : 1 / (1 + Real.cosh x) ≤ 2 * Real.exp x := by
  have hc : 0 < 1 + Real.cosh x := by linarith [Real.cosh_pos x]
  rw [div_le_iff₀ hc, Real.cosh_eq]
  have h := Real.exp_pos x
  have h' := Real.exp_pos (-x)
  have he : Real.exp x * Real.exp (-x) = 1 := by rw [← Real.exp_add]; simp
  nlinarith

/-- **`1/(1 + cosh x) ≤ C φ'(x)²` on `x ≤ 0`** (for `p a ≤ 1/2`). -/
theorem exists_inv_one_add_cosh_le_scalePowD (hκ : 0 < κ) (hσ : -1 < σ) {p : ℝ} (hp0 : 0 < p)
    (hp1 : p ≤ 1) (hpa : p * (2 * (σ + 1) / κ) ≤ 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ≤ 0, 1 / (1 + Real.cosh x) ≤ C * scalePowD κ σ p x ^ 2 := by
  set c := p * (Real.exp (4 / κ * Real.log 2) / (2 * (σ + 1) / κ)) ^ (p - 1) with hc_def
  have ha : 0 < 2 * (σ + 1) / κ := by
    have : 0 < σ + 1 := by linarith
    positivity
  have hc : 0 < c := by positivity
  refine ⟨2 / c ^ 2, by positivity, fun x hx => ?_⟩
  have h1 := le_scalePowD hκ hσ hp0 hp1 hpa hx
  rw [← hc_def] at h1
  have h3 : (c * Real.exp (x / 2)) ^ 2 ≤ scalePowD κ σ p x ^ 2 :=
    pow_le_pow_left₀ (by positivity) h1 2
  have h4 : Real.exp x = Real.exp (x / 2) ^ 2 := by
    rw [sq, ← Real.exp_add]; ring_nf
  calc 1 / (1 + Real.cosh x) ≤ 2 * Real.exp x := inv_one_add_cosh_le_two_mul_exp
    _ = 2 / c ^ 2 * (c * Real.exp (x / 2)) ^ 2 := by
        rw [h4]; field_simp
    _ ≤ 2 / c ^ 2 * scalePowD κ σ p x ^ 2 := by gcongr

end Zhan

end InteractingSLE
