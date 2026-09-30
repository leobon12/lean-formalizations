/-
Copyright (c) 2026 Leonardo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo (with Claude Code)
-/
import QuantumZipper.Proofs.RS.OnePointState
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# RS S1-W: the parabolic barrier for the one-point radial generator

Blueprint `blueprint/EXT_RS_BLUEPRINT.md`, node S1-W (EXT-RS §9).

The one-point state of the forward Loewner flow (node S1-0, `Proofs/RS/OnePointState.lean`) has
radial generator

`radGen κ φ L θ = −(4/κ) ∂_L φ + ½ ∂²_θ φ + (1 − 4/κ) (cos θ / sin θ) ∂_θ φ`.

The barrier of S1-W is `barrier κ K t₀ L₀ L θ = e^{K σ} W_p(ξ)`, with the *remaining radial time*
`σ = t₀ + (κ/4)(L − L₀)`, `ξ = sin θ/√σ`, `p = 8/κ − 1`, and the profile

`W_p(ξ) = ∫_0^ξ η^{p−1} e^{−η²/2} dη / ∫_0^∞ η^{p−1} e^{−η²/2} dη`.

Its point is the exact cancellation

`radGen κ barrier L θ = e^{Kσ} (−K W_p(ξ) + ½ ξ W_p'(ξ) (ξ² − 1))`

valid for every `κ < 8` and on all of `(0,π)`: `−(4/κ) ∂_L = −∂_σ`, and the terms
`½ W'' + (1 − 4/κ) W'/ξ` combine to `−½ ξ W'` because `½(p − 1) = 4/κ − 1` and
`cos²θ/σ = 1/σ − ξ²`, using `W'' = W'((p − 1)/ξ − ξ)`. Since `W_p` increases from `0` to `1` and
`W_p'(ξ) ≍ ξ^{p−1}` at `0`, some constant `K ≥ 0` makes the bracket non-positive everywhere on
`(0,∞)`, so `barrier` is a `radGen`-supersolution. (`W_p` is the exact survival function of the
Bessel process `BES(2 − β)`, Revuz–Yor XI Exercise (1.23).)

**This is an own argument** (EXT-RS §9). It replaces Lawler–Zhou arXiv:1006.4936 Lemma 2.2 (26)
(proved there by coupling, the invariant density and an OU entrance-from-∞ argument) and
Lawler–Werness arXiv:1011.3551 Lemma 2.9. The Lean proof below is self-contained real analysis:
Gaussian-type integrals, FTC-1 for the `ξ`-derivative, and two chain-rule differentiations of the
barrier along `θ` (the second one through an eventual-equality of derivatives).
-/

noncomputable section

open Set Filter MeasureTheory intervalIntegral
open scoped Topology ENNReal

namespace QuantumZipper
namespace RS

/-! ## 1. The barrier profile and its basic properties -/

/-- The Gaussian-type integrand `η ↦ η^{p−1} e^{−η²/2}` of the barrier. -/
def barG (p η : ℝ) : ℝ := η ^ (p - 1) * Real.exp (-η ^ 2 / 2)

/-- The normalising constant `∫_0^∞ η^{p−1} e^{−η²/2} dη` of the barrier profile. -/
def barDen (p : ℝ) : ℝ := ∫ η in Set.Ioi (0 : ℝ), barG p η

/-- The inner integral `∫_0^ξ η^{p−1} e^{−η²/2} dη` of the barrier profile. -/
def barNum (p ξ : ℝ) : ℝ := ∫ η in (0 : ℝ)..ξ, barG p η

/-- **The parabolic barrier profile** `W_p(ξ) = ∫_0^ξ η^{p−1} e^{−η²/2} dη / ∫_0^∞ η^{p−1}
e^{−η²/2} dη`. -/
def barW (p ξ : ℝ) : ℝ := (∫ η in (0 : ℝ)..ξ, η ^ (p - 1) * Real.exp (-η ^ 2 / 2)) /
  ∫ η in Set.Ioi (0 : ℝ), η ^ (p - 1) * Real.exp (-η ^ 2 / 2)

theorem barW_eq (p ξ : ℝ) : barW p ξ = barNum p ξ / barDen p := rfl

theorem barG_integrableOn (hp : 0 < p) : IntegrableOn (barG p) (Set.Ioi (0 : ℝ)) := by
  have h : IntegrableOn (fun x : ℝ => x ^ (p - 1) * Real.exp (-(1 / 2) * x ^ 2)) (Set.Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_sq (b := 1 / 2) (by norm_num) (by linarith)
  refine h.congr_fun ?_ measurableSet_Ioi
  intro x _
  simp only [barG]
  rw [show -(1 / 2) * x ^ 2 = -x ^ 2 / 2 by ring]

theorem intervalIntegrable_barG (hp : 0 < p) (hξ : 0 ≤ ξ) :
    IntervalIntegrable (barG p) volume 0 ξ :=
  ⟨(barG_integrableOn hp).mono_set fun x hx => hx.1,
    (barG_integrableOn hp).mono_set fun x hx =>
      absurd hx.2 (not_le.mpr (lt_of_le_of_lt hξ hx.1))⟩

theorem barDen_pos (hp : 0 < p) : 0 < barDen p := by
  rw [barDen]
  refine (setIntegral_pos_iff_support_of_nonneg_ae ?_ (barG_integrableOn hp)).mpr ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg (Real.rpow_nonneg hx.le _) (Real.exp_pos _).le
  · have hsub : Set.Ioi (0 : ℝ) ⊆ Function.support (barG p) ∩ Set.Ioi 0 := by
      intro x hx
      exact ⟨mul_ne_zero (Real.rpow_pos_of_pos hx _).ne' (Real.exp_pos _).ne', hx⟩
    exact lt_of_lt_of_le (by rw [Real.volume_Ioi]; exact ENNReal.zero_lt_top)
      (measure_mono hsub)

theorem barNum_nonneg (hp : 0 < p) (hξ : 0 ≤ ξ) : 0 ≤ barNum p ξ := by
  rw [barNum, intervalIntegral.integral_of_le hξ]
  exact setIntegral_nonneg measurableSet_Ioc
    (fun x hx => mul_nonneg (Real.rpow_nonneg hx.1.le _) (Real.exp_pos _).le)

theorem barNum_pos (hp : 0 < p) (hξ : 0 < ξ) : 0 < barNum p ξ := by
  rw [barNum, intervalIntegral.integral_of_le hξ.le]
  refine (setIntegral_pos_iff_support_of_nonneg_ae ?_ ?_).mpr ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact mul_nonneg (Real.rpow_nonneg hx.1.le _) (Real.exp_pos _).le
  · exact (barG_integrableOn hp).mono_set (fun x hx => hx.1)
  · have hsub : Set.Ioo (0 : ℝ) ξ ⊆ Function.support (barG p) ∩ Set.Ioc 0 ξ := by
      intro x hx
      exact ⟨mul_ne_zero (Real.rpow_pos_of_pos hx.1 _).ne' (Real.exp_pos _).ne',
        ⟨hx.1, hx.2.le⟩⟩
    refine lt_of_lt_of_le ?_ (measure_mono hsub)
    rw [Real.volume_Ioo, ENNReal.ofReal_pos]
    linarith

theorem barNum_le_barDen (hp : 0 < p) (hξ : 0 ≤ ξ) : barNum p ξ ≤ barDen p := by
  rw [barNum, barDen, intervalIntegral.integral_of_le hξ]
  refine setIntegral_mono_set (barG_integrableOn hp) ?_ ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg (Real.rpow_nonneg hx.le _) (Real.exp_pos _).le
  · exact (show Ioc (0 : ℝ) ξ ⊆ Ioi 0 from fun x hx => hx.1).eventuallySubset

theorem barW_mem_Icc (hp : 0 < p) (hξ : 0 ≤ ξ) : barW p ξ ∈ Set.Icc (0 : ℝ) 1 := by
  have hD := barDen_pos hp
  constructor
  · rw [barW_eq]
    exact div_nonneg (barNum_nonneg hp hξ) hD.le
  · rw [barW_eq, div_le_one hD]
    exact barNum_le_barDen hp hξ

theorem barNum_mono (hp : 0 < p) (h0 : 0 ≤ ξ) (h : ξ ≤ ξ') : barNum p ξ ≤ barNum p ξ' := by
  rw [barNum, barNum, intervalIntegral.integral_of_le h0,
    intervalIntegral.integral_of_le (h0.trans h)]
  refine setIntegral_mono_set ((barG_integrableOn hp).mono_set (fun x hx => hx.1)) ?_ ?_
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    exact mul_nonneg (Real.rpow_nonneg hx.1.le _) (Real.exp_pos _).le
  · exact (show Ioc (0 : ℝ) ξ ⊆ Ioc 0 ξ' from fun x hx => ⟨hx.1, hx.2.trans h⟩).eventuallySubset

theorem barW_mono (hp : 0 < p) (h0 : 0 ≤ ξ) (h : ξ ≤ ξ') : barW p ξ ≤ barW p ξ' := by
  rw [barW_eq, barW_eq]
  exact div_le_div_of_nonneg_right (barNum_mono hp h0 h) (barDen_pos hp).le

/-- Comparison with the elementary integral: `∫_0^ξ η^{p−1} dη = ξ^p/p`. -/
theorem barNum_le_rpow_div (hp : 0 < p) (hξ : 0 ≤ ξ) : barNum p ξ ≤ ξ ^ p / p := by
  rcases eq_or_lt_of_le hξ with h0 | hξpos
  · rw [← h0, barNum, intervalIntegral.integral_same, Real.zero_rpow hp.ne', zero_div]
  · have hr : -1 < p - 1 := by linarith
    have h1 : barNum p ξ ≤ ∫ η in (0 : ℝ)..ξ, η ^ (p - 1) := by
      rw [barNum]
      refine intervalIntegral.integral_mono_on hξpos.le (intervalIntegrable_barG hp hξpos.le)
        (intervalIntegrable_rpow' hr) fun x hx => ?_
      rw [barG]
      exact mul_le_of_le_one_right (Real.rpow_nonneg hx.1 _)
        (Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x]))
    have h2 : (∫ η in (0 : ℝ)..ξ, η ^ (p - 1)) = ξ ^ p / p := by
      rw [integral_rpow (Or.inl hr), Real.zero_rpow (by linarith : p - 1 + 1 ≠ 0), sub_zero,
        show p - 1 + 1 = p by ring]
    linarith

theorem barW_le_rpow (hp : 0 < p) : ∃ C, ∀ ξ ≥ 0, barW p ξ ≤ C * ξ ^ p := by
  refine ⟨1 / (p * barDen p), fun ξ hξ => ?_⟩
  have hD := barDen_pos hp
  rw [barW_eq, div_le_iff₀ hD]
  calc barNum p ξ ≤ ξ ^ p / p := barNum_le_rpow_div hp hξ
    _ = (1 / (p * barDen p) * ξ ^ p) * barDen p := by
        field_simp

/-! ## 2. Smoothness and derivatives of the profile -/

theorem hasDerivAt_barW (hp : 0 < p) (hξ : 0 < ξ) :
    HasDerivAt (barW p) (ξ ^ (p - 1) * Real.exp (-ξ ^ 2 / 2) /
      ∫ η in Set.Ioi (0 : ℝ), η ^ (p - 1) * Real.exp (-η ^ 2 / 2)) ξ := by
  have hInt := barG_integrableOn hp
  have hc : ContinuousAt (barG p) ξ := by
    show ContinuousAt (fun η : ℝ => η ^ (p - 1) * Real.exp (-η ^ 2 / 2)) ξ
    exact ContinuousAt.mul (Real.continuousAt_rpow_const ξ (p - 1) (Or.inl hξ.ne'))
      (by fun_prop)
  have hsm : StronglyMeasurableAtFilter (barG p) (𝓝 ξ) volume :=
    AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem
      ((show Integrable (barG p) (volume.restrict (Set.Ioi 0)) from hInt).aestronglyMeasurable)
      (isOpen_Ioi.mem_nhds hξ)
  have hmain := intervalIntegral.integral_hasDerivAt_right (intervalIntegrable_barG hp hξ.le)
    hsm hc
  have h2 := hmain.div_const (barDen p)
  exact h2

/-- The derivative of the integrand: `(η^{p−1} e^{−η²/2})' = η^{p−1} e^{−η²/2} ((p−1)/η − η)`. -/
theorem hasDerivAt_barG (p : ℝ) (hξ : 0 < ξ) :
    HasDerivAt (barG p) (barG p ξ * ((p - 1) / ξ - ξ)) ξ := by
  have h1 : HasDerivAt (fun η : ℝ => η ^ (p - 1)) ((p - 1) * ξ ^ (p - 2)) ξ := by
    simpa only [show p - 1 - 1 = p - 2 by ring] using
      Real.hasDerivAt_rpow_const (x := ξ) (p := p - 1) (Or.inl hξ.ne')
  have h2 : HasDerivAt (fun η : ℝ => Real.exp (-η ^ 2 / 2))
      (Real.exp (-ξ ^ 2 / 2) * (-ξ)) ξ := by
    have h3 : HasDerivAt (fun η : ℝ => -η ^ 2 / 2) (-ξ) ξ := by
      have h4 : HasDerivAt (fun η : ℝ => η ^ 2) (2 * ξ) ξ := by
        simpa using hasDerivAt_pow 2 ξ
      have h5 := h4.neg.div_const 2
      refine h5.congr_deriv ?_
      ring
    exact h3.exp
  have h6 := h1.mul h2
  show HasDerivAt (fun η : ℝ => η ^ (p - 1) * Real.exp (-η ^ 2 / 2))
    (ξ ^ (p - 1) * Real.exp (-ξ ^ 2 / 2) * ((p - 1) / ξ - ξ)) ξ
  refine h6.congr_deriv ?_
  rw [show p - 2 = p - 1 - 1 by ring, Real.rpow_sub hξ, Real.rpow_one]
  first | (field_simp; ring) | field_simp

theorem hasDerivAt_deriv_barW (hp : 0 < p) (hξ : 0 < ξ) :
    HasDerivAt (deriv (barW p)) (deriv (barW p) ξ * ((p - 1) / ξ - ξ)) ξ := by
  have hev : deriv (barW p) =ᶠ[𝓝 ξ] fun η => barG p η / barDen p := by
    filter_upwards [isOpen_Ioi.mem_nhds hξ] with η hη
    exact (hasDerivAt_barW hp hη).deriv
  have h1 : HasDerivAt (fun η => barG p η / barDen p)
      (barG p ξ / barDen p * ((p - 1) / ξ - ξ)) ξ :=
    (hasDerivAt_barG p hξ).div_const _ |>.congr_deriv (by ring)
  have h2 := h1.congr_of_eventuallyEq hev
  have hval : barG p ξ / barDen p * ((p - 1) / ξ - ξ)
      = deriv (barW p) ξ * ((p - 1) / ξ - ξ) := by
    rw [(hasDerivAt_barW hp hξ).deriv]
    rfl
  exact h2.congr_deriv hval

theorem deriv_deriv_barW (hp : 0 < p) (hξ : 0 < ξ) :
    deriv (deriv (barW p)) ξ = deriv (barW p) ξ * ((p - 1) / ξ - ξ) :=
  (hasDerivAt_deriv_barW hp hξ).deriv

/-! ## 3. The constant `K` of the barrier -/

/-- `ξ^q e^{−ξ²/2}` is bounded on `[0,∞)` by `e^{q²/2}`. -/
theorem rpow_mul_exp_neg_sq_half_le (hq : 0 ≤ q) (hξ : 0 ≤ ξ) :
    ξ ^ q * Real.exp (-ξ ^ 2 / 2) ≤ Real.exp (q ^ 2 / 2) := by
  have hexp : ξ ≤ Real.exp ξ := by linarith [Real.add_one_le_exp ξ]
  have h1 : ξ ^ q ≤ Real.exp ξ ^ q := Real.rpow_le_rpow hξ hexp hq
  have h2 : Real.exp ξ ^ q = Real.exp (ξ * q) := (Real.exp_mul ξ q).symm
  calc ξ ^ q * Real.exp (-ξ ^ 2 / 2) ≤ Real.exp (ξ * q) * Real.exp (-ξ ^ 2 / 2) := by
        rw [← h2]
        exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
    _ = Real.exp (ξ * q - ξ ^ 2 / 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
    _ ≤ Real.exp (q ^ 2 / 2) := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (ξ - q)])

/-- The positive part of the `K`-inequality is bounded by `e^{(p+3)²/2}/(2 D)` on `ξ > 0`. -/
theorem mul_deriv_barW_le (hp : 0 < p) (hξ : 0 < ξ) :
    ξ * deriv (barW p) ξ * (ξ ^ 2 - 1) / 2 ≤ Real.exp ((p + 3) ^ 2 / 2) / (2 * barDen p) := by
  have hD := barDen_pos hp
  have hd : deriv (barW p) ξ = ξ ^ (p - 1) * Real.exp (-ξ ^ 2 / 2) / barDen p :=
    (hasDerivAt_barW hp hξ).deriv
  have hpw : ξ ^ (p + 2) = ξ * ξ ^ (p - 1) * ξ ^ 2 := by
    rw [show p + 2 = 1 + (p - 1) + 2 by ring]
    conv_lhs => rw [Real.rpow_add hξ, Real.rpow_add hξ]
    rw [Real.rpow_one, Real.rpow_two]
  have hb : ξ ^ (p + 2) * Real.exp (-ξ ^ 2 / 2) ≤ Real.exp ((p + 3) ^ 2 / 2) := by
    have h1 := rpow_mul_exp_neg_sq_half_le (q := p + 2) (by linarith) hξ.le
    have h2 : Real.exp ((p + 2) ^ 2 / 2) ≤ Real.exp ((p + 3) ^ 2 / 2) :=
      Real.exp_le_exp.mpr (by nlinarith)
    linarith
  rw [hd]
  have hstep : 0 ≤ ξ * (ξ ^ (p - 1) * Real.exp (-ξ ^ 2 / 2) / barDen p) :=
    mul_nonneg hξ.le
      (div_nonneg (mul_nonneg (Real.rpow_nonneg hξ.le _) (Real.exp_pos _).le) hD.le)
  calc ξ * (ξ ^ (p - 1) * Real.exp (-ξ ^ 2 / 2) / barDen p) * (ξ ^ 2 - 1) / 2
      ≤ ξ * (ξ ^ (p - 1) * Real.exp (-ξ ^ 2 / 2) / barDen p) * ξ ^ 2 / 2 := by
        nlinarith [hstep, sq_nonneg ξ, show ξ ^ 2 - 1 ≤ ξ ^ 2 by linarith]
    _ = ξ ^ (p + 2) * Real.exp (-ξ ^ 2 / 2) / (2 * barDen p) := by
        rw [show ξ ^ (p + 2) * Real.exp (-ξ ^ 2 / 2) / (2 * barDen p)
              = ξ * ξ ^ (p - 1) * ξ ^ 2 * Real.exp (-ξ ^ 2 / 2) / (2 * barDen p) by
            rw [hpw]]
        ring
    _ ≤ Real.exp ((p + 3) ^ 2 / 2) / (2 * barDen p) :=
        div_le_div_of_nonneg_right hb (by linarith)

/-- For `ξ ≤ 1` the `K`-inequality holds for every `K ≥ 0`. -/
theorem barrier_neg_of_le_one (hp : 0 < p) (hK : 0 ≤ K) (hξ0 : 0 < ξ) (hξ1 : ξ ≤ 1) :
    -K * barW p ξ + ξ * deriv (barW p) ξ * (ξ ^ 2 - 1) / 2 ≤ 0 := by
  have hD := barDen_pos hp
  have hd : deriv (barW p) ξ = ξ ^ (p - 1) * Real.exp (-ξ ^ 2 / 2) / barDen p :=
    (hasDerivAt_barW hp hξ0).deriv
  have hW : 0 ≤ barW p ξ := (barW_mem_Icc hp hξ0.le).1
  have hW' : 0 ≤ deriv (barW p) ξ := by
    rw [hd]
    exact div_nonneg (mul_nonneg (Real.rpow_nonneg hξ0.le _) (Real.exp_pos _).le) hD.le
  have hsq : ξ ^ 2 ≤ 1 := by nlinarith
  have h1 : -K * barW p ξ ≤ 0 := by nlinarith [mul_nonneg hK hW]
  have h2 : ξ * deriv (barW p) ξ * (ξ ^ 2 - 1) / 2 ≤ 0 := by
    have h3 : 0 ≤ ξ * deriv (barW p) ξ := mul_nonneg hξ0.le hW'
    nlinarith [h3, hsq]
  linarith

theorem exists_barK (hp : 0 < p) : ∃ K ≥ 0, ∀ ξ > 0,
    -K * barW p ξ + ξ * deriv (barW p) ξ * (ξ ^ 2 - 1) / 2 ≤ 0 := by
  have hD := barDen_pos hp
  have hW1 : 0 < barW p 1 := by
    rw [barW_eq]
    exact div_pos (barNum_pos hp one_pos) hD
  have hden : 0 < 2 * barDen p * barW p 1 := mul_pos (mul_pos two_pos hD) hW1
  refine ⟨Real.exp ((p + 3) ^ 2 / 2) / (2 * barDen p * barW p 1), ?_, fun ξ hξ => ?_⟩
  · exact div_nonneg (Real.exp_pos _).le hden.le
  · have hKm : 0 ≤ Real.exp ((p + 3) ^ 2 / 2) / (2 * barDen p * barW p 1) :=
      div_nonneg (Real.exp_pos _).le hden.le
    rcases le_or_gt ξ 1 with h1 | h1
    · exact barrier_neg_of_le_one hp hKm hξ h1
    · have hWle : barW p 1 ≤ barW p ξ := barW_mono hp one_pos.le h1.le
      have hkey : Real.exp ((p + 3) ^ 2 / 2) / (2 * barDen p * barW p 1) * barW p 1
          = Real.exp ((p + 3) ^ 2 / 2) / (2 * barDen p) := by
        field_simp
      have h3 : Real.exp ((p + 3) ^ 2 / 2) / (2 * barDen p * barW p 1) * barW p 1
          ≤ Real.exp ((p + 3) ^ 2 / 2) / (2 * barDen p * barW p 1) * barW p ξ :=
        mul_le_mul_of_nonneg_left hWle hKm
      have h4 := mul_deriv_barW_le hp hξ
      linarith

/-! ## 4. The barrier and the radial-generator identity -/

/-- Trigonometry bookkeeping: `(cos θ/√σ)² = 1/σ − (sin θ/√σ)²` for `σ > 0`. -/
theorem cos_div_sqrt_sq (hσ : 0 < σ) :
    (Real.cos θ / Real.sqrt σ) ^ 2 = 1 / σ - (Real.sin θ / Real.sqrt σ) ^ 2 := by
  have h1 : Real.cos θ ^ 2 = 1 - Real.sin θ ^ 2 := by
    linarith [Real.sin_sq_add_cos_sq θ]
  rw [div_pow, div_pow, Real.sq_sqrt hσ.le, h1, sub_div]

/-- The same identity in the product form produced by the chain rule. -/
theorem cos_div_sqrt_mul_self (hσ : 0 < σ) :
    (Real.cos θ / Real.sqrt σ) * (Real.cos θ / Real.sqrt σ)
      = 1 / σ - (Real.sin θ / Real.sqrt σ) ^ 2 := by
  rw [← sq]
  exact cos_div_sqrt_sq (θ := θ) hσ

/-- `(cos θ/sin θ)(cos θ/√σ) = (1/σ − (sin θ/√σ)²)/(sin θ/√σ)` for `σ > 0`, `sin θ > 0`. -/
theorem cos_div_sin_mul_cos_div_sqrt (hσ : 0 < σ) (hsin : 0 < Real.sin θ) :
    (Real.cos θ / Real.sin θ) * (Real.cos θ / Real.sqrt σ)
      = (1 / σ - (Real.sin θ / Real.sqrt σ) ^ 2) / (Real.sin θ / Real.sqrt σ) := by
  have hQ := cos_div_sqrt_sq (σ := σ) (θ := θ) hσ
  rw [← hQ]
  field_simp [Real.sq_sqrt hσ.le]

/-- Derivative of `σ ↦ sin θ/√σ`. -/
theorem hasDerivAt_sin_div_sqrt (hσ : 0 < σ) :
    HasDerivAt (fun σ' : ℝ => Real.sin θ / Real.sqrt σ')
      (-(Real.sin θ) / (2 * σ * Real.sqrt σ)) σ := by
  have h1 : HasDerivAt (fun σ' : ℝ => (Real.sqrt σ')⁻¹)
      (-(1 / (2 * Real.sqrt σ)) / (Real.sqrt σ) ^ 2) σ :=
    (Real.hasDerivAt_sqrt hσ.ne').inv (Real.sqrt_pos.2 hσ).ne'
  have h2 := h1.const_mul (Real.sin θ)
  refine h2.congr_deriv ?_
  rw [Real.sq_sqrt hσ.le]
  first | (field_simp; ring) | field_simp

/-- The `σ`-derivative of the barrier at fixed angle: `∂_σ (e^{Kσ} W_p(sin θ/√σ))
= e^{Kσ} (K W_p(ξ) − ½ (ξ/σ) W_p'(ξ))`, `ξ = sin θ/√σ`. -/
theorem hasDerivAt_exp_barW_sigma (hp : 0 < p) (hσ : 0 < σ) (hsin : 0 < Real.sin θ) :
    HasDerivAt (fun σ' : ℝ => Real.exp (K * σ') * barW p (Real.sin θ / Real.sqrt σ'))
      (Real.exp (K * σ) * (K * barW p (Real.sin θ / Real.sqrt σ)
        - (1 / 2) * ((Real.sin θ / Real.sqrt σ) / σ) * deriv (barW p) (Real.sin θ / Real.sqrt σ)))
      σ := by
  have hξpos : 0 < Real.sin θ / Real.sqrt σ := div_pos hsin (Real.sqrt_pos.2 hσ)
  have hW : HasDerivAt (barW p) (deriv (barW p) (Real.sin θ / Real.sqrt σ))
      (Real.sin θ / Real.sqrt σ) := (hasDerivAt_barW hp hξpos).differentiableAt.hasDerivAt
  have hcomp := hW.comp σ (hasDerivAt_sin_div_sqrt (θ := θ) hσ)
  have hexp : HasDerivAt (fun σ' : ℝ => Real.exp (K * σ')) (Real.exp (K * σ) * K) σ := by
    have h : HasDerivAt (fun σ' : ℝ => K * σ') K σ := by
      simpa using (hasDerivAt_id σ).const_mul K
    exact h.exp
  have hprod := hexp.mul hcomp
  refine hprod.congr_deriv ?_
  simp only [Function.comp_apply]
  rw [div_div, mul_comm (Real.sqrt σ) σ]
  first | (field_simp; ring) | field_simp

/-- The `θ`-derivative of the barrier at fixed radial time. -/
theorem hasDerivAt_exp_barW_theta (hp : 0 < p) (hσ : 0 < σ) (hsin : 0 < Real.sin θ) :
    HasDerivAt (fun θ' : ℝ => Real.exp (K * σ) * barW p (Real.sin θ' / Real.sqrt σ))
      (Real.exp (K * σ)
        * (deriv (barW p) (Real.sin θ / Real.sqrt σ) * (Real.cos θ / Real.sqrt σ))) θ := by
  have hξpos : 0 < Real.sin θ / Real.sqrt σ := div_pos hsin (Real.sqrt_pos.2 hσ)
  have hW : HasDerivAt (barW p) (deriv (barW p) (Real.sin θ / Real.sqrt σ))
      (Real.sin θ / Real.sqrt σ) := (hasDerivAt_barW hp hξpos).differentiableAt.hasDerivAt
  have hsin' : HasDerivAt (fun θ' : ℝ => Real.sin θ' / Real.sqrt σ)
      (Real.cos θ / Real.sqrt σ) θ := (Real.hasDerivAt_sin θ).div_const _
  exact (hW.comp θ hsin').const_mul (Real.exp (K * σ))

/-- The second `θ`-derivative of the barrier at fixed radial time. -/
theorem hasDerivAt_deriv_exp_barW_theta (hp : 0 < p) (hσ : 0 < σ) (hsin : 0 < Real.sin θ) :
    HasDerivAt (deriv (fun θ' : ℝ => Real.exp (K * σ) * barW p (Real.sin θ' / Real.sqrt σ)))
      (Real.exp (K * σ) * (deriv (deriv (barW p)) (Real.sin θ / Real.sqrt σ)
        * ((Real.cos θ / Real.sqrt σ) * (Real.cos θ / Real.sqrt σ))
        + deriv (barW p) (Real.sin θ / Real.sqrt σ) * (-(Real.sin θ / Real.sqrt σ)))) θ := by
  have hξpos : 0 < Real.sin θ / Real.sqrt σ := div_pos hsin (Real.sqrt_pos.2 hσ)
  have hev : deriv (fun θ' : ℝ => Real.exp (K * σ) * barW p (Real.sin θ' / Real.sqrt σ))
      =ᶠ[𝓝 θ] fun θ' => Real.exp (K * σ)
        * (deriv (barW p) (Real.sin θ' / Real.sqrt σ) * (Real.cos θ' / Real.sqrt σ)) := by
    filter_upwards [(isOpen_lt continuous_const Real.continuous_sin).mem_nhds hsin] with θ' hθ'
    exact (hasDerivAt_exp_barW_theta (p := p) (K := K) (σ := σ) hp hσ hθ').deriv
  have hW' : HasDerivAt (deriv (barW p)) (deriv (deriv (barW p)) (Real.sin θ / Real.sqrt σ))
      (Real.sin θ / Real.sqrt σ) :=
    (hasDerivAt_deriv_barW hp hξpos).differentiableAt.hasDerivAt
  have hsin' : HasDerivAt (fun θ' : ℝ => Real.sin θ' / Real.sqrt σ)
      (Real.cos θ / Real.sqrt σ) θ := (Real.hasDerivAt_sin θ).div_const _
  have hcos' : HasDerivAt (fun θ' : ℝ => Real.cos θ' / Real.sqrt σ)
      (-(Real.sin θ) / Real.sqrt σ) θ := (Real.hasDerivAt_cos θ).div_const _
  have hfull := ((hW'.comp θ hsin').mul hcos').const_mul (Real.exp (K * σ))
  refine (hfull.congr_of_eventuallyEq hev).congr_deriv ?_
  simp only [Function.comp_apply]
  ring

/-- **The barrier** of S1-W, with `σ = t₀ + (κ/4)(L − L₀)` the remaining radial time. -/
def barrier (κ K t₀ L₀ : ℝ) (L θ : ℝ) : ℝ :=
  Real.exp (K * (t₀ + κ / 4 * (L - L₀))) *
    barW (8 / κ - 1) (Real.sin θ / Real.sqrt (t₀ + κ / 4 * (L - L₀)))

theorem radGen_barrier_le (hκ : 0 < κ) (hκ8 : κ < 8) {K : ℝ}
    (hK : ∀ ξ > 0, -K * barW (8 / κ - 1) ξ + ξ * deriv (barW (8 / κ - 1)) ξ * (ξ ^ 2 - 1) / 2 ≤ 0)
    (hσ : 0 < t₀ + κ / 4 * (L - L₀)) (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    radGen κ (barrier κ K t₀ L₀) L θ ≤ 0 := by
  have hp : 0 < 8 / κ - 1 := by
    rw [sub_pos, lt_div_iff₀ hκ]
    linarith
  have hsin : 0 < Real.sin θ := Real.sin_pos_of_mem_Ioo hθ
  set ξ : ℝ := Real.sin θ / Real.sqrt (t₀ + κ / 4 * (L - L₀)) with hξdef
  set ζ : ℝ := Real.cos θ / Real.sqrt (t₀ + κ / 4 * (L - L₀)) with hζdef
  have hξpos : 0 < ξ := by
    rw [hξdef]
    exact div_pos hsin (Real.sqrt_pos.2 hσ)
  have hQ : ζ * ζ = 1 / (t₀ + κ / 4 * (L - L₀)) - ξ ^ 2 := by
    rw [hζdef, hξdef]
    exact cos_div_sqrt_mul_self hσ
  have hR : (Real.cos θ / Real.sin θ) * ζ
      = (1 / (t₀ + κ / 4 * (L - L₀)) - ξ ^ 2) / ξ := by
    rw [hζdef, hξdef]
    exact cos_div_sin_mul_cos_div_sqrt hσ hsin
  have hW'' : deriv (deriv (barW (8 / κ - 1))) ξ
      = deriv (barW (8 / κ - 1)) ξ * ((8 / κ - 1 - 1) / ξ - ξ) :=
    deriv_deriv_barW hp hξpos
  have hD1 : deriv (fun L' => barrier κ K t₀ L₀ L' θ) L
      = (Real.exp (K * (t₀ + κ / 4 * (L - L₀)))
          * (K * barW (8 / κ - 1) ξ
            - (1 / 2) * (ξ / (t₀ + κ / 4 * (L - L₀))) * deriv (barW (8 / κ - 1)) ξ))
        * (κ / 4) := by
    have hσd : HasDerivAt (fun L' : ℝ => t₀ + κ / 4 * (L' - L₀)) (κ / 4) L := by
      simpa using (((hasDerivAt_id L).sub_const L₀).const_mul (κ / 4)).const_add t₀
    have hcomp := (hasDerivAt_exp_barW_sigma (p := 8 / κ - 1) hp (K := K) (θ := θ) hσ hsin).comp
      L hσd
    show deriv (fun L' : ℝ => Real.exp (K * (t₀ + κ / 4 * (L' - L₀)))
        * barW (8 / κ - 1) (Real.sin θ / Real.sqrt (t₀ + κ / 4 * (L' - L₀)))) L
      = (Real.exp (K * (t₀ + κ / 4 * (L - L₀)))
          * (K * barW (8 / κ - 1) ξ
            - (1 / 2) * (ξ / (t₀ + κ / 4 * (L - L₀))) * deriv (barW (8 / κ - 1)) ξ))
        * (κ / 4)
    rw [hξdef]
    exact hcomp.deriv
  have hD3 : deriv (barrier κ K t₀ L₀ L) θ
      = Real.exp (K * (t₀ + κ / 4 * (L - L₀)))
        * (deriv (barW (8 / κ - 1)) ξ * ζ) := by
    have h := (hasDerivAt_exp_barW_theta (p := 8 / κ - 1) hp (K := K) hσ hsin).deriv
    show deriv (fun θ' : ℝ => Real.exp (K * (t₀ + κ / 4 * (L - L₀)))
        * barW (8 / κ - 1) (Real.sin θ' / Real.sqrt (t₀ + κ / 4 * (L - L₀)))) θ
      = Real.exp (K * (t₀ + κ / 4 * (L - L₀))) * (deriv (barW (8 / κ - 1)) ξ * ζ)
    rw [hξdef, hζdef]
    exact h
  have hD2 : deriv (deriv (barrier κ K t₀ L₀ L)) θ
      = Real.exp (K * (t₀ + κ / 4 * (L - L₀)))
        * (deriv (deriv (barW (8 / κ - 1))) ξ * (ζ * ζ)
          + deriv (barW (8 / κ - 1)) ξ * (-ξ)) := by
    have h := (hasDerivAt_deriv_exp_barW_theta (p := 8 / κ - 1) hp (K := K) hσ hsin).deriv
    show deriv (deriv (fun θ' : ℝ => Real.exp (K * (t₀ + κ / 4 * (L - L₀)))
        * barW (8 / κ - 1) (Real.sin θ' / Real.sqrt (t₀ + κ / 4 * (L - L₀))))) θ
      = Real.exp (K * (t₀ + κ / 4 * (L - L₀)))
        * (deriv (deriv (barW (8 / κ - 1))) ξ * (ζ * ζ)
          + deriv (barW (8 / κ - 1)) ξ * (-ξ))
    rw [hξdef, hζdef]
    exact h
  rw [radGen, hD2, hD3, hD1]
  rw [hQ, hW'']
  have hthird : (1 - 4 / κ) * (Real.cos θ / Real.sin θ)
        * (Real.exp (K * (t₀ + κ / 4 * (L - L₀)))
          * (deriv (barW (8 / κ - 1)) ξ * ζ))
      = (1 - 4 / κ) * (Real.exp (K * (t₀ + κ / 4 * (L - L₀)))
          * (deriv (barW (8 / κ - 1)) ξ
            * ((1 / (t₀ + κ / 4 * (L - L₀)) - ξ ^ 2) / ξ))) := by
    rw [show (1 - 4 / κ) * (Real.cos θ / Real.sin θ)
          * (Real.exp (K * (t₀ + κ / 4 * (L - L₀)))
            * (deriv (barW (8 / κ - 1)) ξ * ζ))
        = (1 - 4 / κ) * Real.exp (K * (t₀ + κ / 4 * (L - L₀)))
          * deriv (barW (8 / κ - 1)) ξ * ((Real.cos θ / Real.sin θ) * ζ) from by ring,
      hR]
    ring
  rw [hthird]
  have hkey : -(4 / κ) * ((Real.exp (K * (t₀ + κ / 4 * (L - L₀)))
          * (K * barW (8 / κ - 1) ξ
            - (1 / 2) * (ξ / (t₀ + κ / 4 * (L - L₀))) * deriv (barW (8 / κ - 1)) ξ))
        * (κ / 4))
      + (1 / 2) * (Real.exp (K * (t₀ + κ / 4 * (L - L₀)))
          * (deriv (barW (8 / κ - 1)) ξ * ((8 / κ - 1 - 1) / ξ - ξ)
              * (1 / (t₀ + κ / 4 * (L - L₀)) - ξ ^ 2)
            + deriv (barW (8 / κ - 1)) ξ * (-ξ)))
      + (1 - 4 / κ) * (Real.exp (K * (t₀ + κ / 4 * (L - L₀)))
          * (deriv (barW (8 / κ - 1)) ξ
            * ((1 / (t₀ + κ / 4 * (L - L₀)) - ξ ^ 2) / ξ)))
      = Real.exp (K * (t₀ + κ / 4 * (L - L₀)))
        * (-K * barW (8 / κ - 1) ξ + ξ * deriv (barW (8 / κ - 1)) ξ * (ξ ^ 2 - 1) / 2) := by
    field_simp
    ring
  rw [hkey]
  exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (hK ξ hξpos)

end RS
end QuantumZipper
