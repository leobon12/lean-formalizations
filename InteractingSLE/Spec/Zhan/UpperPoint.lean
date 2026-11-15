/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Foundations.Strip.Chain
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# The upper-point diffusion: the pathwise equation (3.15) and the scale density (3.16)

Packet PROVE-ZHAN-A. Astra §3, "Complete upper-point diffusion calculation" (`ig1_formalization_proofs.txt`
L1170–L1219). For a fixed upper boundary point `x + iπ` put `X_t(x) = Re ψ_t(x + iπ) − ξ_t`. It solves

  `dX_t = −√κ dB_t + (tanh(X_t/2) − σ) dt`                                                        (3.15)

when `ξ_t = √κ B_t + σ t`. With `w_σ(x) = e^{2σx/κ} cosh(x/2)^{−4/κ}`, a primitive `s` of `w_σ` solves

  `(κ/2) s'' + (tanh(x/2) − σ) s' = 0`.                                                             (3.16)

If `|σ| < 1` then `Z = ∫_ℝ w_σ < ∞`; for `σ ≥ 1` the primitive from `−∞` is finite at `−∞` and infinite at `+∞`.

## Main results

* `IsSepMark.stripPoint_eq_add_integral_of_gt` (**(3.15), pathwise**): an upper point path (chordal `y < v`) has
  strip coordinate `p_t = p_0 + ∫₀ᵗ tanh((p_u − ξ_u)/2) du`; hence `X = p − ξ` satisfies
  `X_t − X_0 = −(ξ_t − ξ_0) + ∫₀ᵗ tanh(X_u/2) du` (`IsSepMark.upperGap_eq`);
* `scaleDensity κ σ` (`w_σ`), `scaleDensity_eq_rpow`, `hasDerivAt_scaleDensity`, `scaleDensity_ode` (**(3.16)**);
* `integrable_scaleDensity` (`|σ| < 1`), `integrableOn_scaleDensity_Iic` (`σ > −1`),
  `not_integrableOn_scaleDensity_Ioi` (`σ ≥ 1`, including the critical value `σ = 1`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory

namespace InteractingSLE

namespace Zhan

/-! ### The scale density `w_σ` and (3.16) -/

/-- The scale density `w_σ(x) = e^{2σx/κ} cosh(x/2)^{−4/κ}`, written as one exponential. -/
def scaleDensity (κ σ x : ℝ) : ℝ := Real.exp (2 * σ * x / κ - 4 / κ * Real.log (Real.cosh (x / 2)))

theorem scaleDensity_pos (κ σ x : ℝ) : 0 < scaleDensity κ σ x := Real.exp_pos _

theorem scaleDensity_eq_rpow (κ σ x : ℝ) :
    scaleDensity κ σ x = Real.exp (2 * σ * x / κ) * Real.cosh (x / 2) ^ (-4 / κ) := by
  rw [scaleDensity, Real.rpow_def_of_pos (Real.cosh_pos _), sub_eq_add_neg, Real.exp_add]
  congr 2; ring

theorem continuous_scaleDensity (κ σ : ℝ) : Continuous (scaleDensity κ σ) := by
  unfold scaleDensity
  refine Real.continuous_exp.comp ((by fun_prop : Continuous fun x : ℝ => 2 * σ * x / κ).sub
    (continuous_const.mul ?_))
  exact (Real.continuous_cosh.comp (by fun_prop : Continuous fun x : ℝ => x / 2)).log fun x =>
    (Real.cosh_pos _).ne'

/-- `d/dx log cosh(x/2) = ½ tanh(x/2)`. -/
theorem hasDerivAt_log_cosh_half (x : ℝ) :
    HasDerivAt (fun x => Real.log (Real.cosh (x / 2))) (Real.tanh (x / 2) / 2) x := by
  have h1 : HasDerivAt (fun x : ℝ => x / 2) (1 / 2) x := by simpa using (hasDerivAt_id x).div_const 2
  have h2 := (Real.hasDerivAt_cosh (x / 2)).comp x h1
  have h3 := h2.log (Real.cosh_pos _).ne'
  refine h3.congr_deriv ?_
  rw [Real.tanh_eq_sinh_div_cosh]
  simp only [Function.comp_apply]
  ring

/-- `w_σ' = w_σ (2σ/κ − (2/κ) tanh(x/2))`. -/
theorem hasDerivAt_scaleDensity (κ σ x : ℝ) :
    HasDerivAt (scaleDensity κ σ) (scaleDensity κ σ x * (2 * σ / κ - 2 / κ * Real.tanh (x / 2))) x := by
  have h1 : HasDerivAt (fun x : ℝ => 2 * σ * x / κ) (2 * σ / κ) x := by
    simpa using ((hasDerivAt_id x).const_mul (2 * σ)).div_const κ
  have h2 := h1.sub ((hasDerivAt_log_cosh_half x).const_mul (4 / κ))
  refine (h2.exp).congr_deriv ?_
  simp only [scaleDensity, Pi.sub_apply]
  ring

/-- **(3.16)**: `(κ/2) w_σ' + (tanh(x/2) − σ) w_σ = 0`, i.e. a primitive `s` of `w_σ` solves
`(κ/2) s'' + (tanh(x/2) − σ) s' = 0`, so `s(X_t)` is driftless along (3.15). -/
theorem scaleDensity_ode {κ : ℝ} (hκ : κ ≠ 0) (σ x : ℝ) :
    κ / 2 * (scaleDensity κ σ x * (2 * σ / κ - 2 / κ * Real.tanh (x / 2))) +
      (Real.tanh (x / 2) - σ) * scaleDensity κ σ x = 0 := by
  field_simp
  ring

/-! ### Bounds and integrability -/

theorem abs_div_two_sub_log_two_le_log_cosh (y : ℝ) : |y| - Real.log 2 ≤ Real.log (Real.cosh y) := by
  have hc : Real.exp |y| / 2 ≤ Real.cosh y := by
    rw [Real.cosh_eq]
    rcases le_total 0 y with hy | hy
    · rw [abs_of_nonneg hy]; linarith [Real.exp_pos (-y)]
    · rw [abs_of_nonpos hy]; linarith [Real.exp_pos y]
  have := Real.log_le_log (by positivity) hc
  rwa [Real.log_div (Real.exp_pos _).ne' two_ne_zero, Real.log_exp] at this

theorem log_cosh_le_abs (y : ℝ) : Real.log (Real.cosh y) ≤ |y| := by
  have hc : Real.cosh y ≤ Real.exp |y| := by
    rw [Real.cosh_eq]
    have h1 := Real.exp_le_exp.2 (le_abs_self y)
    have h2 := Real.exp_le_exp.2 (neg_le_abs y)
    linarith
  have := Real.log_le_log (Real.cosh_pos y) hc
  rwa [Real.log_exp] at this

/-- `w_σ(x) ≤ 2^{4/κ} e^{2(σx − |x|)/κ}`. -/
theorem scaleDensity_le {κ : ℝ} (hκ : 0 < κ) (σ x : ℝ) :
    scaleDensity κ σ x ≤ Real.exp (4 / κ * Real.log 2) * Real.exp (2 * (σ * x - |x|) / κ) := by
  rw [← Real.exp_add, scaleDensity]
  refine Real.exp_le_exp.2 ?_
  have h := abs_div_two_sub_log_two_le_log_cosh (x / 2)
  rw [abs_div, abs_two] at h
  have h4 : 0 < 4 / κ := by positivity
  have := mul_le_mul_of_nonneg_left h h4.le
  have e1 : 2 * σ * x / κ = 4 / κ * (σ * x / 2) := by field_simp; ring
  have e2 : 2 * (σ * x - |x|) / κ = 4 / κ * ((σ * x - |x|) / 2) := by field_simp; ring
  rw [e1, e2]
  nlinarith

/-- `w_σ(x) ≥ e^{2(σx − |x|)/κ}`. -/
theorem le_scaleDensity {κ : ℝ} (hκ : 0 < κ) (σ x : ℝ) :
    Real.exp (2 * (σ * x - |x|) / κ) ≤ scaleDensity κ σ x := by
  rw [scaleDensity]
  refine Real.exp_le_exp.2 ?_
  have h := log_cosh_le_abs (x / 2)
  rw [abs_div, abs_two] at h
  have h4 : 0 < 4 / κ := by positivity
  have := mul_le_mul_of_nonneg_left h h4.le
  have e1 : 2 * σ * x / κ = 4 / κ * (σ * x / 2) := by field_simp; ring
  have e2 : 2 * (σ * x - |x|) / κ = 4 / κ * ((σ * x - |x|) / 2) := by field_simp; ring
  rw [e1, e2]
  nlinarith

/-- For `σ > −1`, `w_σ` is integrable at `−∞`. -/
theorem integrableOn_scaleDensity_Iic {κ : ℝ} (hκ : 0 < κ) {σ : ℝ} (hσ : -1 < σ) :
    IntegrableOn (scaleDensity κ σ) (Iic 0) := by
  have hb : 0 < 2 * (σ + 1) / κ := by have : 0 < σ + 1 := by linarith
                                      positivity
  have hg : IntegrableOn (fun x => Real.exp (4 / κ * Real.log 2) * Real.exp (2 * (σ + 1) / κ * x)) (Iic 0) :=
    (integrableOn_exp_mul_Iic hb 0).const_mul _
  refine hg.mono' (continuous_scaleDensity κ σ).aestronglyMeasurable.restrict ?_
  refine (ae_restrict_iff' measurableSet_Iic).2 (Eventually.of_forall fun x hx => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (scaleDensity_pos _ _ _)]
  refine (scaleDensity_le hκ σ x).trans (le_of_eq ?_)
  rw [abs_of_nonpos hx]
  congr 2; ring

/-- For `σ < 1`, `w_σ` is integrable at `+∞`. -/
theorem integrableOn_scaleDensity_Ioi {κ : ℝ} (hκ : 0 < κ) {σ : ℝ} (hσ : σ < 1) :
    IntegrableOn (scaleDensity κ σ) (Ioi 0) := by
  have hb : 0 < 2 * (1 - σ) / κ := by have : 0 < 1 - σ := by linarith
                                      positivity
  have hg : IntegrableOn (fun x => Real.exp (4 / κ * Real.log 2) * Real.exp (-(2 * (1 - σ) / κ) * x))
      (Ioi 0) := (exp_neg_integrableOn_Ioi 0 hb).const_mul _
  refine hg.mono' (continuous_scaleDensity κ σ).aestronglyMeasurable.restrict ?_
  refine (ae_restrict_iff' measurableSet_Ioi).2 (Eventually.of_forall fun x hx => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (scaleDensity_pos _ _ _)]
  refine (scaleDensity_le hκ σ x).trans (le_of_eq ?_)
  rw [abs_of_pos hx]
  congr 2; ring

/-- **`Z = ∫_ℝ w_σ < ∞` for `|σ| < 1`.** -/
theorem integrable_scaleDensity {κ : ℝ} (hκ : 0 < κ) {σ : ℝ} (hσ : |σ| < 1) :
    Integrable (scaleDensity κ σ) := by
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
  exact (integrableOn_scaleDensity_Iic hκ (neg_lt_of_abs_lt hσ)).union
    (integrableOn_scaleDensity_Ioi hκ (lt_of_abs_lt hσ))

/-- **`σ ≥ 1` (including the critical drift `σ = 1`)**: `w_σ ≥ 1` on `[0, ∞)`, so its primitive is infinite at
`+∞`. -/
theorem not_integrableOn_scaleDensity_Ioi {κ : ℝ} (hκ : 0 < κ) {σ : ℝ} (hσ : 1 ≤ σ) :
    ¬ IntegrableOn (scaleDensity κ σ) (Ioi 0) := by
  intro hint
  have h1 : IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Ioi 0) := by
    refine hint.mono' (by fun_prop) ((ae_restrict_iff' measurableSet_Ioi).2
      (Eventually.of_forall fun x hx => ?_))
    rw [norm_one]
    refine le_trans ?_ (le_scaleDensity hκ σ x)
    rw [abs_of_pos (show (0 : ℝ) < x from hx)]
    refine Real.one_le_exp_iff.2 (div_nonneg ?_ hκ.le)
    nlinarith [show (0 : ℝ) < x from hx]
  rw [integrableOn_const_iff] at h1
  rcases h1 with h | h
  · simp at h
  · exact absurd h (by simp)

end Zhan

/-! ### (3.15) pathwise: upper points in the strip clock -/

namespace Strip

namespace IsSepMark

variable {w v : ℝ → ℝ} {S : ℝ}

/-- A real point path that stays off the end mark has a continuous strip coordinate. -/
theorem continuousOn_stripPoint (h : IsSepMark w v S) {y : ℝ → ℝ} (hy : ContinuousOn y (Icc 0 S))
    (hyv : ∀ s ∈ Icc 0 S, y s ≠ v s) :
    ContinuousOn (stripPoint w v y) (Icc 0 (stripClock w v S)) := by
  have hc : ContinuousOn (fun t => y (chordalTime w v t) - v (chordalTime w v t))
      (Icc 0 (stripClock w v S)) :=
    (hy.comp h.continuousOn_chordalTime h.mapsTo_chordalTime).sub
      (h.continuousOn_v.comp h.continuousOn_chordalTime h.mapsTo_chordalTime)
  exact continuousOn_id.add (hc.abs.log fun t ht =>
    (abs_pos.2 (sub_ne_zero.2 (hyv _ (h.chordalTime_mem ht)))).ne')

/-- **(3.15), pathwise, for upper points**: if the chordal point path `y` (the image of an upper boundary point
`x + iπ`) stays strictly left of the end mark on `[0, S]`, its strip coordinate solves
`p_t = p_0 + ∫₀ᵗ tanh((p_u − ξ_u)/2) du` on `[0, t(S)]`. -/
theorem stripPoint_eq_add_integral_of_gt (h : IsSepMark w v S) {y : ℝ → ℝ}
    (hy : ContinuousOn y (Icc 0 S)) (hint : IntervalIntegrable (fun u => 2 / (y u - w u)) volume 0 S)
    (heq : ∀ s ∈ Icc 0 S, y s = y 0 + ∫ u in (0 : ℝ)..s, 2 / (y u - w u))
    (hyv : ∀ s ∈ Icc 0 S, y s < v s) {t : ℝ} (ht : t ∈ Icc 0 (stripClock w v S)) :
    stripPoint w v y t = stripPoint w v y 0 +
      ∫ u in (0 : ℝ)..t, Real.tanh ((stripPoint w v y u - stripDriver w v u) / 2) := by
  have hsub : Icc 0 t ⊆ Icc 0 (stripClock w v S) := Icc_subset_Icc le_rfl ht.2
  have hp := h.continuousOn_stripPoint hy fun s hs => (hyv s hs).ne
  have hg : ContinuousOn (fun u => (stripPoint w v y u - stripDriver w v u) / 2) (Icc 0 t) :=
    ((hp.sub h.continuousOn_stripDriver).div_const 2).mono hsub
  have hcont : ContinuousOn (fun u => Real.tanh ((stripPoint w v y u - stripDriver w v u) / 2))
      (Icc 0 t) := by
    simp only [Real.tanh_eq_sinh_div_cosh]
    exact (Real.continuous_sinh.comp_continuousOn hg).div (Real.continuous_cosh.comp_continuousOn hg)
      fun _ _ => (Real.cosh_pos _).ne'
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le ht.1 (hp.mono hsub)
    (fun u hu => h.hasDerivAt_stripPoint_of_gt hy hint heq ⟨hu.1, hu.2.trans_le ht.2⟩
      (hyv _ (h.chordalTime_mem ⟨hu.1.le, hu.2.le.trans ht.2⟩)))
    (hcont.intervalIntegrable_of_Icc ht.1)]
  ring

/-- **(3.15) for the gap `X = p − ξ`** of an upper point: `X_t − X_0 = −(ξ_t − ξ_0) + ∫₀ᵗ tanh(X_u/2) du`.
With `ξ_t = √κ B_t + σ t` this is `dX = −√κ dB + (tanh(X/2) − σ) dt`. -/
theorem upperGap_eq (h : IsSepMark w v S) {y : ℝ → ℝ}
    (hy : ContinuousOn y (Icc 0 S)) (hint : IntervalIntegrable (fun u => 2 / (y u - w u)) volume 0 S)
    (heq : ∀ s ∈ Icc 0 S, y s = y 0 + ∫ u in (0 : ℝ)..s, 2 / (y u - w u))
    (hyv : ∀ s ∈ Icc 0 S, y s < v s) {t : ℝ} (ht : t ∈ Icc 0 (stripClock w v S)) :
    (stripPoint w v y t - stripDriver w v t) - (stripPoint w v y 0 - stripDriver w v 0) =
      -(stripDriver w v t - stripDriver w v 0) +
        ∫ u in (0 : ℝ)..t, Real.tanh ((stripPoint w v y u - stripDriver w v u) / 2) := by
  rw [h.stripPoint_eq_add_integral_of_gt hy hint heq hyv ht]
  ring

end IsSepMark

end Strip

namespace Zhan

end Zhan

end InteractingSLE
