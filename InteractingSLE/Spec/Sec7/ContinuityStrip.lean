/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec4.UpperDrift
import QuantumZipper.Common.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Aux. lemma 98: the strip chart and the deterministic identities (Q1)–(Q4)

Packet PROVE-SEC7-C (specification §7.3, Aux. lemma 98 "A seed force and a separated marked point",
`source/spec/p289-336.md` L688–L734 and `p337-384.md` L1–L11, pp. 334–337). The proof of Aux. lemma 98 maps the strip
`𝕊 = {0 < Im z < π}` to the half-plane by `F(z) = 1 − e^{−z}` (Q1) and studies the strip driver `ξ`, the seed force
coordinate `V` and their gap `X = V − ξ` (Q2). This file proves the deterministic steps:

* (Q1): `F` maps `𝕊` bijectively onto `ℍ` (`bijOn_aux98StripMap`), `F(0) = 0`, the right strip end goes to the mark
  `1` (`tendsto_aux98StripMap_atTop`) and the left end to the original target `∞`
  (`tendsto_norm_aux98StripMap_atBot`);
* Claim 1: `coth(x/2) = 2/(1 − e^{−x}) − 1` (`cothHalf_eq_two_div_one_sub_exp_neg`), and for `x > 0` the function
  `coth(x/2) − 2/x` is bounded between zero and one (`cothHalf_sub_two_div_pos`, `cothHalf_sub_two_div_lt_one`); hence
  the gap drift `A coth(X/2) − σ` is the Bessel drift `2A/X` of dimension `δ = 1 + 2(r + 2)/κ > 1` (after the
  scaling `X/√κ`; `aux98_bessel_dimension`) plus a drift bounded by `A + |σ|` (`aux98_gapDrift_split`);
* (Q2): the parameter identities `A − σ = S − d` (`aux98A_sub_aux98Sigma`, Claim 2), `μ = σ − r/2 = κ/2 − 3 − S`
  (`aux98Mu_eq`) and `μ < 1` for `S > −2`, `κ < 4` (`aux98Mu_lt_one`, (Q4));
* (Q2a)–(Q2c): the chordal coordinates `Ŵ = p − Y`, `V̂¹ = p − e^{−t−V}`, `V̂² = p` have gaps `Y(1 − e^{−X})` and `Y`
  (`aux98_gap_one`, `aux98_gap_two`); the force coordinates solve the chordal Loewner equation in the clock
  `dϑ = Y² dt` (`hasDerivAt_aux98V1`, `hasDerivAt_aux98V2`); the dt-coefficient of `dŴ` given by Itô's formula is the
  chordal force drift `r/(Ŵ − V̂¹) + ρ/(Ŵ − V̂²)` in that clock (`aux98_driver_drift_identity`); and (Q2c) together
  with the strip Loewner equation gives the chordal Loewner equation for `F_t ∘ ψ_t` in the clock `ϑ`
  (`aux98_Q2c`, `hasDerivAt_aux98Ft_comp`);
* Claim 2: the pathwise comparison (Q3) `X_t ≥ −√κ B_t + (S − d) t` (`aux98_Q3`), eventual linear separation from the
  Brownian strong law (`aux98_eventually_linear`), and finiteness of the tail energy of the drift error `e_t` of (Q4)
  (`aux98_integrableOn_sq_error`, reusing `Sec4.integrableOn_sq_correction`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory
open QuantumZipper (H)

namespace InteractingSLE

namespace Sec7

/-! ### (Q1): the strip chart `F(z) = 1 − e^{−z}` -/

/-- The strip `𝕊 = {0 < Im z < π}` of Aux. lemma 98. -/
def aux98Strip : Set ℂ := {z | 0 < z.im ∧ z.im < Real.pi}

/-- (Q1): `F(z) = 1 − e^{−z}`. -/
def aux98StripMap (z : ℂ) : ℂ := 1 - exp (-z)

/-- The inverse of (Q1): `w ↦ −log(1 − w)`. -/
def aux98StripMapInv (w : ℂ) : ℂ := -log (1 - w)

@[simp] theorem aux98StripMap_zero : aux98StripMap 0 = 0 := by simp [aux98StripMap]

/-- `Im F(z) = e^{−Re z} sin(Im z)`. -/
theorem im_aux98StripMap (z : ℂ) : (aux98StripMap z).im = Real.exp (-z.re) * Real.sin z.im := by
  simp only [aux98StripMap, sub_im, one_im, exp_im, neg_re, neg_im, Real.sin_neg]
  ring

theorem aux98StripMap_mem_H {z : ℂ} (hz : z ∈ aux98Strip) : aux98StripMap z ∈ H := by
  show 0 < (aux98StripMap z).im
  rw [im_aux98StripMap]
  exact mul_pos (Real.exp_pos _) (Real.sin_pos_of_pos_of_lt_pi hz.1 hz.2)

theorem aux98StripMapInv_mem {w : ℂ} (hw : w ∈ H) : aux98StripMapInv w ∈ aux98Strip := by
  have hw' : 0 < w.im := hw
  have hne : 1 - w ≠ 0 := by
    intro h; have := congrArg Complex.im h; simp at this; linarith
  have him : (1 - w).im < 0 := by simp; linarith
  have harg : arg (1 - w) < 0 := arg_neg_iff.2 him
  refine ⟨?_, ?_⟩
  · simp only [aux98StripMapInv, neg_im, log_im]; linarith
  · simp only [aux98StripMapInv, neg_im, log_im]; linarith [neg_pi_lt_arg (1 - w)]

theorem aux98StripMap_aux98StripMapInv {w : ℂ} (hw : w ≠ 1) :
    aux98StripMap (aux98StripMapInv w) = w := by
  have hne : 1 - w ≠ 0 := sub_ne_zero.2 (Ne.symm hw)
  simp [aux98StripMap, aux98StripMapInv, exp_log hne]

theorem aux98StripMapInv_aux98StripMap {z : ℂ} (hz : z ∈ aux98Strip) :
    aux98StripMapInv (aux98StripMap z) = z := by
  have h1 : -Real.pi < (-z).im := by simp; linarith [hz.2]
  have h2 : (-z).im ≤ Real.pi := by simp; linarith [hz.1, Real.pi_pos]
  simp [aux98StripMap, aux98StripMapInv, log_exp h1 h2]

/-- (Q1): `F` maps the strip bijectively onto the upper half-plane. -/
theorem bijOn_aux98StripMap : BijOn aux98StripMap aux98Strip H := by
  refine ⟨fun z hz => aux98StripMap_mem_H hz, ?_, ?_⟩
  · intro z hz z' hz' h
    have := congrArg aux98StripMapInv h
    rwa [aux98StripMapInv_aux98StripMap hz, aux98StripMapInv_aux98StripMap hz'] at this
  · intro w hw
    have hw1 : w ≠ 1 := by
      intro h; have : (0 : ℝ) < w.im := hw; rw [h] at this; simp at this
    exact ⟨aux98StripMapInv w, aux98StripMapInv_mem hw, aux98StripMap_aux98StripMapInv hw1⟩

/-- `|F(z) − 1| = e^{−Re z}`. -/
theorem norm_aux98StripMap_sub_one (z : ℂ) : ‖aux98StripMap z - 1‖ = Real.exp (-z.re) := by
  simp [aux98StripMap, norm_exp]

/-- (Q1): the right strip end goes to the marked point `1`. -/
theorem tendsto_aux98StripMap_atTop :
    Tendsto aux98StripMap (comap re atTop) (𝓝 1) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  simp only [norm_aux98StripMap_sub_one]
  exact (Real.tendsto_exp_neg_atTop_nhds_zero).comp tendsto_comap

/-- (Q1): the left strip end goes to the original target `∞`. -/
theorem tendsto_norm_aux98StripMap_atBot :
    Tendsto (fun z => ‖aux98StripMap z‖) (comap re atBot) atTop := by
  have h1 : Tendsto (fun z : ℂ => Real.exp (-z.re) - 1) (comap re atBot) atTop := by
    have : Tendsto (fun z : ℂ => -z.re) (comap re atBot) atTop :=
      tendsto_neg_atBot_atTop.comp tendsto_comap
    exact tendsto_atTop_add_const_right _ (-1) (Real.tendsto_exp_atTop.comp this)
  refine tendsto_atTop_mono (fun z => ?_) h1
  have h := norm_sub_norm_le (exp (-z)) 1
  have : ‖exp (-z)‖ - ‖(1 : ℂ)‖ ≤ ‖aux98StripMap z‖ := by
    rw [aux98StripMap, norm_sub_rev]; exact norm_sub_norm_le _ _
  simpa [norm_exp] using this


/-! ### Claim 1: `coth(x/2) − 2/x` is bounded between zero and one -/

open Sec4 (cothHalf one_le_cothHalf cothHalf_sub_one)

/-- `coth(x/2) = 2/(1 − e^{−x}) − 1` (the identity used to verify (Q2b)). -/
theorem cothHalf_eq_two_div_one_sub_exp_neg {x : ℝ} (hx : x ≠ 0) :
    cothHalf x = 2 / (1 - Real.exp (-x)) - 1 := by
  have hE : Real.exp x ≠ 1 := by
    intro h; exact hx (Real.exp_eq_one_iff x |>.1 h)
  have h1 : Real.exp x - 1 ≠ 0 := sub_ne_zero.2 hE
  have hpos := Real.exp_pos x
  have h2 : 1 - (Real.exp x)⁻¹ ≠ 0 := by
    intro h; apply hE
    have : (Real.exp x)⁻¹ = 1 := by linarith
    exact inv_eq_one.1 this
  rw [cothHalf, Real.exp_neg]
  field_simp
  ring

/-- `x eˣ − eˣ + 1 > 0` for `x > 0` (its derivative is `x eˣ`). -/
theorem mul_exp_sub_exp_add_one_pos {x : ℝ} (hx : 0 < x) : 0 < x * Real.exp x - Real.exp x + 1 := by
  have hmono : StrictMonoOn (fun x : ℝ => x * Real.exp x - Real.exp x + 1) (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · fun_prop
    · intro y hy
      rw [interior_Ici] at hy
      have hd : HasDerivAt (fun x : ℝ => x * Real.exp x - Real.exp x + 1) (y * Real.exp y) y := by
        have := (((hasDerivAt_id' y).mul (Real.hasDerivAt_exp y)).sub (Real.hasDerivAt_exp y)).add_const 1
        exact this.congr_deriv (by ring)
      rw [hd.deriv]
      exact mul_pos hy (Real.exp_pos y)
  have := hmono self_mem_Ici (mem_Ici.2 hx.le) hx
  simpa using this

/-- `x (eˣ + 1) − 2 (eˣ − 1) > 0` for `x > 0` (its derivative is `x eˣ − eˣ + 1 > 0`). -/
theorem two_mul_exp_sub_one_lt {x : ℝ} (hx : 0 < x) : 2 * (Real.exp x - 1) < x * (Real.exp x + 1) := by
  have hmono : StrictMonoOn (fun x : ℝ => x * (Real.exp x + 1) - 2 * (Real.exp x - 1)) (Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
    · fun_prop
    · intro y hy
      rw [interior_Ici] at hy
      have hd : HasDerivAt (fun x : ℝ => x * (Real.exp x + 1) - 2 * (Real.exp x - 1))
          (y * Real.exp y - Real.exp y + 1) y := by
        have := ((hasDerivAt_id' y).mul ((Real.hasDerivAt_exp y).add_const 1)).sub
          (((Real.hasDerivAt_exp y).sub_const 1).const_mul 2)
        exact this.congr_deriv (by ring)
      rw [hd.deriv]
      exact mul_exp_sub_exp_add_one_pos hy
  have := hmono self_mem_Ici (mem_Ici.2 hx.le) hx
  simp at this
  linarith

/-- Claim 1 of Aux. lemma 98: `coth(x/2) − 2/x > 0` for `x > 0`. -/
theorem cothHalf_sub_two_div_pos {x : ℝ} (hx : 0 < x) : 0 < cothHalf x - 2 / x := by
  have hE : 1 < Real.exp x := Real.one_lt_exp_iff.2 hx
  rw [sub_pos, cothHalf, div_lt_div_iff₀ hx (by linarith)]
  linarith [two_mul_exp_sub_one_lt hx]

/-- Claim 1 of Aux. lemma 98: `coth(x/2) − 2/x < 1` for `x > 0`. -/
theorem cothHalf_sub_two_div_lt_one {x : ℝ} (hx : 0 < x) : cothHalf x - 2 / x < 1 := by
  have h1 := cothHalf_sub_one hx
  have h2 : x < Real.exp x - 1 := by linarith [Real.add_one_lt_exp hx.ne']
  have h3 : 2 / (Real.exp x - 1) < 2 / x := div_lt_div_of_pos_left (by norm_num) hx h2
  linarith

/-! ### (Q2): the parameters `A`, `σ`, `μ` and the Bessel comparison -/

/-- `A = 1 + r/2` of (Q2). -/
def aux98A (r : ℝ) : ℝ := 1 + r / 2

/-- `σ = (κ − 6 − r − 2ρ^{2,R})/2` of (Q2). -/
def aux98Sigma (κ r ρ : ℝ) : ℝ := (κ - 6 - r - 2 * ρ) / 2

/-- `μ = σ − r/2` of (Q4). -/
def aux98Mu (κ r ρ : ℝ) : ℝ := aux98Sigma κ r ρ - r / 2

theorem aux98A_pos {r : ℝ} (hr : -2 < r) : 0 < aux98A r := by
  unfold aux98A; linarith

/-- (Q1)–(Q2): the strip-end weights `ρ₊ = ρ^{2,R}` and `ρ₋ = κ − 6 − S` together with the seed weight `r` have
total `κ − 6`. -/
theorem aux98_strip_weights (κ r ρ : ℝ) : r + ρ + (κ - 6 - (r + ρ)) = κ - 6 := by ring

/-- Claim 2: `A − σ = S − d` with `S = r + ρ^{2,R}` and `d = κ/2 − 4`. -/
theorem aux98A_sub_aux98Sigma (κ r ρ : ℝ) : aux98A r - aux98Sigma κ r ρ = (r + ρ) - (κ / 2 - 4) := by
  unfold aux98A aux98Sigma; ring

/-- (Q4): `μ = σ − r/2 = κ/2 − 3 − S`. -/
theorem aux98Mu_eq (κ r ρ : ℝ) : aux98Mu κ r ρ = κ / 2 - 3 - (r + ρ) := by
  unfold aux98Mu aux98Sigma; ring

/-- (Q4): `μ < 1`, using `S > −2` and `κ < 4`. -/
theorem aux98Mu_lt_one {κ r ρ : ℝ} (hκ : κ < 4) (hS : -2 < r + ρ) : aux98Mu κ r ρ < 1 := by
  rw [aux98Mu_eq]; linarith

/-- For `0 < κ < 4` and `S > −2`, `S − d > 0` (`d = κ/2 − 4 < −2`): the linear rate of Claim 2 is positive. -/
theorem aux98_S_sub_d_pos {κ S : ℝ} (hκ : κ < 4) (hS : -2 < S) : 0 < S - (κ / 2 - 4) := by linarith

/-- Claim 1: after the scaling `X/√κ`, the singular part `2A/X` of the gap drift is the Bessel drift
`(δ − 1)/(2 · X/√κ)` of dimension `δ = 1 + 2(r + 2)/κ`: `2A/κ = (δ − 1)/2`. -/
theorem aux98_bessel_dimension {κ : ℝ} (hκ : 0 < κ) (r : ℝ) :
    2 * aux98A r / κ = ((1 + 2 * (r + 2) / κ) - 1) / 2 := by
  unfold aux98A; field_simp; ring

/-- Claim 1: the Bessel dimension `1 + 2(r + 2)/κ` exceeds one when `r > −2`. -/
theorem one_lt_aux98_bessel_dimension {κ r : ℝ} (hκ : 0 < κ) (hr : -2 < r) : 1 < 1 + 2 * (r + 2) / κ := by
  have : 0 < 2 * (r + 2) / κ := div_pos (by linarith) hκ
  linarith

/-- Claim 1: the gap drift `A coth(X/2) − σ` is the Bessel drift `2A/X − σ` plus a term in `[0, A]`. -/
theorem aux98_gapDrift_split {A σ x : ℝ} (hx : 0 < x) (hA : 0 ≤ A) :
    A * cothHalf x - σ = 2 * A / x - σ + A * (cothHalf x - 2 / x) ∧
      0 ≤ A * (cothHalf x - 2 / x) ∧ A * (cothHalf x - 2 / x) ≤ A := by
  refine ⟨by ring, mul_nonneg hA (cothHalf_sub_two_div_pos hx).le, ?_⟩
  calc A * (cothHalf x - 2 / x) ≤ A * 1 :=
        mul_le_mul_of_nonneg_left (cothHalf_sub_two_div_lt_one hx).le hA
    _ = A := mul_one A

/-- (Q4): the driver drift splits as the constant `μ` plus the error `e = −(r/2)(coth(X/2) − 1)`. -/
theorem aux98_driver_drift_split (κ r ρ x : ℝ) :
    aux98Sigma κ r ρ - r / 2 * cothHalf x = aux98Mu κ r ρ + -(r / 2) * (cothHalf x - 1) := by
  unfold aux98Mu; ring


/-! ### (Q2a)–(Q2b): the chordal coordinates and their equations in the clock `ϑ`

Here `Y_t = e^{−t−ξ_t}`, `Ŵ = p_t − Y_t`, `V̂¹ = p_t − e^{−t−V_t}`, `V̂² = p_t`, where `p_t = 1 + 2∫₀ᵗ Y`
(so `p' = 2Y`), and the clock is `dϑ = Y² dt`. The statements are pointwise in `t`: `ξ` enters only through
its value at `t`. -/

/-- (Q2b): the first chordal gap is `V̂¹ − Ŵ = Y (1 − e^{−X})`, `X = V − ξ`. -/
theorem aux98_gap_one (p t ξ V : ℝ) :
    (p - Real.exp (-t - V)) - (p - Real.exp (-t - ξ)) = Real.exp (-t - ξ) * (1 - Real.exp (-(V - ξ))) := by
  rw [mul_sub, mul_one, ← Real.exp_add]
  ring_nf

/-- (Q2b): the second chordal gap is `V̂² − Ŵ = Y`; in particular the separated mark is never swallowed at a
finite strip time. -/
theorem aux98_gap_two (p t ξ : ℝ) : p - (p - Real.exp (-t - ξ)) = Real.exp (-t - ξ) := by ring

theorem one_sub_exp_neg_pos {x : ℝ} (hx : 0 < x) : 0 < 1 - Real.exp (-x) := by
  have : Real.exp (-x) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  linarith

/-- (Q2b), the driving equation: Itô's formula gives `dŴ = Y √κ dB + Y (3 − κ/2 + σ − (r/2) coth(X/2)) dt`
(from `dY = Y(−dt − dξ + (κ/2) dt)` and (Q2)); in the clock `dϑ = Y² dt` its drift is the chordal force drift:
`(3 − κ/2 + σ − (r/2) coth(X/2)) = Y (r/(Ŵ − V̂¹) + ρ^{2,R}/(Ŵ − V̂²))` whenever `X = V − ξ > 0`. -/
theorem aux98_driver_drift_identity (κ r ρ p t ξ V : ℝ) (hX : 0 < V - ξ) :
    3 - κ / 2 + aux98Sigma κ r ρ - r / 2 * cothHalf (V - ξ) =
      Real.exp (-t - ξ) * (r / ((p - Real.exp (-t - ξ)) - (p - Real.exp (-t - V))) +
        ρ / ((p - Real.exp (-t - ξ)) - p)) := by
  have hg1 : (p - Real.exp (-t - ξ)) - (p - Real.exp (-t - V)) =
      -(Real.exp (-t - ξ) * (1 - Real.exp (-(V - ξ)))) := by
    rw [← aux98_gap_one p t ξ V]; ring
  have hg2 : (p - Real.exp (-t - ξ)) - p = -Real.exp (-t - ξ) := by ring
  have hY := Real.exp_pos (-t - ξ)
  have hE := one_sub_exp_neg_pos hX
  rw [hg1, hg2, cothHalf_eq_two_div_one_sub_exp_neg hX.ne', aux98Sigma]
  field_simp
  ring

/-- (Q2b), the first force coordinate: if `dV/dt = coth(X/2)` at `t` (a non-collision time, `X_t > 0`) and
`p' = 2Y`, then `V̂¹ = p − e^{−t−V}` satisfies `dV̂¹/dt = Y² · 2/(V̂¹ − Ŵ)`, i.e. the chordal Loewner equation
`dV̂¹ = 2/(V̂¹ − Ŵ) dϑ`. -/
theorem hasDerivAt_aux98V1 {p V : ℝ → ℝ} {t ξ : ℝ} (hp : HasDerivAt p (2 * Real.exp (-t - ξ)) t)
    (hV : HasDerivAt V (cothHalf (V t - ξ)) t) (hX : 0 < V t - ξ) :
    HasDerivAt (fun s => p s - Real.exp (-s - V s))
      (Real.exp (-t - ξ) ^ 2 *
        (2 / ((p t - Real.exp (-t - V t)) - (p t - Real.exp (-t - ξ))))) t := by
  have hf : HasDerivAt (fun s => -s - V s) (-1 - cothHalf (V t - ξ)) t :=
    (hasDerivAt_id' t).neg.sub hV
  have h := hp.sub hf.exp
  refine h.congr_deriv ?_
  rw [aux98_gap_one, cothHalf_eq_two_div_one_sub_exp_neg hX.ne']
  have hsplit : Real.exp (-t - V t) = Real.exp (-t - ξ) * Real.exp (-(V t - ξ)) := by
    rw [← Real.exp_add]; ring_nf
  rw [hsplit]
  have hY := Real.exp_pos (-t - ξ)
  have hE := one_sub_exp_neg_pos hX
  field_simp
  ring

/-- (Q2b), the separated mark: `V̂² = p` satisfies `dV̂²/dt = 2Y = Y² · 2/(V̂² − Ŵ)`. -/
theorem hasDerivAt_aux98V2 {p : ℝ → ℝ} {t ξ : ℝ} (hp : HasDerivAt p (2 * Real.exp (-t - ξ)) t) :
    HasDerivAt p (Real.exp (-t - ξ) ^ 2 * (2 / (p t - (p t - Real.exp (-t - ξ))))) t := by
  refine hp.congr_deriv ?_
  have hY := (Real.exp_pos (-t - ξ)).ne'
  rw [aux98_gap_two]
  field_simp

/-- The clock `ϑ(t) = ∫₀ᵗ Y_s² ds` is strictly increasing (`Y > 0`): `ϑ' = Y² > 0`. -/
theorem aux98_clock_deriv_pos (t ξ : ℝ) : 0 < Real.exp (-t - ξ) ^ 2 := by positivity

/-! ### (Q2c): the hull coordinate -/

/-- `coth(w/2) = (e^{w} + 1)/(e^{w} − 1)` for complex `w`, written with `u = e^{w/2}`. -/
theorem cosh_div_sinh_eq (w : ℂ) (hs : sinh w ≠ 0) :
    cosh w / sinh w = (exp w ^ 2 + 1) / (exp w ^ 2 - 1) := by
  have hu : exp w ≠ 0 := exp_ne_zero w
  have hsinh : sinh w = (exp w - (exp w)⁻¹) / 2 := by
    rw [← exp_neg, sinh]
  have hcosh : cosh w = (exp w + (exp w)⁻¹) / 2 := by
    rw [← exp_neg, cosh]
  have h2 : exp w ^ 2 - 1 ≠ 0 := by
    intro h; apply hs; rw [hsinh]
    have : exp w - (exp w)⁻¹ = (exp w ^ 2 - 1) / exp w := by field_simp
    rw [this, h]; simp
  rw [hcosh, hsinh]
  field_simp

/-- (Q2c) at one time: with `a = e^{−t−z}` (`= F_t'(z)`), `Y = e^{−t−ξ}` and `∂_t F_t(z) = p' + a = 2Y + a`,
`∂_t F_t(z) + F_t'(z) coth((z − ξ)/2) = 2Y²/(F_t(z) − Ŵ)`, where `F_t(z) = p − e^{−t−z}` and `Ŵ = p − Y`. -/
theorem aux98_Q2c (p t ξ : ℝ) (z : ℂ) (hs : sinh ((z - ξ) / 2) ≠ 0)
    (ha : exp (-t - z) ≠ (Real.exp (-t - ξ) : ℂ)) :
    (2 * (Real.exp (-t - ξ) : ℂ) + exp (-t - z)) +
        exp (-t - z) * (cosh ((z - ξ) / 2) / sinh ((z - ξ) / 2)) =
      2 * (Real.exp (-t - ξ) : ℂ) ^ 2 / (((p : ℂ) - exp (-t - z)) - ((p : ℂ) - Real.exp (-t - ξ))) := by
  rw [cosh_div_sinh_eq _ hs]
  set u := exp ((z - ξ) / 2) with hu_def
  have hu2 : u ^ 2 = exp (z - ξ) := by
    rw [hu_def, ← exp_nat_mul]; congr 1; push_cast; ring
  have hY : (Real.exp (-t - ξ) : ℂ) = exp (-t - z) * u ^ 2 := by
    rw [hu2, ← exp_add, ofReal_exp]; congr 1; push_cast; ring
  set a := exp (-t - z) with ha_def
  have ha0 : a ≠ 0 := exp_ne_zero _
  have hu1 : u ^ 2 - 1 ≠ 0 := by
    intro h; apply ha; rw [hY]
    have : u ^ 2 = 1 := by linear_combination h
    rw [this, mul_one]
  rw [hY]
  have hden : ((p : ℂ) - a) - ((p : ℂ) - a * u ^ 2) = a * (u ^ 2 - 1) := by ring
  rw [hden]
  field_simp
  ring

/-- (Q2c) with the strip Loewner equation `∂_t ψ_t(z) = coth((ψ_t(z) − ξ_t)/2)`: the composite
`F_t(ψ_t(z)) = p_t − e^{−t−ψ_t(z)}` satisfies `∂_t F_t(ψ_t(z)) = Y² · 2/(F_t(ψ_t(z)) − Ŵ)`, i.e. the chordal
Loewner equation in the clock `dϑ = Y² dt`; uniqueness of the deterministic Loewner equation then identifies
`ĝ_{ϑ(t)} ∘ F = F_t ∘ ψ_t`. -/
theorem hasDerivAt_aux98Ft_comp {p : ℝ → ℝ} {ψ : ℝ → ℂ} {t ξ : ℝ}
    (hp : HasDerivAt p (2 * Real.exp (-t - ξ)) t)
    (hψ : HasDerivAt ψ (cosh ((ψ t - ξ) / 2) / sinh ((ψ t - ξ) / 2)) t)
    (hs : sinh ((ψ t - ξ) / 2) ≠ 0) (ha : exp (-t - ψ t) ≠ (Real.exp (-t - ξ) : ℂ)) :
    HasDerivAt (fun s => (p s : ℂ) - exp (-s - ψ s))
      ((Real.exp (-t - ξ) : ℂ) ^ 2 *
        (2 / (((p t : ℂ) - exp (-t - ψ t)) - ((p t : ℂ) - Real.exp (-t - ξ))))) t := by
  have hpc : HasDerivAt (fun s => (p s : ℂ)) ((2 * Real.exp (-t - ξ) : ℝ) : ℂ) t := hp.ofReal_comp
  have hf : HasDerivAt (fun s : ℝ => -(s : ℂ) - ψ s)
      (-1 - cosh ((ψ t - ξ) / 2) / sinh ((ψ t - ξ) / 2)) t := by
    have h1 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 t := by
      simpa using (hasDerivAt_id' t).ofReal_comp
    exact h1.neg.sub hψ
  have h := hpc.sub hf.cexp
  refine h.congr_deriv ?_
  have key := aux98_Q2c (p t) t ξ (ψ t) hs ha
  have e : ∀ x y : ℂ, x ^ 2 * (2 / y) = 2 * x ^ 2 / y := fun x y => by ring
  rw [e, ← key]
  push_cast
  ring

/-! ### Claim 2: linear separation and the tail energy of the drift error -/

/-- (Q3), pathwise: if `X_t = −√κ b_t + ∫₀ᵗ (A coth(X_s/2) − σ) ds` with `A ≥ 0` and `X > 0` almost everywhere on
`[0, t]` (the collision set is Lebesgue-null), then `X_t ≥ −√κ b_t + (A − σ) t`. -/
theorem aux98_Q3 {κ A σ t : ℝ} {X b : ℝ → ℝ} (hA : 0 ≤ A) (ht : 0 ≤ t)
    (hint : IntervalIntegrable (fun s => A * cothHalf (X s) - σ) volume 0 t)
    (hpos : ∀ᵐ s ∂(volume.restrict (Icc 0 t)), 0 < X s)
    (heq : X t = -(Real.sqrt κ * b t) + ∫ s in (0 : ℝ)..t, (A * cothHalf (X s) - σ)) :
    -(Real.sqrt κ * b t) + (A - σ) * t ≤ X t := by
  have hmono : (∫ _ in (0 : ℝ)..t, (A - σ)) ≤ ∫ s in (0 : ℝ)..t, (A * cothHalf (X s) - σ) := by
    apply intervalIntegral.integral_mono_ae_restrict ht intervalIntegrable_const hint
    filter_upwards [hpos] with s hs
    have := one_le_cothHalf hs
    have : A * 1 ≤ A * cothHalf (X s) := mul_le_mul_of_nonneg_left this hA
    linarith
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hmono
  rw [heq]
  linarith

/-- Claim 2: from (Q3) with rate `c = S − d > 0` and the Brownian strong law `b_t/t → 0`, eventually
`X_t ≥ c t / 2`. -/
theorem aux98_eventually_linear {κ c : ℝ} {X b : ℝ → ℝ} (hc : 0 < c)
    (hb : Tendsto (fun t => b t / t) atTop (𝓝 0))
    (hX : ∀ t, 0 ≤ t → -(Real.sqrt κ * b t) + c * t ≤ X t) :
    ∃ T, ∀ t, T ≤ t → c / 2 * t ≤ X t := by
  set ε := c / (2 * (Real.sqrt κ + 1)) with hε
  have hs := Real.sqrt_nonneg κ
  have hεpos : 0 < ε := div_pos hc (by positivity)
  obtain ⟨T, hT⟩ := (Metric.tendsto_atTop.1 hb) ε hεpos
  refine ⟨max T 1, fun t ht => ?_⟩
  have ht1 : 1 ≤ t := (le_max_right _ _).trans ht
  have htT : T ≤ t := (le_max_left _ _).trans ht
  have htpos : 0 < t := by linarith
  have h1 := hT t htT
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos htpos, div_lt_iff₀ htpos] at h1
  have h2 : Real.sqrt κ * b t ≤ Real.sqrt κ * (ε * t) :=
    mul_le_mul_of_nonneg_left ((le_abs_self _).trans h1.le) hs
  have h3 : Real.sqrt κ * ε ≤ c / 2 := by
    rw [hε, mul_div_assoc']
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have h4 : Real.sqrt κ * (ε * t) ≤ c / 2 * t := by
    rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right h3 htpos.le
  have := hX t htpos.le
  linarith

/-- (Q4): on a late tail the drift error `e_t = −(r/2)(coth(X_t/2) − 1)` has finite energy `∫ e_t² dt < ∞`
(exponential decay from Claim 2). The finite-energy computation is `Sec4.integrableOn_sq_correction`. -/
theorem aux98_integrableOn_sq_error {κ c r : ℝ} {X b : ℝ → ℝ} (hc : 0 < c) (hXm : Measurable X)
    (hb : Tendsto (fun t => b t / t) atTop (𝓝 0))
    (hX : ∀ t, 0 ≤ t → -(Real.sqrt κ * b t) + c * t ≤ X t) :
    ∃ T, IntegrableOn (fun t => (-(r / 2) * (cothHalf (X t) - 1)) ^ 2) (Ioi T) := by
  obtain ⟨T, hT⟩ := aux98_eventually_linear hc hb hX
  exact ⟨_, Sec4.integrableOn_sq_correction (half_pos hc) hXm hT⟩

end Sec7

end InteractingSLE
