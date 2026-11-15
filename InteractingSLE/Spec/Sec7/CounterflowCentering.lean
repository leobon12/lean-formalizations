/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec4.CounterflowHeights

/-!
# §7.4, Aux. lemma 118: counterflow centering and the strip-to-half-plane word

Packet PROVE-SEC7-D (specification §7.4, `source/spec/p337-384.md` L941–L985, pp. 383–384; supplement §4 opening,
`source/spec/p433-480.md` L744–L752).

Fix `0 < κ < 4`, `κ' = 16/κ`, `χ = chiC κ`, `λ = sleLambda κ`, `λ' = sleLambda κ'`. The `κ'` coupling is applied to the
field `F_c = −h + c`; `c = 0` is the literal half-plane convention of Theorem 1.1 and `c = −πχ` the centred frame of the
frozen `IsCenteredCounterflowDriver`. On the strip `𝒮 = {0 < Im z < 1}`, with `q > 0` and `z_* = (log q)/π + i`, the map
`P(z) = −(e^{πz} + q)/(e^{πz} − 1)` with lift `L_P(z) = log(π(q + 1)) + πz − 2 Log(e^{πz} − 1)` (CF9.1) is
`DerivLog.stripToH q` / `DerivLog.derivLogStripToH q` (FD11.5; `isDerivLog_stripToH`, `mapsTo_stripToH` are reused).

* **The map (CF9.1).** `stripToH_eqOn_comp` (`P = M_q ∘ E` with Sec4's `M_q` and `E(z) = e^{πz} − 1`),
  `bijOn_stripToH`, `isConformalBijection_stripToH`, the explicit inverse `stripToHInv` (`leftInvOn_stripToHInv`,
  `rightInvOn_stripToHInv`, `invFunOn_stripToH_eqOn`), the marks `stripToH_stripSeed` (`P(z_*) = 0`) and
  `tendsto_stripToH_cobounded` (`P → ∞` at `0`), and the exact inverse branch `L_{P⁻¹} = −L_P ∘ P⁻¹`
  (`isDerivLog_stripToHInv`).
* **Boundary values.** `P` sends the lower-left line to `(q, ∞)`, the lower-right line to `(−∞, −1)`, the upper line
  left of `z_*` to `(0, q)` and right of `z_*` to `(−1, 0)` (`stripToH_lower_of_neg`, …); `Im L_P` is `−2π`, `0`, `−π`
  there (`im_derivLogStripToH_lower_of_neg`, `…_lower_of_pos`, `…_upper`), and these are boundary limits from inside
  (`continuousWithinAt_im_derivLogStripToH`).
* **(CF9.2)–(CF9.4).** The strip word `cf92Lower`, `cf92Upper`; the `κ'` coordinate field `F_c^P = −h ∘ P⁻¹ − χ Im L_P ∘
  P⁻¹ + c` (CF9.3) has on `ℝ` the heights `cf94Heights` (`cf94Heights_stripToH_lower`, `cf94Heights_stripToH_upper`).
* **Centering and (CF9.5).** `cf94_driver_heights_iff` (the driver-side heights are `∓λ'` iff `c = −πχ`), the weights
  `cf95RhoL`, `cf95RhoR` with `cf95_left_height`, `cf95_right_height`, the uniqueness forms `cf95RhoL_eq_iff`,
  `cf95RhoR_eq_iff`, and the two conversions `sleLambda_div_sleLambda_sixteen_div` (`λ/λ' = κ'/4`) and
  `pi_mul_chiC_div_sleLambda_sixteen_div` (`πχ/λ' = κ'/2 − 2`).
* **The constant is a field choice.** `exists_int_im_eq_of_isDerivLog_stripToH` (another lift changes the field by one
  constant `−2πnχ`), `two_pi_mul_int_mul_chiC_ne_pi_mul_chiC` (it can never produce `−πχ`).
* **(CF9.6).** `coordChange_neg_add_const` (`T^{κ'}_ψ(F_c) = −T^κ_ψ(h) + c` for functions; composition along the chain
  rule lift is `coordChange_coordChange`). The distribution form is not stated: the frozen `IsChartTransport` (v1)
  parses its lift integral inside the first integral (the R28 pitfall; PROVE-SEC7-D handoff §0).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology
open scoped Real
open QuantumZipper (H chiC)

namespace InteractingSLE

namespace Sec7

open DerivLog

/-! ### The map `P` of (CF9.1) -/

/-- The strip `𝒮 = {0 < Im z < 1}` (the same set as `InteractingSLE.strip`, in the form used by `DerivLog`). -/
theorem strip_eq : strip = {z : ℂ | 0 < z.im ∧ z.im < 1} := rfl

/-- The upper marked point `z_* = (log q)/π + i` of Aux. lemma 118. -/
def stripSeed (q : ℝ) : ℂ := ((Real.log q / π : ℝ) : ℂ) + I

/-- The explicit inverse of `P`: `P⁻¹(w) = Log((w − q)/(w + 1))/π`. -/
def stripToHInv (q : ℝ) (w : ℂ) : ℂ := log ((w - q) / (w + 1)) / π

variable {q : ℝ}

theorem exp_pi_mul_ne_one_of_mem_strip {z : ℂ} (hz : z ∈ strip) : exp ((π : ℂ) * z) - 1 ≠ 0 :=
  ne_zero_of_mem_H (sub_one_mem_H (exp_pi_mul_mem_H hz))

/-- `P = M_q ∘ E` off the pole, with `E(z) = e^{πz} − 1` and `M_q(w) = −1 − (1 + q)/w` (Sec4's
`stripCounterflowChart`). -/
theorem stripToH_eq_comp {z : ℂ} (hz : Sec4.expChart z ≠ 0) :
    stripToH q z = (Sec4.stripCounterflowChart q).1 (Sec4.expChart z) := by
  rw [Sec4.stripCounterflowChart_fwd, stripToH]
  simp only [Sec4.expChart] at hz ⊢
  field_simp
  ring

theorem stripToH_eqOn_comp :
    EqOn (stripToH q) ((Sec4.stripCounterflowChart q).1 ∘ Sec4.expChart) strip := fun _ hz =>
  stripToH_eq_comp (exp_pi_mul_ne_one_of_mem_strip hz)

/-- `M_q` is a bijection of `ℍ`. -/
theorem bijOn_stripCounterflowChart (hq : 0 < q) : BijOn (Sec4.stripCounterflowChart q).1 H H := by
  refine ⟨fun w hw => Sec4.stripCounterflowChart_fwd_mem_H hq hw, ?_, fun w hw => ?_⟩
  · intro w₁ hw₁ w₂ hw₂ h
    rw [← Sec4.stripCounterflowChart_inv_fwd hq (ne_zero_of_mem_H hw₁),
      ← Sec4.stripCounterflowChart_inv_fwd hq (ne_zero_of_mem_H hw₂), h]
  · have hw1 : w ≠ -1 := fun h => by
      have : (0 : ℝ) < w.im := hw
      rw [h] at this; simp at this
    exact ⟨_, Sec4.stripCounterflowChart_inv_mem_H hq hw, Sec4.stripCounterflowChart_fwd_inv hq hw1⟩

/-- (CF9.1): `P` maps the strip bijectively onto `ℍ`. -/
theorem bijOn_stripToH (hq : 0 < q) : BijOn (stripToH q) strip H :=
  ((bijOn_stripCounterflowChart hq).comp Sec4.bijOn_expChart).congr stripToH_eqOn_comp.symm

theorem differentiableOn_stripToH : DifferentiableOn ℂ (stripToH q) strip := by
  intro z hz
  have hE := hasDerivAt_exp_pi_mul z
  exact ((((hE.add_const (q : ℂ)).neg).div (hE.sub_const 1)
    (exp_pi_mul_ne_one_of_mem_strip hz)).differentiableAt).differentiableWithinAt

/-- (CF9.1): `P` is a conformal bijection of the strip onto `ℍ`. -/
theorem isConformalBijection_stripToH (hq : 0 < q) :
    SupercriticalConformalCovariance.IsConformalBijection (stripToH q) strip H :=
  ⟨differentiableOn_stripToH, bijOn_stripToH hq⟩

theorem div_add_one_mem_H (hq : 0 < q) {w : ℂ} (hw : w ∈ H) : (w - q) / (w + 1) ∈ H := by
  have := Sec4.div_add_mem_H hw (show -q < (1 : ℝ) by linarith)
  simpa [sub_eq_add_neg] using this

theorem stripToHInv_mem_strip (hq : 0 < q) {w : ℂ} (hw : w ∈ H) : stripToHInv q w ∈ strip := by
  have ha := arg_mem_Ioo_of_mem_H (div_add_one_mem_H hq hw)
  have hπ := Real.pi_pos
  simp only [strip, stripToHInv, mem_ofPred_eq, div_ofReal_im, log_im]
  exact ⟨div_pos ha.1 hπ, (div_lt_one hπ).2 ha.2⟩

theorem exp_pi_mul_stripToHInv (hq : 0 < q) {w : ℂ} (hw : w ∈ H) :
    exp ((π : ℂ) * stripToHInv q w) = (w - q) / (w + 1) := by
  rw [stripToHInv, mul_div_cancel₀ _ (ofReal_ne_zero.2 Real.pi_pos.ne'),
    exp_log (ne_zero_of_mem_H (div_add_one_mem_H hq hw))]

theorem rightInvOn_stripToHInv (hq : 0 < q) : RightInvOn (stripToHInv q) (stripToH q) H := by
  intro w hw
  have hw1 : w + 1 ≠ 0 := ne_zero_of_mem_H (by simpa using add_ofReal_mem_H hw 1)
  have hq1 : (1 + q : ℂ) ≠ 0 := Sec4.one_add_ne_zero_of_pos hq
  have hq2 : (-1 - q : ℂ) ≠ 0 := by
    rw [show (-1 - q : ℂ) = -(1 + q) by ring]; exact neg_ne_zero.2 hq1
  show stripToH q (stripToHInv q w) = w
  have e1 : (w - q) / (w + 1) + q = w * (1 + q) / (w + 1) := by field_simp; ring
  have e2 : (w - q) / (w + 1) - 1 = -(1 + q) / (w + 1) := by field_simp; ring
  rw [stripToH, exp_pi_mul_stripToHInv hq hw, e1, e2,
    div_eq_iff (div_ne_zero (neg_ne_zero.2 hq1) hw1)]
  ring

theorem leftInvOn_stripToHInv (hq : 0 < q) : LeftInvOn (stripToHInv q) (stripToH q) strip := by
  intro z hz
  have hP := (bijOn_stripToH hq).mapsTo hz
  exact (bijOn_stripToH hq).injOn (stripToHInv_mem_strip hq hP) hz (rightInvOn_stripToHInv hq hP)

/-- `Function.invFunOn P 𝒮` is the explicit inverse on `ℍ`. -/
theorem invFunOn_stripToH_eqOn (hq : 0 < q) :
    EqOn (Function.invFunOn (stripToH q) strip) (stripToHInv q) H := by
  intro w hw
  have hb := bijOn_stripToH hq
  have hmem := Function.invFunOn_mem (hb.surjOn hw)
  have heq := Function.invFunOn_eq (hb.surjOn hw)
  exact hb.injOn hmem (stripToHInv_mem_strip hq hw) (by rw [heq, rightInvOn_stripToHInv hq hw])

theorem image_stripToHInv (hq : 0 < q) : stripToHInv q '' H = strip := by
  refine Subset.antisymm (image_subset_iff.2 fun w hw => stripToHInv_mem_strip hq hw) fun z hz =>
    ⟨stripToH q z, (bijOn_stripToH hq).mapsTo hz, leftInvOn_stripToHInv hq hz⟩

/-- (CF9.1): `P(z_*) = 0`, since `e^{π z_*} = −q`. -/
theorem stripToH_stripSeed (hq : 0 < q) : stripToH q (stripSeed q) = 0 := by
  have he : exp ((π : ℂ) * stripSeed q) = -(q : ℂ) := by
    rw [stripSeed, mul_add, exp_add, exp_pi_mul_I, ← ofReal_mul,
      mul_div_cancel₀ _ Real.pi_pos.ne', ← ofReal_exp, Real.exp_log hq]
    ring
  rw [stripToH, he]
  simp

theorem im_stripSeed (q : ℝ) : (stripSeed q).im = 1 := by simp [stripSeed]

/-- Near `0` (punctured) the denominator `e^{πz} − 1` of `P` does not vanish. -/
theorem eventually_exp_pi_mul_sub_one_ne_zero :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ), exp ((π : ℂ) * z) - 1 ≠ 0 := by
  have hball : ∀ᶠ z in 𝓝[≠] (0 : ℂ), ‖z‖ < 2 :=
    nhdsWithin_le_nhds (Metric.ball_mem_nhds 0 (by norm_num : (0 : ℝ) < 2) |>
      Filter.mem_of_superset <| fun z hz => by simpa using hz)
  filter_upwards [hball, self_mem_nhdsWithin] with z hz hz0
  intro h
  obtain ⟨n, hn⟩ := exp_eq_one_iff.1 (sub_eq_zero.1 h)
  have hz' : z = n * (2 * I) := by
    have hπ : (π : ℂ) ≠ 0 := ofReal_ne_zero.2 Real.pi_pos.ne'
    apply mul_left_cancel₀ hπ
    rw [hn]; ring
  have hn0 : n ≠ 0 := by
    rintro rfl; simp at hz'; exact hz0 hz'
  have : ‖z‖ = 2 * |(n : ℝ)| := by
    rw [hz', norm_mul, norm_mul, norm_I, Complex.norm_intCast]; norm_num; ring
  have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn0
  linarith

/-- (CF9.1): `P` sends the strip point `0` to `∞`. -/
theorem tendsto_stripToH_cobounded (hq : 0 < q) :
    Tendsto (stripToH q) (𝓝[≠] 0) (Bornology.cobounded ℂ) := by
  rw [← tendsto_norm_atTop_iff_cobounded]
  have hc : Continuous fun z : ℂ => exp ((π : ℂ) * z) := by fun_prop
  have hlim : ‖-((1 : ℂ) + q)‖ = 1 + q := by
    rw [norm_neg, ← ofReal_one, ← ofReal_add, norm_real, Real.norm_of_nonneg (by linarith)]
  have h0 : Tendsto (fun z : ℂ => -(exp ((π : ℂ) * z) + q)) (𝓝 0) (𝓝 (-((1 : ℂ) + q))) := by
    have hcont : Continuous fun z : ℂ => -(exp ((π : ℂ) * z) + q) := by fun_prop
    simpa only [mul_zero, exp_zero] using hcont.tendsto 0
  have hnum := h0.norm.mono_left (nhdsWithin_le_nhds (s := {(0 : ℂ)}ᶜ))
  rw [hlim] at hnum
  have hden : Tendsto (fun z : ℂ => exp ((π : ℂ) * z) - 1) (𝓝[≠] 0) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, eventually_exp_pi_mul_sub_one_ne_zero⟩
    have : Tendsto (fun z : ℂ => exp ((π : ℂ) * z) - 1) (𝓝 0) (𝓝 (exp ((π : ℂ) * 0) - 1)) :=
      ((hc.sub continuous_const)).tendsto 0
    simpa using this.mono_left nhdsWithin_le_nhds
  have hinv := (tendsto_norm_atTop_iff_cobounded.2 tendsto_inv₀_nhdsNE_zero).comp hden
  refine (Tendsto.pos_mul_atTop (by linarith) hnum hinv).congr fun z => ?_
  simp only [Function.comp_apply, stripToH, div_eq_mul_inv, norm_mul]

/-- **The exact inverse branch** (Aux. lemma 118): `L_{P⁻¹} = −L_P ∘ P⁻¹` is a derivative lift of `P⁻¹` on `ℍ`. -/
theorem isDerivLog_stripToHInv (hq : 0 < q) :
    IsDerivLog (stripToHInv q) (fun w => -derivLogStripToH q (stripToHInv q w)) H := by
  have hD : IsOpen strip := isOpen_strip
  have h := (isDerivLog_stripToH hq).invFunOn hD (isConformalBijection_stripToH hq)
  have hEq := invFunOn_stripToH_eqOn hq
  have hHo : IsOpen H := QuantumZipper.isOpen_H
  refine ⟨h.1.congr fun w hw => by rw [hEq hw], fun w hw => ?_⟩
  have hev : Function.invFunOn (stripToH q) strip =ᶠ[𝓝 w] stripToHInv q :=
    Filter.eventuallyEq_of_mem (hHo.mem_nhds hw) hEq
  rw [← hev.deriv_eq, ← h.2 w hw]
  simp only [hEq hw]

/-- The chart `(P, P⁻¹, Im L_P)` of Aux. lemma 118, in the frozen `Chart` format; the `κ'` coordinate field (CF9.3)
of `F_c = −h + c` is meant to be its transport `IsChartTransport (aux118Chart q) (−1) c (chiC (16/κ)) h h'`, since
`χ(κ') = −χ` (`Sec4.chiC_sixteen_div`), once that frozen relation is parenthesized correctly (PROVE-SEC7-D handoff §0).
Its exploration domain is the strip (`aux118Chart_inv_image`). -/
def aux118Chart (q : ℝ) : Chart :=
  (stripToH q, stripToHInv q, fun z => (derivLogStripToH q z).im)

theorem aux118Chart_inv_image (hq : 0 < q) : (aux118Chart q).2.1 '' H = strip := image_stripToHInv hq

/-! ### Boundary values of `P` and of `Im L_P` -/

/-- `e^{πx} < q` iff `x < Re z_* = (log q)/π`. -/
theorem exp_pi_mul_lt_iff (hq : 0 < q) {x : ℝ} : Real.exp (π * x) < q ↔ x < Real.log q / π := by
  rw [← Real.lt_log_iff_exp_lt hq, lt_div_iff₀ Real.pi_pos, mul_comm]

theorem lt_exp_pi_mul_iff (hq : 0 < q) {x : ℝ} : q < Real.exp (π * x) ↔ Real.log q / π < x := by
  rw [← Real.log_lt_iff_lt_exp hq, div_lt_iff₀ Real.pi_pos, mul_comm]

/-- `P` on the lower line: `P(x) = −(e^{πx} + q)/(e^{πx} − 1)`. -/
theorem stripToH_ofReal (q x : ℝ) :
    stripToH q x = ((-(Real.exp (π * x) + q) / (Real.exp (π * x) - 1) : ℝ) : ℂ) := by
  rw [stripToH, Sec4.exp_pi_mul_ofReal]; push_cast; rfl

/-- `P` on the upper line: `P(x + i) = (q − e^{πx})/(e^{πx} + 1)`. -/
theorem stripToH_add_I (q x : ℝ) :
    stripToH q (x + I) = (((q - Real.exp (π * x)) / (Real.exp (π * x) + 1) : ℝ) : ℂ) := by
  have he := Real.exp_pos (π * x)
  have h1 : -((Real.exp (π * x) : ℝ) : ℂ) - 1 ≠ 0 := by
    rw [← ofReal_one, ← ofReal_neg, ← ofReal_sub]; exact ofReal_ne_zero.2 (by linarith)
  have h2 : ((Real.exp (π * x) : ℝ) : ℂ) + 1 ≠ 0 := by
    rw [← ofReal_one, ← ofReal_add]; exact ofReal_ne_zero.2 (by linarith)
  rw [stripToH, Sec4.exp_pi_mul_upper, ofReal_div, ofReal_sub, ofReal_add, ofReal_one,
    div_eq_div_iff h1 h2]
  ring

/-- The lower-left line `{x < 0}` goes into `(q, ∞)`. -/
theorem stripToH_lower_of_neg (hq : 0 < q) {x : ℝ} (hx : x < 0) :
    q < -(Real.exp (π * x) + q) / (Real.exp (π * x) - 1) := by
  have he := Real.exp_pos (π * x)
  have he1 : Real.exp (π * x) < 1 := Real.exp_lt_one_iff.2 (by nlinarith [Real.pi_pos])
  rw [lt_div_iff_of_neg (by linarith)]
  nlinarith

/-- The lower-right line `{x > 0}` goes into `(−∞, −1)`. -/
theorem stripToH_lower_of_pos (hq : 0 < q) {x : ℝ} (hx : 0 < x) :
    -(Real.exp (π * x) + q) / (Real.exp (π * x) - 1) < -1 := by
  have he1 : 1 < Real.exp (π * x) := Real.one_lt_exp_iff.2 (by nlinarith [Real.pi_pos])
  rw [div_lt_iff₀ (by linarith)]
  linarith

/-- The upper line left of `z_*` goes into `(0, q)`. -/
theorem stripToH_upper_of_lt (hq : 0 < q) {x : ℝ} (hx : x < Real.log q / π) :
    0 < (q - Real.exp (π * x)) / (Real.exp (π * x) + 1) ∧
      (q - Real.exp (π * x)) / (Real.exp (π * x) + 1) < q := by
  have he := Real.exp_pos (π * x)
  have hlt := (exp_pi_mul_lt_iff hq).2 hx
  refine ⟨div_pos (by linarith) (by linarith), ?_⟩
  rw [div_lt_iff₀ (by linarith)]
  nlinarith

/-- The upper line right of `z_*` goes into `(−1, 0)`. -/
theorem stripToH_upper_of_gt (hq : 0 < q) {x : ℝ} (hx : Real.log q / π < x) :
    -1 < (q - Real.exp (π * x)) / (Real.exp (π * x) + 1) ∧
      (q - Real.exp (π * x)) / (Real.exp (π * x) + 1) < 0 := by
  have he := Real.exp_pos (π * x)
  have hlt := (lt_exp_pi_mul_iff hq).2 hx
  refine ⟨?_, div_neg_of_neg_of_pos (by linarith) (by linarith)⟩
  rw [lt_div_iff₀ (by linarith)]
  linarith

theorem im_derivLogStripToH (q : ℝ) (z : ℂ) :
    (derivLogStripToH q z).im = π * z.im - 2 * arg (exp ((π : ℂ) * z) - 1) := by
  simp [derivLogStripToH, log_im]

/-- `Im L_P = −2π` on the lower-left line. -/
theorem im_derivLogStripToH_lower_of_neg {x : ℝ} (hx : x < 0) : (derivLogStripToH q x).im = -2 * π := by
  have he1 : Real.exp (π * x) < 1 := Real.exp_lt_one_iff.2 (by nlinarith [Real.pi_pos])
  rw [im_derivLogStripToH, Sec4.exp_pi_mul_ofReal, ← ofReal_one, ← ofReal_sub,
    arg_ofReal_of_neg (by linarith)]
  simp

/-- `Im L_P = 0` on the lower-right line. -/
theorem im_derivLogStripToH_lower_of_pos {x : ℝ} (hx : 0 < x) : (derivLogStripToH q x).im = 0 := by
  have he1 : 1 < Real.exp (π * x) := Real.one_lt_exp_iff.2 (by nlinarith [Real.pi_pos])
  rw [im_derivLogStripToH, Sec4.exp_pi_mul_ofReal, ← ofReal_one, ← ofReal_sub,
    arg_ofReal_of_nonneg (by linarith)]
  simp

/-- `Im L_P = −π` on the whole upper line. -/
theorem im_derivLogStripToH_upper (x : ℝ) : (derivLogStripToH q (x + I)).im = -π := by
  have he := Real.exp_pos (π * x)
  rw [im_derivLogStripToH, Sec4.exp_pi_mul_upper, Sec4.im_ofReal_add_I,
    show -((Real.exp (π * x) : ℝ) : ℂ) - 1 = ((-Real.exp (π * x) - 1 : ℝ) : ℂ) by push_cast; ring,
    arg_ofReal_of_neg (by linarith)]
  ring

/-- `Im L_P` is continuous on the closed strip off the pole `0`: its boundary values above are the boundary limits
from inside. -/
theorem continuousWithinAt_im_derivLogStripToH (q : ℝ) {z : ℂ} (hz : z ∈ closure strip)
    (hne : exp ((π : ℂ) * z) - 1 ≠ 0) :
    ContinuousWithinAt (fun w => (derivLogStripToH q w).im) (closure strip) z := by
  have h := Sec4.continuousWithinAt_arg_exp_add (c := -1) hz (by simpa [sub_eq_add_neg] using hne)
  simp only [ofReal_neg, ofReal_one, ← sub_eq_add_neg] at h
  simp only [im_derivLogStripToH]
  exact ((continuous_const.mul continuous_im).continuousWithinAt).sub (continuousWithinAt_const.mul h)

/-! ### (CF9.2)–(CF9.4): the strip word and the `κ'` coordinate heights -/

variable {κ θ₁ θ₂ c : ℝ}

/-- (CF9.2), lower line of the strip (an explicit input of Aux. lemma 118): the height of `h` is `λ − θ₂χ` on
`ℝ₋` and `−λ − θ₁χ` on `ℝ₊`. -/
def cf92Lower (κ θ₁ θ₂ : ℝ) (x : ℝ) : ℝ :=
  if x < 0 then sleLambda κ - θ₂ * chiC κ else -sleLambda κ - θ₁ * chiC κ

/-- (CF9.2), upper line `{x + i}`: the height of `h` is `−λ'` left of `Re z_* = (log q)/π` and `+λ'` right of it. -/
def cf92Upper (κ q : ℝ) (x : ℝ) : ℝ :=
  if x < Real.log q / π then -sleLambda (16 / κ) else sleLambda (16 / κ)

/-- (CF9.4): the four real-interval heights of the `κ'` coordinate field `F_c^P`: `λ + θ₁χ + c` on `(−∞, −1)`,
`−λ' + πχ + c` on `(−1, 0)`, `λ' + πχ + c` on `(0, q)`, `−λ + (θ₂ + 2π)χ + c` on `(q, ∞)`. -/
def cf94Heights (κ θ₁ θ₂ q c : ℝ) (y : ℝ) : ℝ :=
  if y < -1 then sleLambda κ + θ₁ * chiC κ + c
  else if y < 0 then -sleLambda (16 / κ) + π * chiC κ + c
  else if y < q then sleLambda (16 / κ) + π * chiC κ + c
  else -sleLambda κ + (θ₂ + 2 * π) * chiC κ + c

theorem cf94Heights_of_lt_neg_one {y : ℝ} (hy : y < -1) :
    cf94Heights κ θ₁ θ₂ q c y = sleLambda κ + θ₁ * chiC κ + c := ite_eq_left hy

theorem cf94Heights_of_mem_Ioo_neg_one_zero {y : ℝ} (hy : y ∈ Ioo (-1) 0) :
    cf94Heights κ θ₁ θ₂ q c y = -sleLambda (16 / κ) + π * chiC κ + c := by
  rw [cf94Heights, ite_eq_right (not_lt.2 hy.1.le), ite_eq_left hy.2]

theorem cf94Heights_of_mem_Ioo_zero {y : ℝ} (hy : y ∈ Ioo 0 q) :
    cf94Heights κ θ₁ θ₂ q c y = sleLambda (16 / κ) + π * chiC κ + c := by
  rw [cf94Heights, ite_eq_right (by linarith [hy.1]), ite_eq_right (not_lt.2 hy.1.le), ite_eq_left hy.2]

theorem cf94Heights_of_lt (hq : 0 < q) {y : ℝ} (hy : q < y) :
    cf94Heights κ θ₁ θ₂ q c y = -sleLambda κ + (θ₂ + 2 * π) * chiC κ + c := by
  rw [cf94Heights, ite_eq_right (by linarith), ite_eq_right (by linarith), ite_eq_right (not_lt.2 hy.le)]

/-- **(CF9.3)–(CF9.4) on the lower line.** For a lower boundary point `x ≠ 0` of the strip, `P(x)` is real and the
`κ'` coordinate rule `F_c^P(P x) = −h(x) − χ Im L_P(x) + c` gives the (CF9.4) height at `P(x)`. -/
theorem cf94Heights_stripToH_lower (hq : 0 < q) {x : ℝ} (hx : x ≠ 0) :
    (stripToH q x).im = 0 ∧
      cf94Heights κ θ₁ θ₂ q c (stripToH q x).re =
        -cf92Lower κ θ₁ θ₂ x - chiC κ * (derivLogStripToH q x).im + c := by
  rw [stripToH_ofReal, ofReal_im, ofReal_re]
  refine ⟨rfl, ?_⟩
  rcases lt_or_gt_of_ne hx with hlt | hgt
  · rw [cf94Heights_of_lt hq (stripToH_lower_of_neg hq hlt), im_derivLogStripToH_lower_of_neg hlt,
      cf92Lower, ite_eq_left hlt]
    ring
  · rw [cf94Heights_of_lt_neg_one (stripToH_lower_of_pos hq hgt), im_derivLogStripToH_lower_of_pos hgt,
      cf92Lower, ite_eq_right (not_lt.2 hgt.le)]
    ring

/-- **(CF9.3)–(CF9.4) on the upper line.** For an upper boundary point `x + i ≠ z_*`, `P(x + i)` is real and the
`κ'` coordinate rule gives the (CF9.4) height at `P(x + i)`. -/
theorem cf94Heights_stripToH_upper (hq : 0 < q) {x : ℝ} (hx : x ≠ Real.log q / π) :
    (stripToH q (x + I)).im = 0 ∧
      cf94Heights κ θ₁ θ₂ q c (stripToH q (x + I)).re =
        -cf92Upper κ q x - chiC κ * (derivLogStripToH q (x + I)).im + c := by
  rw [stripToH_add_I, ofReal_im, ofReal_re, im_derivLogStripToH_upper]
  refine ⟨rfl, ?_⟩
  rcases lt_or_gt_of_ne hx with hlt | hgt
  · rw [cf94Heights_of_mem_Ioo_zero (stripToH_upper_of_lt hq hlt), cf92Upper, ite_eq_left hlt]
    ring
  · rw [cf94Heights_of_mem_Ioo_neg_one_zero (stripToH_upper_of_gt hq hgt), cf92Upper,
      ite_eq_right (not_lt.2 hgt.le)]
    ring

/-! ### Centering and the seed weights (CF9.5) -/

/-- **Centering** (Aux. lemma 118): the two newly exposed driver-side heights of (CF9.4) are `−λ'` and `+λ'`
precisely for `c = −πχ`. -/
theorem cf94_driver_heights_iff (hq : 0 < q) :
    (cf94Heights κ θ₁ θ₂ q c (-(1 / 2)) = -sleLambda (16 / κ) ∧
        cf94Heights κ θ₁ θ₂ q c (q / 2) = sleLambda (16 / κ)) ↔ c = -(π * chiC κ) := by
  rw [cf94Heights_of_mem_Ioo_neg_one_zero ⟨by norm_num, by norm_num⟩,
    cf94Heights_of_mem_Ioo_zero ⟨by linarith, by linarith⟩]
  constructor
  · rintro ⟨h, -⟩; linarith
  · rintro rfl; constructor <;> ring

/-- `λ/λ' = κ'/4`. -/
theorem sleLambda_div_sleLambda_sixteen_div {κ : ℝ} (hκ : 0 < κ) :
    sleLambda κ / sleLambda (16 / κ) = 16 / κ / 4 := by
  have := Sec4.sleLambda_ne_zero hκ
  rw [Sec4.sleLambda_sixteen_div hκ]
  field_simp
  norm_num

/-- `πχ = (κ'/2 − 2) λ'`. -/
theorem pi_mul_chiC_eq_mul_sleLambda_sixteen_div {κ : ℝ} (hκ : 0 < κ) :
    π * chiC κ = (16 / κ / 2 - 2) * sleLambda (16 / κ) := by
  have h := Sec4.pi_mul_chiC (div_pos (by norm_num : (0 : ℝ) < 16) hκ)
  rw [Sec4.chiC_sixteen_div hκ] at h
  linarith

/-- `πχ/λ' = κ'/2 − 2`. -/
theorem pi_mul_chiC_div_sleLambda_sixteen_div {κ : ℝ} (hκ : 0 < κ) :
    π * chiC κ / sleLambda (16 / κ) = 16 / κ / 2 - 2 := by
  rw [pi_mul_chiC_eq_mul_sleLambda_sixteen_div hκ,
    mul_div_assoc, div_self (Sec4.sleLambda_sixteen_div_pos hκ).ne', mul_one]

/-- (CF9.5), left: `ρ_L = (1/2 − θ₁/π)(κ'/2 − 2) − 2`. -/
def cf95RhoL (κ θ₁ : ℝ) : ℝ := (1 / 2 - θ₁ / π) * (16 / κ / 2 - 2) - 2

/-- (CF9.5), right: `ρ_R = (1/2 + θ₂/π)(κ'/2 − 2) − 2`. -/
def cf95RhoR (κ θ₂ : ℝ) : ℝ := (1 / 2 + θ₂ / π) * (16 / κ / 2 - 2) - 2

theorem chiC_eq_of_sixteen_div {κ : ℝ} (hκ : 0 < κ) :
    chiC κ = (16 / κ / 2 - 2) * sleLambda (16 / κ) / π := by
  rw [← pi_mul_chiC_eq_mul_sleLambda_sixteen_div hκ]
  field_simp

theorem sleLambda_eq_of_sixteen_div {κ : ℝ} (hκ : 0 < κ) :
    sleLambda κ = 16 / κ / 4 * sleLambda (16 / κ) := by
  have := (Sec4.sleLambda_sixteen_div_pos hκ).ne'
  rw [← sleLambda_div_sleLambda_sixteen_div hκ]
  field_simp

/-- **(CF9.5), left exterior height**: `λ + (θ₁ − π)χ = −λ'(1 + ρ_L)`. -/
theorem cf95_left_height {κ : ℝ} (hκ : 0 < κ) (θ₁ : ℝ) :
    sleLambda κ + (θ₁ - π) * chiC κ = -sleLambda (16 / κ) * (1 + cf95RhoL κ θ₁) := by
  have hπ := Real.pi_pos.ne'
  rw [sleLambda_eq_of_sixteen_div hκ, chiC_eq_of_sixteen_div hκ, cf95RhoL]
  field_simp
  ring

/-- **(CF9.5), right exterior height**: `−λ + (θ₂ + π)χ = λ'(1 + ρ_R)`. -/
theorem cf95_right_height {κ : ℝ} (hκ : 0 < κ) (θ₂ : ℝ) :
    -sleLambda κ + (θ₂ + π) * chiC κ = sleLambda (16 / κ) * (1 + cf95RhoR κ θ₂) := by
  have hπ := Real.pi_pos.ne'
  rw [sleLambda_eq_of_sixteen_div hκ, chiC_eq_of_sixteen_div hκ, cf95RhoR]
  field_simp
  ring

/-- (CF9.5) is the unique solution: `λ + (θ₁ − π)χ = −λ'(1 + ρ)` iff `ρ = ρ_L`. -/
theorem cf95RhoL_eq_iff {κ : ℝ} (hκ : 0 < κ) {θ₁ ρ : ℝ} :
    sleLambda κ + (θ₁ - π) * chiC κ = -sleLambda (16 / κ) * (1 + ρ) ↔ ρ = cf95RhoL κ θ₁ := by
  have h := (Sec4.sleLambda_sixteen_div_pos hκ).ne'
  rw [cf95_left_height hκ]
  constructor
  · intro he
    have := mul_left_cancel₀ (neg_ne_zero.2 h) he
    linarith
  · rintro rfl; rfl

/-- (CF9.5) is the unique solution: `−λ + (θ₂ + π)χ = λ'(1 + ρ)` iff `ρ = ρ_R`. -/
theorem cf95RhoR_eq_iff {κ : ℝ} (hκ : 0 < κ) {θ₂ ρ : ℝ} :
    -sleLambda κ + (θ₂ + π) * chiC κ = sleLambda (16 / κ) * (1 + ρ) ↔ ρ = cf95RhoR κ θ₂ := by
  have h := (Sec4.sleLambda_sixteen_div_pos hκ).ne'
  rw [cf95_right_height hκ]
  constructor
  · intro he
    have := mul_left_cancel₀ h he
    linarith
  · rintro rfl; rfl

/-- (CF9.5) as Sec4's height-to-weight conversions with parameter `κ'`. -/
theorem cf95RhoL_eq_cumWeightLeft {κ : ℝ} (hκ : 0 < κ) (θ₁ : ℝ) :
    cf95RhoL κ θ₁ = Sec4.cumWeightLeft (16 / κ) (sleLambda κ + (θ₁ - π) * chiC κ) := by
  have := (Sec4.sleLambda_sixteen_div_pos hκ).ne'
  rw [cf95_left_height hκ, Sec4.cumWeightLeft]
  field_simp
  ring

theorem cf95RhoR_eq_cumWeightRight {κ : ℝ} (hκ : 0 < κ) (θ₂ : ℝ) :
    cf95RhoR κ θ₂ = Sec4.cumWeightRight (16 / κ) (-sleLambda κ + (θ₂ + π) * chiC κ) := by
  have := (Sec4.sleLambda_sixteen_div_pos hκ).ne'
  rw [cf95_right_height hκ, Sec4.cumWeightRight]
  field_simp
  ring

/-- **Aux. lemma 118, centred word.** In the frame `c = −πχ` the (CF9.4) heights are the seed-oriented word with
weights (CF9.5): `−λ'(1 + ρ_L)` on `(−∞, −1)`, `−λ'` on `(−1, 0)`, `λ'` on `(0, q)`, `λ'(1 + ρ_R)` on `(q, ∞)`. -/
theorem cf94Heights_centered (hκ : 0 < κ) (hq : 0 < q) {y : ℝ} :
    (y < -1 → cf94Heights κ θ₁ θ₂ q (-(π * chiC κ)) y = -sleLambda (16 / κ) * (1 + cf95RhoL κ θ₁)) ∧
      (y ∈ Ioo (-1) 0 → cf94Heights κ θ₁ θ₂ q (-(π * chiC κ)) y = -sleLambda (16 / κ)) ∧
      (y ∈ Ioo 0 q → cf94Heights κ θ₁ θ₂ q (-(π * chiC κ)) y = sleLambda (16 / κ)) ∧
      (q < y → cf94Heights κ θ₁ θ₂ q (-(π * chiC κ)) y = sleLambda (16 / κ) * (1 + cf95RhoR κ θ₂)) := by
  refine ⟨fun hy => ?_, fun hy => ?_, fun hy => ?_, fun hy => ?_⟩
  · rw [cf94Heights_of_lt_neg_one hy, ← cf95_left_height hκ]; ring
  · rw [cf94Heights_of_mem_Ioo_neg_one_zero hy]; ring
  · rw [cf94Heights_of_mem_Ioo_zero hy]; ring
  · rw [cf94Heights_of_lt hq hy, ← cf95_right_height hκ]; ring

/-! ### The constant is a field choice, not an argument branch -/

theorem isPreconnected_strip : IsPreconnected strip := by
  have : strip = Complex.im ⁻¹' Ioo 0 1 := rfl
  rw [this]
  exact ((convex_Ioo (0 : ℝ) 1).linear_preimage Complex.imLm).isPreconnected

/-- Any other analytic logarithm of `P'` on the strip is `L_P + 2πin`; it changes the coordinate correction
`−X Im L` by the one constant `−2πnX` (for a coefficient `X`, e.g. `X = χ`). -/
theorem exists_int_im_eq_of_isDerivLog_stripToH (hq : 0 < q) {L : ℂ → ℂ}
    (hL : IsDerivLog (stripToH q) L strip) (X : ℝ) :
    ∃ n : ℤ, ∀ z ∈ strip, -X * (L z).im = -X * (derivLogStripToH q z).im - 2 * π * n * X := by
  obtain ⟨n, hn⟩ := hL.exists_int_eqOn isOpen_strip isPreconnected_strip (isDerivLog_stripToH hq)
  refine ⟨n, fun z hz => ?_⟩
  rw [hn hz]
  simp only [add_im, mul_im, mul_re, ofReal_re, ofReal_im, I_re, I_im, intCast_re, intCast_im,
    re_ofNat, im_ofNat]
  ring

/-- A branch change can never produce the centering: `−2πnχ ≠ −πχ` for every integer `n` (`0 < κ < 4`). -/
theorem two_pi_mul_int_mul_chiC_ne_pi_mul_chiC {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (n : ℤ) :
    -(2 * π * n * chiC κ) ≠ -(π * chiC κ) := by
  have hχ := Sec4.chiC_pos hκ hκ4
  intro h
  have h2 : ((2 * n : ℤ) : ℝ) = ((1 : ℤ) : ℝ) := by
    have : (2 * n - 1 : ℝ) * (π * chiC κ) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · push_cast; linarith
    · exact absurd h (mul_pos Real.pi_pos hχ).ne'
  have := Int.cast_injective h2
  omega

/-! ### (CF9.6): transport of the centred frame -/

/-- **(CF9.6)** for functions (means, boundary data): `T^{κ'}_ψ(−h + c) = −T^κ_ψ(h) + c`, since `χ(κ') = −χ`.
Composition along the chain-rule lift is `coordChange_coordChange`. -/
theorem coordChange_neg_add_const {κ : ℝ} (hκ : 0 < κ) (ψ L : ℂ → ℂ) (h : ℂ → ℝ) (c : ℝ) :
    coordChange (chiC (16 / κ)) ψ L (fun z => -h z + c) =
      fun z => -coordChange (chiC κ) ψ L h z + c := by
  funext z
  simp only [coordChange, Sec4.chiC_sixteen_div hκ]
  ring

end Sec7

end InteractingSLE
