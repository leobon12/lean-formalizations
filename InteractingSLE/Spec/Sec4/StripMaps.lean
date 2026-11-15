/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Foundations.Complex.DerivLog
import InteractingSLE.Foundations.Harmonic.Strip

/-!
# The explicit strip charts of §4.1 and their derivative lifts

Packet PROVE-SEC4-A (specification §4.1, `source/spec/p097-144.md` L174–L470, pp. 103–115).

Every proof in §4.1 maps the strip `𝒮 = {0 < Im z < 1}` by an explicit conformal map and transforms the field by
the coordinate rule (1.4), `h_𝒮 = h ∘ ψ − X arg ψ'` (`InteractingSLE.coordChange`), with the continuous branch of
`arg ψ'` that vanishes on the lower boundary line. This file proves, for each chart, that the displayed lift is a
derivative lift on the strip (`IsDerivLog`), where the chart maps the strip, and the values of the lift's imaginary
part (the branch of `arg ψ'`) on the two boundary lines:

* `expChart`, `z ↦ e^{πz} − 1` (Figure 4.1; Lemma 4.3, first case): argument `0` on the lower line, `π` on the upper
  line; the lower line goes to `(−1, ∞)`, the upper line to `(−∞, −1)`;
* `stripQ q`, `z ↦ (e^{πz} − 1)/(e^{πz} + q)` (Lemma 4.5's `ψ`, with `q = r = e^{π x₀}`; reused from
  `Foundations/Complex/DerivLog.lean`): argument `0` on the lower line, `+π` on the upper line left of `z₀`, `−π`
  right of `z₀`;
* `leftEndChart`, `z ↦ 1 − e^{−πz}` (Aux. lemma 22, the all-upper-positive alternative; (HB1) after rescaling):
  argument `0` below and `−π` above;
* `spanChart r₀ r₁` (UC11) and the semi-infinite and full-span maps `spanChartLeft r₁`, `spanChartRight r₀`,
  `π z` (UC12), onto the strip `{0 < Im z < π}`: argument `π` on the old upper arc left of `I`, `0` on `I`, `−π` right
  of `I`.

The argument values are those of `Im L` for the displayed lift `L`; `continuousWithinAt_im_derivLog…` shows that
these are the boundary limits from inside the strip (the branch is continuous on the closed strip off the pole), so
they are the values the coordinate rule assigns to the boundary data.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology
open scoped Real
open QuantumZipper (H)

namespace InteractingSLE

namespace Sec4

/-! ### Exponentials on the two boundary lines -/

theorem exp_pi_mul_ofReal (x : ℝ) : exp ((π : ℂ) * x) = (Real.exp (π * x) : ℂ) := by
  rw [← ofReal_mul, ofReal_exp]

/-- On the upper line, `e^{π(x + i)} = −e^{πx}`. -/
theorem exp_pi_mul_upper (x : ℝ) : exp ((π : ℂ) * (x + I)) = -(Real.exp (π * x) : ℂ) := by
  rw [mul_add, exp_add, exp_pi_mul_ofReal, exp_pi_mul_I]; ring

theorem im_ofReal_add_I (x : ℝ) : ((x : ℂ) + I).im = 1 := by simp

theorem mem_closure_strip_of_im {z : ℂ} (h0 : 0 ≤ z.im) (h1 : z.im ≤ 1) : z ∈ closure strip := by
  -- the segment from `z` towards `z.re + i/2` lies in the strip
  have hseg : ∀ t ∈ Ioo (0 : ℝ) 1,
      (1 - t) • z + t • ((z.re : ℂ) + I / 2) ∈ strip := by
    intro t ht
    have him : ((1 - t) • z + t • ((z.re : ℂ) + I / 2)).im = (1 - t) * z.im + t / 2 := by
      simp only [add_im, Complex.real_smul, mul_im, ofReal_re, ofReal_im, div_ofNat_im, I_im]
      ring
    show 0 < _ ∧ _ < 1
    rw [him]
    constructor <;> nlinarith [ht.1, ht.2]
  have hlim : Tendsto (fun t : ℝ => (1 - t) • z + t • ((z.re : ℂ) + I / 2)) (𝓝[>] 0) (𝓝 z) := by
    have hc : Continuous (fun t : ℝ => (1 - t) • z + t • ((z.re : ℂ) + I / 2)) := by fun_prop
    have := hc.tendsto 0
    simp only [sub_zero, one_smul, zero_smul, add_zero] at this
    exact this.mono_left nhdsWithin_le_nhds
  refine mem_closure_of_tendsto hlim ?_
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < 1 by norm_num)] with t ht using hseg t ht

/-! ### Continuity of the principal argument on the closed upper half-plane -/

/-- `arg` is continuous on `{Im ≥ 0} \ {0}`, relative to the closed upper half-plane. -/
theorem continuousWithinAt_arg_closedUpper {w : ℂ} (hw : w ≠ 0) (_him : 0 ≤ w.im) :
    ContinuousWithinAt arg {z : ℂ | 0 ≤ z.im} w := by
  by_cases hs : w ∈ slitPlane
  · exact (continuousAt_arg hs).continuousWithinAt
  · rw [mem_slitPlane_iff, not_or, not_lt, not_not] at hs
    have hre : w.re < 0 := lt_of_le_of_ne hs.1 fun h => hw (Complex.ext h hs.2)
    exact continuousWithinAt_arg_of_re_neg_of_im_zero hre hs.2

theorem im_exp_pi_mul_nonneg {z : ℂ} (hz : z ∈ closure strip) : 0 ≤ (exp ((π : ℂ) * z)).im := by
  have hsub : closure strip ⊆ {w : ℂ | 0 ≤ w.im ∧ w.im ≤ 1} :=
    closure_minimal (fun w hw => ⟨hw.1.le, hw.2.le⟩)
      ((isClosed_le continuous_const continuous_im).inter
        (isClosed_le continuous_im continuous_const))
  obtain ⟨h0, h1⟩ := hsub hz
  rw [exp_im]
  refine mul_nonneg (Real.exp_pos _).le (Real.sin_nonneg_of_nonneg_of_le_pi ?_ ?_)
  · simp only [mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]; exact mul_nonneg Real.pi_pos.le h0
  · simp only [mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]; nlinarith [Real.pi_pos]

/-- For `c` real, `z ↦ arg (e^{πz} + c)` is continuous relative to the closed strip at every point where
`e^{πz} + c ≠ 0`. -/
theorem continuousWithinAt_arg_exp_add {c : ℝ} {z : ℂ} (hz : z ∈ closure strip)
    (hne : exp ((π : ℂ) * z) + c ≠ 0) :
    ContinuousWithinAt (fun w : ℂ => arg (exp ((π : ℂ) * w) + c)) (closure strip) z := by
  have hg : Continuous (fun w : ℂ => exp ((π : ℂ) * w) + c) := by fun_prop
  show ContinuousWithinAt (arg ∘ fun w : ℂ => exp ((π : ℂ) * w) + c) (closure strip) z
  refine ContinuousWithinAt.comp (f := fun w : ℂ => exp ((π : ℂ) * w) + c) (g := arg)
    (t := {w : ℂ | 0 ≤ w.im}) (continuousWithinAt_arg_closedUpper hne ?_) hg.continuousWithinAt ?_
  · simp only [add_im, ofReal_im, add_zero]; exact im_exp_pi_mul_nonneg hz
  · intro w hw
    simp only [mem_ofPred_eq, add_im, ofReal_im, add_zero]
    exact im_exp_pi_mul_nonneg hw

/-! ### The chart `z ↦ e^{πz} − 1` (Figure 4.1, Lemma 4.3) -/

/-- Figure 4.1's chart `ψ(z) = e^{πz} − 1`: fixes `0`, sends the left strip end to `−1` and the right end to
`∞`. -/
def expChart (z : ℂ) : ℂ := exp ((π : ℂ) * z) - 1

/-- Its derivative lift `log π + π z`. -/
def derivLogExpChart (z : ℂ) : ℂ := (Real.log π : ℂ) + π * z

theorem isDerivLog_expChart : IsDerivLog expChart derivLogExpChart univ := by
  refine ⟨by unfold derivLogExpChart; fun_prop, fun z _ => ?_⟩
  have hd : HasDerivAt expChart (π * exp ((π : ℂ) * z)) z :=
    (DerivLog.hasDerivAt_exp_pi_mul z).sub_const 1
  rw [hd.deriv, derivLogExpChart, exp_add, ← ofReal_exp, Real.exp_log Real.pi_pos]

theorem expChart_zero : expChart 0 = 0 := by simp [expChart]

theorem mapsTo_expChart : MapsTo expChart strip H := fun _ hz =>
  DerivLog.sub_one_mem_H (exp_pi_mul_mem_H hz)

/-- `e^{πz} − 1` maps the strip bijectively onto `ℍ`; the inverse is `w ↦ Log(w + 1)/π`. -/
theorem bijOn_expChart : BijOn expChart strip H := by
  refine ⟨mapsTo_expChart, ?_, ?_⟩
  · intro z hz w hw h
    have h' : exp ((π : ℂ) * z) = exp ((π : ℂ) * w) := by
      simpa only [expChart, sub_left_inj] using h
    have him : ∀ u ∈ strip, -π < ((π : ℂ) * u).im ∧ ((π : ℂ) * u).im ≤ π := by
      intro u hu
      simp only [mul_im, ofReal_re, ofReal_im, zero_mul, add_zero]
      constructor <;> nlinarith [Real.pi_pos, hu.1, hu.2]
    have hz' := log_exp (him z hz).1 (him z hz).2
    have hw' := log_exp (him w hw).1 (him w hw).2
    have : (π : ℂ) * z = π * w := by rw [← hz', ← hw', h']
    exact mul_left_cancel₀ (ofReal_ne_zero.2 Real.pi_pos.ne') this
  · intro w hw
    have hw1 : w + 1 ∈ H := by simpa using DerivLog.add_ofReal_mem_H hw 1
    have ha := DerivLog.arg_mem_Ioo_of_mem_H hw1
    refine ⟨log (w + 1) / π, ?_, ?_⟩
    · have hπ := Real.pi_pos
      simp only [strip, mem_ofPred_eq, div_ofReal_im, log_im]
      exact ⟨div_pos ha.1 hπ, (div_lt_one hπ).2 ha.2⟩
    · simp only [expChart]
      rw [mul_div_cancel₀ _ (ofReal_ne_zero.2 Real.pi_pos.ne'),
        exp_log (DerivLog.ne_zero_of_mem_H hw1), add_sub_cancel_right]

theorem im_derivLogExpChart (z : ℂ) : (derivLogExpChart z).im = π * z.im := by
  simp [derivLogExpChart]

/-- The branch of `arg ψ'` is `0` on the lower line. -/
theorem im_derivLogExpChart_lower (x : ℝ) : (derivLogExpChart x).im = 0 := by
  simp [derivLogExpChart]

/-- The branch of `arg ψ'` is `π` on the upper line. -/
theorem im_derivLogExpChart_upper (x : ℝ) : (derivLogExpChart (x + I)).im = π := by
  simp [derivLogExpChart]

/-- The lower line goes to `(−1, ∞)`: `ψ(x) = e^{πx} − 1`. -/
theorem expChart_lower (x : ℝ) : expChart x = ((Real.exp (π * x) - 1 : ℝ) : ℂ) := by
  rw [expChart, exp_pi_mul_ofReal]; push_cast; ring

/-- The upper line goes to `(−∞, −1)`: `ψ(x + i) = −e^{πx} − 1`. -/
theorem expChart_upper (x : ℝ) : expChart (x + I) = ((-Real.exp (π * x) - 1 : ℝ) : ℂ) := by
  rw [expChart, exp_pi_mul_upper]; push_cast; ring

/-! ### Lemma 4.5's chart `ψ = stripQ q`, `q = e^{π x₀}` -/

theorem im_derivLogStripQ (q : ℝ) (z : ℂ) :
    (derivLogStripQ q z).im = π * z.im - 2 * arg (exp ((π : ℂ) * z) + q) := by
  simp [derivLogStripQ, log_im]

/-- Lemma 4.5: the branch of `arg ψ'` is zero on the lower boundary. -/
theorem im_derivLogStripQ_lower {q : ℝ} (hq : 0 < q) (x : ℝ) : (derivLogStripQ q x).im = 0 := by
  rw [im_derivLogStripQ, exp_pi_mul_ofReal, ← ofReal_add,
    arg_ofReal_of_nonneg (by positivity)]
  simp

/-- Lemma 4.5: the branch of `arg ψ'` is `+π` on the upper boundary left of `z₀ = x₀ + i`
(`e^{πx} < q = e^{π x₀}`). -/
theorem im_derivLogStripQ_upper_left {q x : ℝ} (hx : Real.exp (π * x) < q) :
    (derivLogStripQ q (x + I)).im = π := by
  rw [im_derivLogStripQ, exp_pi_mul_upper, im_ofReal_add_I,
    show -(Real.exp (π * x) : ℂ) + q = ((q - Real.exp (π * x) : ℝ) : ℂ) by push_cast; ring,
    arg_ofReal_of_nonneg (by linarith)]
  ring

/-- Lemma 4.5: the branch of `arg ψ'` is `−π` on the upper boundary right of `z₀`. -/
theorem im_derivLogStripQ_upper_right {q x : ℝ} (hx : q < Real.exp (π * x)) :
    (derivLogStripQ q (x + I)).im = -π := by
  rw [im_derivLogStripQ, exp_pi_mul_upper, im_ofReal_add_I,
    show -(Real.exp (π * x) : ℂ) + q = ((q - Real.exp (π * x) : ℝ) : ℂ) by push_cast; ring,
    arg_ofReal_of_neg (by linarith)]
  ring

/-- The branch of `arg ψ'` is continuous on the closed strip away from the pole `z₀`; hence its boundary
values above are the boundary limits from inside. -/
theorem continuousWithinAt_im_derivLogStripQ (q : ℝ) {z : ℂ} (hz : z ∈ closure strip)
    (hne : exp ((π : ℂ) * z) + q ≠ 0) :
    ContinuousWithinAt (fun w => (derivLogStripQ q w).im) (closure strip) z := by
  simp only [im_derivLogStripQ]
  exact ((continuous_const.mul continuous_im).continuousWithinAt).sub
    (continuousWithinAt_const.mul (continuousWithinAt_arg_exp_add hz hne))

theorem stripQ_zero (q : ℝ) : stripQ q 0 = 0 := by simp [stripQ]

/-- The lower line goes into `(−1/q, 1)`. -/
theorem stripQ_lower {q : ℝ} (hq : 0 < q) (x : ℝ) :
    stripQ q x = (((Real.exp (π * x) - 1) / (Real.exp (π * x) + q) : ℝ) : ℂ) ∧
      -(1 / q) < (Real.exp (π * x) - 1) / (Real.exp (π * x) + q) ∧
      (Real.exp (π * x) - 1) / (Real.exp (π * x) + q) < 1 := by
  have he := Real.exp_pos (π * x)
  refine ⟨by rw [stripQ, exp_pi_mul_ofReal]; push_cast; rfl, ?_, ?_⟩
  · rw [lt_div_iff₀ (by positivity)]
    have : -(1 / q) * (Real.exp (π * x) + q) = -(Real.exp (π * x) / q) - 1 := by field_simp; ring
    rw [this]
    have : 0 < Real.exp (π * x) / q := div_pos he hq
    linarith
  · rw [div_lt_one (by positivity)]; linarith

/-- The upper line left of `z₀` goes to `(−∞, −1/q)`, right of `z₀` to `(1, ∞)`. -/
theorem stripQ_upper (q x : ℝ) :
    stripQ q (x + I) = (((Real.exp (π * x) + 1) / (Real.exp (π * x) - q) : ℝ) : ℂ) := by
  rw [stripQ, exp_pi_mul_upper]
  generalize Real.exp (π * x) = e
  push_cast
  rw [show -(e : ℂ) - 1 = -((e : ℂ) + 1) by ring, show -(e : ℂ) + q = -((e : ℂ) - q) by ring,
    neg_div_neg_eq]

theorem stripQ_upper_left_lt {q x : ℝ} (hq : 0 < q) (hx : Real.exp (π * x) < q) :
    (Real.exp (π * x) + 1) / (Real.exp (π * x) - q) < -(1 / q) := by
  have he := Real.exp_pos (π * x)
  rw [div_lt_iff_of_neg (by linarith)]
  have : -(1 / q) * (Real.exp (π * x) - q) = 1 - Real.exp (π * x) / q := by field_simp; ring
  rw [this]
  have : 0 < Real.exp (π * x) / q := div_pos he hq
  linarith

theorem one_lt_stripQ_upper_right {q x : ℝ} (hq : 0 < q) (hx : q < Real.exp (π * x)) :
    1 < (Real.exp (π * x) + 1) / (Real.exp (π * x) - q) := by
  rw [one_lt_div (by linarith)]
  linarith

/-! ### The chart `z ↦ 1 − e^{−πz}` (Aux. lemma 22, all upper heights at least `Λ`) -/

/-- `ψ(z) = 1 − e^{−πz}`: fixes `0`, sends the left strip end to `∞` and the right end to `1`. -/
def leftEndChart (z : ℂ) : ℂ := 1 - exp (-(π : ℂ) * z)

/-- Its derivative lift `log π − π z`. -/
def derivLogLeftEndChart (z : ℂ) : ℂ := (Real.log π : ℂ) - π * z

theorem isDerivLog_leftEndChart : IsDerivLog leftEndChart derivLogLeftEndChart univ := by
  refine ⟨by unfold derivLogLeftEndChart; fun_prop, fun z _ => ?_⟩
  have hd : HasDerivAt leftEndChart (-(exp (-(π : ℂ) * z) * (-(π : ℂ) * 1))) z :=
    ((hasDerivAt_id' z).const_mul (-(π : ℂ))).cexp.const_sub 1
  rw [hd.deriv, derivLogLeftEndChart, sub_eq_add_neg, exp_add, ← ofReal_exp,
    Real.exp_log Real.pi_pos, ← neg_mul]
  ring

theorem leftEndChart_zero : leftEndChart 0 = 0 := by simp [leftEndChart]

theorem mapsTo_leftEndChart : MapsTo leftEndChart strip H := by
  intro z hz
  show 0 < (leftEndChart z).im
  simp only [leftEndChart, neg_mul, sub_im, one_im, zero_sub, exp_im, neg_im, mul_im, ofReal_re,
    ofReal_im, zero_mul, add_zero, Real.sin_neg, mul_neg, neg_neg]
  exact mul_pos (Real.exp_pos _) (Real.sin_pos_of_pos_of_lt_pi (mul_pos Real.pi_pos hz.1)
    (by nlinarith [Real.pi_pos, hz.2]))

theorem im_derivLogLeftEndChart_lower (x : ℝ) : (derivLogLeftEndChart x).im = 0 := by
  simp [derivLogLeftEndChart]

/-- The branch of `arg ψ'` is `−π` on the upper boundary. -/
theorem im_derivLogLeftEndChart_upper (x : ℝ) : (derivLogLeftEndChart (x + I)).im = -π := by
  simp [derivLogLeftEndChart]

/-- The upper line goes to `(1, ∞)`: `ψ(x + i) = 1 + e^{−πx}`. -/
theorem leftEndChart_upper (x : ℝ) :
    leftEndChart (x + I) = ((1 + Real.exp (-(π * x)) : ℝ) : ℂ) := by
  have : exp (-(π : ℂ) * (x + I)) = -(Real.exp (-(π * x)) : ℂ) := by
    rw [neg_mul]
    rw [mul_add, neg_add, exp_add, ← ofReal_mul, ← ofReal_neg, ofReal_exp, ← neg_mul, exp_neg,
      exp_pi_mul_I]
    rw [show ((-1 : ℂ))⁻¹ = -1 by norm_num]; ring
  rw [leftEndChart, this]; push_cast; ring

/-- The lower line goes to `(−∞, 1)`: `ψ(x) = 1 − e^{−πx}`. -/
theorem leftEndChart_lower (x : ℝ) :
    leftEndChart x = ((1 - Real.exp (-(π * x)) : ℝ) : ℂ) := by
  rw [leftEndChart, neg_mul, ← ofReal_mul, ← ofReal_neg, ← ofReal_exp]; push_cast; ring


/-! ### The span charts (UC11)–(UC12) onto the strip of height `π` -/

/-- The strip `{0 < Im z < π}` of Aux. lemmas 21–22. -/
def stripPi : Set ℂ := {z | 0 < z.im ∧ z.im < π}

theorem log_mem_stripPi {w : ℂ} (hw : w ∈ H) : log w ∈ stripPi := by
  have := DerivLog.arg_mem_Ioo_of_mem_H hw
  simp only [stripPi, mem_ofPred_eq, log_im]
  exact this

/-- `(E + r₀)/(E + r₁) ∈ ℍ` for `E ∈ ℍ` and real `r₀ < r₁`. -/
theorem div_add_mem_H {E : ℂ} (hE : E ∈ H) {r₀ r₁ : ℝ} (h : r₀ < r₁) :
    (E + r₀) / (E + r₁) ∈ H := by
  have hb := DerivLog.ne_zero_of_mem_H (DerivLog.add_ofReal_mem_H hE r₁)
  have hE' : 0 < E.im := hE
  show 0 < ((E + r₀) / (E + r₁)).im
  rw [div_im, ← sub_div]
  refine div_pos ?_ (normSq_pos.2 hb)
  simp only [add_im, add_re, ofReal_im, ofReal_re, add_zero]
  nlinarith

theorem real_mul_mem_H {w : ℂ} (hw : w ∈ H) {c : ℝ} (hc : 0 < c) : (c : ℂ) * w ∈ H := by
  show 0 < ((c : ℂ) * w).im
  rw [im_ofReal_mul]; exact mul_pos hc hw

/-- (UC11): the span chart `Φ(z) = Log[((1 + r₁)/(1 + r₀)) (E + r₀)/(E + r₁)]`, `E = e^{πz}`, for a finite span
`u < v` with `r₀ = e^{πu}`, `r₁ = e^{πv}`. -/
def spanChart (r₀ r₁ : ℝ) (z : ℂ) : ℂ :=
  log ((((1 + r₁) / (1 + r₀) : ℝ) : ℂ) *
    ((exp ((π : ℂ) * z) + r₀) / (exp ((π : ℂ) * z) + r₁)))

/-- Its derivative lift `log(π(r₁ − r₀)) + πz − Log(E + r₀) − Log(E + r₁)` (UC11: `Φ' = π(r₁ − r₀)E/((E + r₀)(E + r₁))`). -/
def derivLogSpanChart (r₀ r₁ : ℝ) (z : ℂ) : ℂ :=
  (Real.log (π * (r₁ - r₀)) : ℂ) + π * z - log (exp ((π : ℂ) * z) + r₀) -
    log (exp ((π : ℂ) * z) + r₁)

theorem spanChart_zero {r₀ r₁ : ℝ} (h₀ : 0 < r₀) (h₁ : 0 < r₁) : spanChart r₀ r₁ 0 = 0 := by
  have h0 : (1 + r₀ : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (1 + r₀ : ℝ) ≠ 0)
  have h1 : (1 + r₁ : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (1 + r₁ : ℝ) ≠ 0)
  simp only [spanChart, mul_zero, exp_zero]
  push_cast
  rw [add_comm (1 : ℂ) r₀, add_comm (1 : ℂ) r₁] at *
  rw [div_mul_div_comm, mul_comm, div_self (mul_ne_zero h0 h1), log_one]

theorem spanChart_arg_mem_H {r₀ r₁ : ℝ} (h₀ : 0 < r₀) (h : r₀ < r₁) {z : ℂ} (hz : z ∈ strip) :
    (((1 + r₁) / (1 + r₀) : ℝ) : ℂ) * ((exp ((π : ℂ) * z) + r₀) / (exp ((π : ℂ) * z) + r₁)) ∈ H :=
  real_mul_mem_H (div_add_mem_H (exp_pi_mul_mem_H hz) h) (by apply div_pos <;> linarith)

/-- (UC11): `Φ` maps the strip into the strip of height `π`. -/
theorem mapsTo_spanChart {r₀ r₁ : ℝ} (h₀ : 0 < r₀) (h : r₀ < r₁) : MapsTo (spanChart r₀ r₁) strip stripPi :=
  fun _ hz => log_mem_stripPi (spanChart_arg_mem_H h₀ h hz)

theorem isDerivLog_spanChart {r₀ r₁ : ℝ} (h₀ : 0 < r₀) (h : r₀ < r₁) :
    IsDerivLog (spanChart r₀ r₁) (derivLogSpanChart r₀ r₁) strip := by
  have hE := DerivLog.hasDerivAt_exp_pi_mul
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · have hs0 := DerivLog.mem_slitPlane_of_mem_H (DerivLog.add_ofReal_mem_H (exp_pi_mul_mem_H hz) r₀)
    have hs1 := DerivLog.mem_slitPlane_of_mem_H (DerivLog.add_ofReal_mem_H (exp_pi_mul_mem_H hz) r₁)
    exact ((((differentiableAt_const _).add (differentiableAt_id.const_mul _)).sub
      (((hE z).differentiableAt.add_const (r₀ : ℂ)).clog hs0)).sub
      (((hE z).differentiableAt.add_const (r₁ : ℂ)).clog hs1)).differentiableWithinAt
  · have hm0 := DerivLog.add_ofReal_mem_H (exp_pi_mul_mem_H hz) r₀
    have hm1 := DerivLog.add_ofReal_mem_H (exp_pi_mul_mem_H hz) r₁
    have hn0 := DerivLog.ne_zero_of_mem_H hm0
    have hn1 := DerivLog.ne_zero_of_mem_H hm1
    have hc : (((1 + r₁) / (1 + r₀) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (div_pos (by linarith) (by linarith) : (0 : ℝ) < (1 + r₁) / (1 + r₀)).ne'
    have hf : HasDerivAt (fun w : ℂ => (((1 + r₁) / (1 + r₀) : ℝ) : ℂ) *
        ((exp ((π : ℂ) * w) + r₀) / (exp ((π : ℂ) * w) + r₁)))
        ((((1 + r₁) / (1 + r₀) : ℝ) : ℂ) * (((π * exp ((π : ℂ) * z)) * (exp ((π : ℂ) * z) + r₁) -
          (exp ((π : ℂ) * z) + r₀) * (π * exp ((π : ℂ) * z))) / (exp ((π : ℂ) * z) + r₁) ^ 2)) z :=
      (((hE z).add_const (r₀ : ℂ)).div ((hE z).add_const (r₁ : ℂ)) hn1).const_mul _
    have hΦ := hf.clog (DerivLog.mem_slitPlane_of_mem_H (spanChart_arg_mem_H h₀ h hz))
    have hpos : (0 : ℝ) < π * (r₁ - r₀) := mul_pos Real.pi_pos (by linarith)
    rw [show spanChart r₀ r₁ = fun w : ℂ => log ((((1 + r₁) / (1 + r₀) : ℝ) : ℂ) *
        ((exp ((π : ℂ) * w) + r₀) / (exp ((π : ℂ) * w) + r₁))) from rfl, hΦ.deriv,
      derivLogSpanChart, exp_sub, exp_sub, exp_add, ← ofReal_exp, Real.exp_log hpos,
      exp_log hn0, exp_log hn1]
    have h0c : (1 + (r₀ : ℂ)) ≠ 0 := by exact_mod_cast (by linarith : (1 + r₀ : ℝ) ≠ 0)
    have h1c : (1 + (r₁ : ℂ)) ≠ 0 := by exact_mod_cast (by linarith : (1 + r₁ : ℝ) ≠ 0)
    push_cast
    field_simp
    ring

theorem im_derivLogSpanChart (r₀ r₁ : ℝ) (z : ℂ) :
    (derivLogSpanChart r₀ r₁ z).im =
      π * z.im - arg (exp ((π : ℂ) * z) + r₀) - arg (exp ((π : ℂ) * z) + r₁) := by
  simp [derivLogSpanChart, log_im]

theorem arg_upper_add_of_le {r x : ℝ} (h : Real.exp (π * x) ≤ r) :
    arg (exp ((π : ℂ) * (x + I)) + r) = 0 := by
  rw [exp_pi_mul_upper, show -(Real.exp (π * x) : ℂ) + r = ((r - Real.exp (π * x) : ℝ) : ℂ) by
    push_cast; ring]
  exact arg_ofReal_of_nonneg (by linarith)

theorem arg_upper_add_of_lt {r x : ℝ} (h : r < Real.exp (π * x)) :
    arg (exp ((π : ℂ) * (x + I)) + r) = π := by
  rw [exp_pi_mul_upper, show -(Real.exp (π * x) : ℂ) + r = ((r - Real.exp (π * x) : ℝ) : ℂ) by
    push_cast; ring]
  exact arg_ofReal_of_neg (by linarith)

theorem arg_lower_add {r x : ℝ} (hr : 0 ≤ r) : arg (exp ((π : ℂ) * x) + r) = 0 := by
  rw [exp_pi_mul_ofReal, ← ofReal_add]
  exact arg_ofReal_of_nonneg (by positivity)

/-- (UC11): the lift vanishes on the lower boundary. -/
theorem im_derivLogSpanChart_lower {r₀ r₁ : ℝ} (h₀ : 0 < r₀) (h₁ : 0 < r₁) (x : ℝ) :
    (derivLogSpanChart r₀ r₁ x).im = 0 := by
  rw [im_derivLogSpanChart, arg_lower_add h₀.le, arg_lower_add h₁.le]; simp

/-- (UC11): the lift is `π` on the old upper arc left of `I` (`e^{πx} < r₀`). -/
theorem im_derivLogSpanChart_upper_left {r₀ r₁ x : ℝ} (h : r₀ < r₁) (hx : Real.exp (π * x) < r₀) :
    (derivLogSpanChart r₀ r₁ (x + I)).im = π := by
  rw [im_derivLogSpanChart, arg_upper_add_of_le hx.le, arg_upper_add_of_le (by linarith),
    im_ofReal_add_I]; ring

/-- (UC11): the lift is `0` on `I` (`r₀ < e^{πx} < r₁`). -/
theorem im_derivLogSpanChart_upper_mid {r₀ r₁ x : ℝ} (hx₀ : r₀ < Real.exp (π * x))
    (hx₁ : Real.exp (π * x) < r₁) : (derivLogSpanChart r₀ r₁ (x + I)).im = 0 := by
  rw [im_derivLogSpanChart, arg_upper_add_of_lt hx₀, arg_upper_add_of_le hx₁.le,
    im_ofReal_add_I]; ring

/-- (UC11): the lift is `−π` on the old upper arc right of `I` (`e^{πx} > r₁`). -/
theorem im_derivLogSpanChart_upper_right {r₀ r₁ x : ℝ} (h : r₀ < r₁) (hx : r₁ < Real.exp (π * x)) :
    (derivLogSpanChart r₀ r₁ (x + I)).im = -π := by
  rw [im_derivLogSpanChart, arg_upper_add_of_lt (by linarith), arg_upper_add_of_lt hx,
    im_ofReal_add_I]; ring

/-- The lift is continuous on the closed strip off the two jump points `u + i`, `v + i`. -/
theorem continuousWithinAt_im_derivLogSpanChart (r₀ r₁ : ℝ) {z : ℂ} (hz : z ∈ closure strip)
    (hne₀ : exp ((π : ℂ) * z) + r₀ ≠ 0) (hne₁ : exp ((π : ℂ) * z) + r₁ ≠ 0) :
    ContinuousWithinAt (fun w => (derivLogSpanChart r₀ r₁ w).im) (closure strip) z := by
  simp only [im_derivLogSpanChart]
  exact (((continuous_const.mul continuous_im).continuousWithinAt).sub
    (continuousWithinAt_arg_exp_add hz hne₀)).sub (continuousWithinAt_arg_exp_add hz hne₁)

/-- (UC11): the old upper boundary is mapped to the line `Im = π` exactly along `I`, and to the real line
outside the closure of `I`: `Φ(x + i) = Log[c (r₀ − e^{πx})/(r₁ − e^{πx})]`. -/
theorem spanChart_upper (r₀ r₁ x : ℝ) :
    spanChart r₀ r₁ (x + I) =
      log ((((1 + r₁) / (1 + r₀) * ((r₀ - Real.exp (π * x)) / (r₁ - Real.exp (π * x))) : ℝ) : ℂ)) := by
  rw [spanChart, exp_pi_mul_upper]
  congr 1
  generalize Real.exp (π * x) = e
  push_cast
  ring

theorem im_spanChart_upper_mid {r₀ r₁ x : ℝ} (h₀ : 0 < r₀) (hx₀ : r₀ < Real.exp (π * x))
    (hx₁ : Real.exp (π * x) < r₁) : (spanChart r₀ r₁ (x + I)).im = π := by
  rw [spanChart_upper, log_im]
  refine arg_ofReal_of_neg (mul_neg_of_pos_of_neg (div_pos (by linarith) (by linarith))
    (div_neg_of_neg_of_pos (by linarith) (by linarith)))

theorem im_spanChart_upper_left {r₀ r₁ x : ℝ} (h₀ : 0 < r₀) (h : r₀ < r₁) (hx : Real.exp (π * x) < r₀) :
    (spanChart r₀ r₁ (x + I)).im = 0 ∧
      (spanChart r₀ r₁ (x + I)).re < 0 := by
  have he := Real.exp_pos (π * x)
  set e := Real.exp (π * x)
  have hpos : 0 < (1 + r₁) / (1 + r₀) * ((r₀ - e) / (r₁ - e)) :=
    mul_pos (div_pos (by linarith) (by linarith)) (div_pos (by linarith) (by linarith))
  have hlt : (1 + r₁) / (1 + r₀) * ((r₀ - e) / (r₁ - e)) < 1 := by
    rw [div_mul_div_comm, div_lt_one (by nlinarith)]
    nlinarith
  rw [spanChart_upper, log_im, log_re, arg_ofReal_of_nonneg hpos.le, norm_real,
    Real.norm_of_nonneg hpos.le]
  exact ⟨rfl, Real.log_neg hpos hlt⟩

theorem im_spanChart_upper_right {r₀ r₁ x : ℝ} (h₀ : 0 < r₀) (h : r₀ < r₁) (hx : r₁ < Real.exp (π * x)) :
    (spanChart r₀ r₁ (x + I)).im = 0 ∧
      0 < (spanChart r₀ r₁ (x + I)).re := by
  set e := Real.exp (π * x)
  have hpos : 0 < (1 + r₁) / (1 + r₀) * ((r₀ - e) / (r₁ - e)) :=
    mul_pos (div_pos (by linarith) (by linarith))
      (div_pos_of_neg_of_neg (by linarith) (by linarith))
  have hgt : 1 < (1 + r₁) / (1 + r₀) * ((r₀ - e) / (r₁ - e)) := by
    rw [div_mul_div_comm, one_lt_div_of_neg (by nlinarith)] at *
    · nlinarith
  rw [spanChart_upper, log_im, log_re, arg_ofReal_of_nonneg hpos.le, norm_real,
    Real.norm_of_nonneg hpos.le]
  exact ⟨rfl, Real.log_pos hgt⟩

/-- (UC12), `u = −∞`: `Φ(z) = Log[(1 + r₁)E/(E + r₁)]`. -/
def spanChartLeft (r₁ : ℝ) (z : ℂ) : ℂ :=
  log (((1 + r₁ : ℝ) : ℂ) * (exp ((π : ℂ) * z) / (exp ((π : ℂ) * z) + r₁)))

/-- Its lift `log(π r₁) − Log(E + r₁)` (`Φ' = π r₁/(E + r₁)`). -/
def derivLogSpanChartLeft (r₁ : ℝ) (z : ℂ) : ℂ :=
  (Real.log (π * r₁) : ℂ) - log (exp ((π : ℂ) * z) + r₁)

/-- (UC12), `v = +∞`: `Φ(z) = Log[(E + r₀)/(1 + r₀)]`. -/
def spanChartRight (r₀ : ℝ) (z : ℂ) : ℂ :=
  log ((exp ((π : ℂ) * z) + r₀) / ((1 + r₀ : ℝ) : ℂ))

/-- Its lift `log π + πz − Log(E + r₀)` (`Φ' = πE/(E + r₀)`). -/
def derivLogSpanChartRight (r₀ : ℝ) (z : ℂ) : ℂ :=
  (Real.log π : ℂ) + π * z - log (exp ((π : ℂ) * z) + r₀)

theorem div_add_self_mem_H {E : ℂ} (hE : E ∈ H) {r : ℝ} (hr : 0 < r) : E / (E + r) ∈ H := by
  have := div_add_mem_H hE hr
  simpa using this

theorem spanChartLeft_zero {r₁ : ℝ} (h₁ : 0 < r₁) : spanChartLeft r₁ 0 = 0 := by
  have h1 : (1 + r₁ : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (1 + r₁ : ℝ) ≠ 0)
  simp only [spanChartLeft, mul_zero, exp_zero]
  push_cast
  rw [mul_one_div_cancel h1, log_one]

theorem spanChartRight_zero {r₀ : ℝ} (h₀ : 0 < r₀) : spanChartRight r₀ 0 = 0 := by
  have h0 : (1 + r₀ : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (1 + r₀ : ℝ) ≠ 0)
  simp only [spanChartRight, mul_zero, exp_zero]
  push_cast
  rw [div_self h0, log_one]

theorem mapsTo_spanChartLeft {r₁ : ℝ} (h₁ : 0 < r₁) : MapsTo (spanChartLeft r₁) strip stripPi :=
  fun _ hz => log_mem_stripPi (real_mul_mem_H (div_add_self_mem_H (exp_pi_mul_mem_H hz) h₁)
    (by linarith))

theorem mapsTo_spanChartRight {r₀ : ℝ} (h₀ : 0 < r₀) : MapsTo (spanChartRight r₀) strip stripPi := by
  intro z hz
  refine log_mem_stripPi ?_
  rw [div_eq_inv_mul, ← ofReal_inv]
  exact real_mul_mem_H (DerivLog.add_ofReal_mem_H (exp_pi_mul_mem_H hz) r₀) (by positivity)

theorem isDerivLog_spanChartLeft {r₁ : ℝ} (h₁ : 0 < r₁) :
    IsDerivLog (spanChartLeft r₁) (derivLogSpanChartLeft r₁) strip := by
  have hE := DerivLog.hasDerivAt_exp_pi_mul
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · have hs1 := DerivLog.mem_slitPlane_of_mem_H (DerivLog.add_ofReal_mem_H (exp_pi_mul_mem_H hz) r₁)
    exact ((differentiableAt_const _).sub
      (((hE z).differentiableAt.add_const (r₁ : ℂ)).clog hs1)).differentiableWithinAt
  · have hm1 := DerivLog.add_ofReal_mem_H (exp_pi_mul_mem_H hz) r₁
    have hn1 := DerivLog.ne_zero_of_mem_H hm1
    have hnE := DerivLog.ne_zero_of_mem_H (exp_pi_mul_mem_H hz)
    have hf : HasDerivAt (fun w : ℂ => ((1 + r₁ : ℝ) : ℂ) *
        (exp ((π : ℂ) * w) / (exp ((π : ℂ) * w) + r₁)))
        (((1 + r₁ : ℝ) : ℂ) * (((π * exp ((π : ℂ) * z)) * (exp ((π : ℂ) * z) + r₁) -
          exp ((π : ℂ) * z) * (π * exp ((π : ℂ) * z))) / (exp ((π : ℂ) * z) + r₁) ^ 2)) z :=
      ((hE z).div ((hE z).add_const (r₁ : ℂ)) hn1).const_mul _
    have hΦ := hf.clog (DerivLog.mem_slitPlane_of_mem_H
      (real_mul_mem_H (div_add_self_mem_H (exp_pi_mul_mem_H hz) h₁) (by linarith)))
    have hpos : (0 : ℝ) < π * r₁ := mul_pos Real.pi_pos h₁
    have h1 : ((1 + r₁ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (1 + r₁ : ℝ) ≠ 0)
    rw [show spanChartLeft r₁ = fun w : ℂ => log (((1 + r₁ : ℝ) : ℂ) *
        (exp ((π : ℂ) * w) / (exp ((π : ℂ) * w) + r₁))) from rfl, hΦ.deriv,
      derivLogSpanChartLeft, exp_sub, ← ofReal_exp, Real.exp_log hpos, exp_log hn1]
    have h1c : (1 + (r₁ : ℂ)) ≠ 0 := by exact_mod_cast (by linarith : (1 + r₁ : ℝ) ≠ 0)
    push_cast
    field_simp
    ring

theorem isDerivLog_spanChartRight {r₀ : ℝ} (h₀ : 0 < r₀) :
    IsDerivLog (spanChartRight r₀) (derivLogSpanChartRight r₀) strip := by
  have hE := DerivLog.hasDerivAt_exp_pi_mul
  refine ⟨fun z hz => ?_, fun z hz => ?_⟩
  · have hs0 := DerivLog.mem_slitPlane_of_mem_H (DerivLog.add_ofReal_mem_H (exp_pi_mul_mem_H hz) r₀)
    exact (((differentiableAt_const _).add (differentiableAt_id.const_mul _)).sub
      (((hE z).differentiableAt.add_const (r₀ : ℂ)).clog hs0)).differentiableWithinAt
  · have hm0 := DerivLog.add_ofReal_mem_H (exp_pi_mul_mem_H hz) r₀
    have hn0 := DerivLog.ne_zero_of_mem_H hm0
    have h0 : ((1 + r₀ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (by linarith : (1 + r₀ : ℝ) ≠ 0)
    have hf : HasDerivAt (fun w : ℂ => (exp ((π : ℂ) * w) + r₀) / ((1 + r₀ : ℝ) : ℂ))
        (π * exp ((π : ℂ) * z) / ((1 + r₀ : ℝ) : ℂ)) z :=
      ((hE z).add_const (r₀ : ℂ)).div_const _
    have hmem : (exp ((π : ℂ) * z) + r₀) / ((1 + r₀ : ℝ) : ℂ) ∈ H := by
      rw [div_eq_inv_mul, ← ofReal_inv]
      exact real_mul_mem_H hm0 (by positivity)
    have hΦ := hf.clog (DerivLog.mem_slitPlane_of_mem_H hmem)
    rw [show spanChartRight r₀ = fun w : ℂ => log ((exp ((π : ℂ) * w) + r₀) / ((1 + r₀ : ℝ) : ℂ))
        from rfl, hΦ.deriv, derivLogSpanChartRight, exp_sub, exp_add, ← ofReal_exp,
      Real.exp_log Real.pi_pos, exp_log hn0]
    field_simp

/-- (UC12), `u = −∞`: lift `0` on the lower line, `0` on `I = {x < v}`, `−π` right of `I`. -/
theorem im_derivLogSpanChartLeft (r₁ : ℝ) (z : ℂ) :
    (derivLogSpanChartLeft r₁ z).im = -arg (exp ((π : ℂ) * z) + r₁) := by
  simp [derivLogSpanChartLeft, log_im]

theorem im_derivLogSpanChartLeft_lower {r₁ : ℝ} (h₁ : 0 < r₁) (x : ℝ) :
    (derivLogSpanChartLeft r₁ x).im = 0 := by
  rw [im_derivLogSpanChartLeft, arg_lower_add h₁.le, neg_zero]

theorem im_derivLogSpanChartLeft_upper_mid {r₁ x : ℝ} (hx : Real.exp (π * x) < r₁) :
    (derivLogSpanChartLeft r₁ (x + I)).im = 0 := by
  rw [im_derivLogSpanChartLeft, arg_upper_add_of_le hx.le, neg_zero]

theorem im_derivLogSpanChartLeft_upper_right {r₁ x : ℝ} (hx : r₁ < Real.exp (π * x)) :
    (derivLogSpanChartLeft r₁ (x + I)).im = -π := by
  rw [im_derivLogSpanChartLeft, arg_upper_add_of_lt hx]

/-- (UC12), `v = +∞`: lift `0` on the lower line, `π` left of `I = {x > u}`, `0` on `I`. -/
theorem im_derivLogSpanChartRight (r₀ : ℝ) (z : ℂ) :
    (derivLogSpanChartRight r₀ z).im = π * z.im - arg (exp ((π : ℂ) * z) + r₀) := by
  simp [derivLogSpanChartRight, log_im]

theorem im_derivLogSpanChartRight_lower {r₀ : ℝ} (h₀ : 0 < r₀) (x : ℝ) :
    (derivLogSpanChartRight r₀ x).im = 0 := by
  rw [im_derivLogSpanChartRight, arg_lower_add h₀.le]; simp

theorem im_derivLogSpanChartRight_upper_left {r₀ x : ℝ} (hx : Real.exp (π * x) < r₀) :
    (derivLogSpanChartRight r₀ (x + I)).im = π := by
  rw [im_derivLogSpanChartRight, arg_upper_add_of_le hx.le, im_ofReal_add_I]; ring

theorem im_derivLogSpanChartRight_upper_mid {r₀ x : ℝ} (hx : r₀ < Real.exp (π * x)) :
    (derivLogSpanChartRight r₀ (x + I)).im = 0 := by
  rw [im_derivLogSpanChartRight, arg_upper_add_of_lt hx, im_ofReal_add_I]; ring

/-- (UC12), full span: `Φ(z) = πz` with constant lift `log π`. -/
theorem isDerivLog_pi_mul : IsDerivLog (fun z : ℂ => (π : ℂ) * z) (fun _ => (Real.log π : ℂ)) univ := by
  refine ⟨differentiableOn_const _, fun z _ => ?_⟩
  rw [((hasDerivAt_id' z).const_mul (π : ℂ)).deriv, ← ofReal_exp, Real.exp_log Real.pi_pos, mul_one]

theorem mapsTo_pi_mul : MapsTo (fun z : ℂ => (π : ℂ) * z) strip stripPi := by
  intro z hz
  simp only [stripPi, mem_ofPred_eq, im_ofReal_mul]
  exact ⟨mul_pos Real.pi_pos hz.1, by nlinarith [Real.pi_pos, hz.2]⟩

end Sec4

end InteractingSLE
