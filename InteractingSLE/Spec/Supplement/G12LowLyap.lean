/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Lemma G12 when the weight before the mark is `≤ −2`: the Lyapunov function of the reference

Packet PROVE-G12C. Supplement §7.4 (Lemma G4) and Aux. lemma 132 (`source/spec/p385-432.md` L552–L640, the
first-swallow table (SS1) and the gap equation (SS5)–(SS6)). For the two-mark reference — weight `S'` on the last mark
`x_k` below the target mark `y`, the actual weight `ρ_Y` on the group of `y` — the variable `Y = log(o/e)`
(`o = V^k − W`, `e = V^y − V^k`) is, in the clock `∫ o⁻²`, a diffusion `dY = b(Y) dT − √κ dB̃` with

  `b(Y) = b₋ + (b₊ − b₋)/(1 + e^{−Y})`,  `b₋ = S' + 2 − κ/2 < 0`,  `b₊ = S' + ρ_Y + 4 − κ/2 > 0`

(the limits (SS6): `b(−∞) = S' − c`, `b(+∞) = S_y − d`). This file is pure real analysis: it builds a bounded
Lyapunov function whose generator dominates the two-mark budget of `G12Det`.

With `Y₀ = log(−b₋/b₊)` the zero of `b`, `0 < α ≤ 1/2` and `κα ≤ min(b₊, −b₋)`:

  `h(Y) = −1/cosh(α(Y − Y₀))`,  `L h = (κ/2) h'' + b h' ≥ (κα²/2)/cosh(α(Y − Y₀))` (`lowGen_ge`),

because `b(Y₀ + z) = b₊(1 − e^{−z})/(1 + (b₊/(−b₋)) e^{−z})` has the sign of `z` and `|b| ≥ min(b₊, −b₋) |tanh(z/2)|`
(`lowDrift_mul_ge`). Moreover `h'² ≤ α²/cosh(α(Y − Y₀))` (`sq_lowH1_le`) and `|h| ≤ 1` (`abs_lowH_le`). The budget
`β = 4e/(u²o) + 4e/u³` (`u = o + e`) satisfies `β o² ≤ 2/cosh²(Y/2)` (`budget_le_cosh`), and
`cosh(α(Y − Y₀)) ≤ 2 cosh(Y₀/2) cosh²(Y/2)` (`cosh_alpha_le`), so `β ≤ c₃ (L h)/o²` (`budget_le_lowGen`). Finally
`(L h)/o² − h' D/o ≥ (L h)/(2o²) − D²/κ` for every real `D` (`lowGen_sub_ge`), which absorbs the drift difference of the
actual word into its energy.
-/

set_option autoImplicit false

noncomputable section

open Real

namespace InteractingSLE

namespace Supp7

namespace G12Low

/-! ### Definitions -/

/-- The drift `b(Y) = b₋ + (b₊ − b₋)/(1 + e^{−Y})` of `Y = log(o/e)` under the two-mark reference. -/
def lowDrift (bm bp Y : ℝ) : ℝ := bm + (bp - bm) / (1 + exp (-Y))

/-- The zero `Y₀ = log(−b₋/b₊)` of the drift. -/
def lowY0 (bm bp : ℝ) : ℝ := log (-bm / bp)

/-- The Lyapunov function `h(Y) = −1/cosh(α(Y − Y₀))`. -/
def lowH (α Y₀ Y : ℝ) : ℝ := -(cosh (α * (Y - Y₀)))⁻¹

/-- `h' = α sinh/cosh²`. -/
def lowH1 (α Y₀ Y : ℝ) : ℝ := α * sinh (α * (Y - Y₀)) / cosh (α * (Y - Y₀)) ^ 2

/-- `h'' = α² (cosh² − 2 sinh²)/cosh³`. -/
def lowH2 (α Y₀ Y : ℝ) : ℝ :=
  α ^ 2 * (cosh (α * (Y - Y₀)) ^ 2 - 2 * sinh (α * (Y - Y₀)) ^ 2) / cosh (α * (Y - Y₀)) ^ 3

/-- The generator `L h = (κ/2) h'' + b h'`. -/
def lowGen (κ bm bp α Y₀ Y : ℝ) : ℝ := κ / 2 * lowH2 α Y₀ Y + lowDrift bm bp Y * lowH1 α Y₀ Y

/-! ### Derivatives and bounds of `h` -/

theorem hasDerivAt_cosh_lin (α Y₀ Y : ℝ) :
    HasDerivAt (fun Y => cosh (α * (Y - Y₀))) (sinh (α * (Y - Y₀)) * α) Y := by
  have h1 : HasDerivAt (fun Y : ℝ => α * (Y - Y₀)) α Y := by
    simpa using ((hasDerivAt_id Y).sub_const Y₀).const_mul α
  exact (hasDerivAt_cosh _).comp Y h1

theorem hasDerivAt_sinh_lin (α Y₀ Y : ℝ) :
    HasDerivAt (fun Y => sinh (α * (Y - Y₀))) (cosh (α * (Y - Y₀)) * α) Y := by
  have h1 : HasDerivAt (fun Y : ℝ => α * (Y - Y₀)) α Y := by
    simpa using ((hasDerivAt_id Y).sub_const Y₀).const_mul α
  exact (hasDerivAt_sinh _).comp Y h1

theorem hasDerivAt_lowH (α Y₀ Y : ℝ) : HasDerivAt (lowH α Y₀) (lowH1 α Y₀ Y) Y := by
  have h := ((hasDerivAt_cosh_lin α Y₀ Y).inv (cosh_pos _).ne').neg
  refine h.congr_deriv ?_
  unfold lowH1
  ring

theorem hasDerivAt_lowH1 (α Y₀ Y : ℝ) : HasDerivAt (lowH1 α Y₀) (lowH2 α Y₀ Y) Y := by
  have hs := (hasDerivAt_sinh_lin α Y₀ Y).const_mul α
  have hc := (hasDerivAt_cosh_lin α Y₀ Y).pow 2
  have hne : cosh (α * (Y - Y₀)) ^ 2 ≠ 0 := pow_ne_zero 2 (cosh_pos _).ne'
  have h := hs.div hc hne
  have hc0 : cosh (α * (Y - Y₀)) ≠ 0 := (cosh_pos _).ne'
  refine h.congr_deriv ?_
  unfold lowH2
  norm_num
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

theorem continuous_lowH1 (α Y₀ : ℝ) : Continuous (lowH1 α Y₀) :=
  continuous_iff_continuousAt.2 fun Y => (hasDerivAt_lowH1 α Y₀ Y).continuousAt

theorem continuous_lowH2 (α Y₀ : ℝ) : Continuous (lowH2 α Y₀) := by
  unfold lowH2
  exact Continuous.div (by fun_prop) (by fun_prop) fun Y => pow_ne_zero 3 (cosh_pos _).ne'

theorem contDiff_lowH {n : WithTop ℕ∞} (α Y₀ : ℝ) : ContDiff ℝ n (lowH α Y₀) := by
  unfold lowH
  have h : ContDiff ℝ n fun Y : ℝ => cosh (α * (Y - Y₀)) := contDiff_cosh.comp (by fun_prop)
  exact (h.inv fun Y => (cosh_pos _).ne').neg

theorem abs_lowH_le (α Y₀ Y : ℝ) : |lowH α Y₀ Y| ≤ 1 := by
  unfold lowH
  rw [abs_neg, abs_inv, abs_of_pos (cosh_pos _)]
  exact inv_le_one_of_one_le₀ (one_le_cosh _)

/-- `h'² ≤ α²/cosh(α(Y − Y₀))`. -/
theorem sq_lowH1_le (α Y₀ Y : ℝ) : lowH1 α Y₀ Y ^ 2 ≤ α ^ 2 / cosh (α * (Y - Y₀)) := by
  set c := cosh (α * (Y - Y₀)) with hc
  set s := sinh (α * (Y - Y₀)) with hs
  have hc1 : 1 ≤ c := one_le_cosh _
  have hc0 : 0 < c := cosh_pos _
  have hcs : c ^ 2 = s ^ 2 + 1 := cosh_sq _
  unfold lowH1
  rw [← hc, ← hs, div_pow, div_le_div_iff₀ (by positivity) hc0]
  have hs2 : s ^ 2 ≤ c ^ 2 := by linarith
  have ha : 0 ≤ α ^ 2 := sq_nonneg α
  have h1 : (α * s) ^ 2 * c ≤ α ^ 2 * c ^ 3 := by
    have : (α * s) ^ 2 * c = α ^ 2 * (s ^ 2 * c) := by ring
    rw [this, show α ^ 2 * c ^ 3 = α ^ 2 * (c ^ 2 * c) by ring]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hs2 hc0.le) ha
  have h2 : α ^ 2 * c ^ 3 ≤ α ^ 2 * (c ^ 2) ^ 2 := by
    refine mul_le_mul_of_nonneg_left ?_ ha
    have : c ^ 3 = c ^ 2 * c := by ring
    rw [this, show (c ^ 2) ^ 2 = c ^ 2 * c ^ 2 by ring]
    exact mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
  linarith

/-! ### The drift has the sign of `Y − Y₀` -/

theorem exp_neg_lowY0 {bm bp : ℝ} (hbm : bm < 0) (hbp : 0 < bp) : exp (-lowY0 bm bp) = bp / -bm := by
  unfold lowY0
  rw [exp_neg, exp_log (div_pos (neg_pos.2 hbm) hbp), inv_div]

/-- `b(Y₀ + z) = b₊(1 − e^{−z})/(1 + r e^{−z})`, `r = b₊/(−b₋)`. -/
theorem lowDrift_eq {bm bp : ℝ} (hbm : bm < 0) (hbp : 0 < bp) (z : ℝ) :
    lowDrift bm bp (lowY0 bm bp + z) = bp * (1 - exp (-z)) / (1 + bp / -bm * exp (-z)) := by
  unfold lowDrift
  rw [neg_add, exp_add, exp_neg_lowY0 hbm hbp]
  have hr : 0 < bp / -bm := div_pos hbp (neg_pos.2 hbm)
  have hden : 1 + bp / -bm * exp (-z) ≠ 0 := by positivity
  have hrel : bm * (bp / -bm) = -bp := by
    have hbm' : bm ≠ 0 := hbm.ne
    field_simp
  rw [eq_div_iff hden, add_mul, div_mul_cancel₀ _ hden]
  linear_combination (exp (-z)) * hrel

/-- **The sign of the drift**: `b · sinh · cosh ≥ m sinh²` at `α(Y − Y₀)`, for `m ≤ min(b₊, −b₋)` and
`0 ≤ α ≤ 1/2`. -/
theorem lowDrift_mul_ge {bm bp m α : ℝ} (hbm : bm < 0) (hbp : 0 < bp) (hmp : m ≤ bp)
    (hmm : m ≤ -bm) (hα0 : 0 ≤ α) (hα : α ≤ 1 / 2) (Y : ℝ) :
    m * sinh (α * (Y - lowY0 bm bp)) ^ 2 ≤
      lowDrift bm bp Y * sinh (α * (Y - lowY0 bm bp)) * cosh (α * (Y - lowY0 bm bp)) := by
  set z := Y - lowY0 bm bp with hz
  have hY : Y = lowY0 bm bp + z := by rw [hz]; ring
  rw [hY, lowDrift_eq hbm hbp z]
  set r := bp / -bm with hr
  have hr0 : 0 < r := div_pos hbp (neg_pos.2 hbm)
  set E := exp (-z) with hE
  have hE0 : 0 < E := exp_pos _
  set a := exp (α * z) with ha
  have ha0 : 0 < a := exp_pos _
  have hsinh : sinh (α * z) = (a - a⁻¹) / 2 := by rw [sinh_eq, ha, exp_neg]
  have hcosh : cosh (α * z) = (a + a⁻¹) / 2 := by rw [cosh_eq, ha, exp_neg]
  rw [hsinh, hcosh]
  -- `m (1 + r E) ≤ b₊ (1 + E)`
  have hmr : m * r ≤ bp := by
    rw [hr, mul_div_assoc']
    rw [div_le_iff₀ (neg_pos.2 hbm)]
    nlinarith
  have hkey : m * (1 + r * E) ≤ bp * (1 + E) := by nlinarith
  -- `E a² = e^{(2α − 1) z}`
  have hEa : E * a ^ 2 = exp ((2 * α - 1) * z) := by
    rw [hE, ha, ← exp_nat_mul, ← exp_add]
    congr 1
    push_cast
    ring
  have hden : 0 < 1 + r * E := by positivity
  have hid : bp * (1 - E) / (1 + r * E) * ((a - a⁻¹) / 2) * ((a + a⁻¹) / 2) - m * ((a - a⁻¹) / 2) ^ 2 =
      (a ^ 2 - 1) / (4 * a ^ 2 * (1 + r * E)) *
        (bp * (1 - E) * (a ^ 2 + 1) - m * (a ^ 2 - 1) * (1 + r * E)) := by
    field_simp
    ring
  rw [← sub_nonneg, hid]
  rcases le_total 0 z with hz0 | hz0
  · -- `z ≥ 0`: `a ≥ 1`, `E a² ≤ 1`
    have ha1 : 1 ≤ a := one_le_exp (mul_nonneg hα0 hz0)
    have hEa1 : E * a ^ 2 ≤ 1 := by
      rw [hEa]; exact exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg (by linarith) hz0)
    have ha2 : 0 ≤ a ^ 2 - 1 := by nlinarith
    have h1 : m * (1 + r * E) * (a ^ 2 - 1) ≤ bp * (1 + E) * (a ^ 2 - 1) :=
      mul_le_mul_of_nonneg_right hkey ha2
    have h2 : bp * (1 + E) * (a ^ 2 - 1) ≤ bp * (1 - E) * (a ^ 2 + 1) := by
      have : bp * (1 - E) * (a ^ 2 + 1) - bp * (1 + E) * (a ^ 2 - 1) = 2 * bp * (1 - E * a ^ 2) := by ring
      have : 0 ≤ 2 * bp * (1 - E * a ^ 2) := mul_nonneg (by positivity) (by linarith)
      linarith
    have hb : 0 ≤ bp * (1 - E) * (a ^ 2 + 1) - m * (a ^ 2 - 1) * (1 + r * E) := by
      have : m * (a ^ 2 - 1) * (1 + r * E) = m * (1 + r * E) * (a ^ 2 - 1) := by ring
      linarith
    exact mul_nonneg (div_nonneg ha2 (by positivity)) hb
  · -- `z ≤ 0`: `a ≤ 1`, `E a² ≥ 1`
    have ha1 : a ≤ 1 := exp_le_one_iff.2 (mul_nonpos_of_nonneg_of_nonpos hα0 hz0)
    have hEa1 : 1 ≤ E * a ^ 2 := by
      rw [hEa]; exact one_le_exp (mul_nonneg_of_nonpos_of_nonpos (by linarith) hz0)
    have ha2 : a ^ 2 - 1 ≤ 0 := by nlinarith
    have h1 : bp * (1 + E) * (a ^ 2 - 1) ≤ m * (1 + r * E) * (a ^ 2 - 1) :=
      mul_le_mul_of_nonpos_right hkey ha2
    have h2 : bp * (1 - E) * (a ^ 2 + 1) ≤ bp * (1 + E) * (a ^ 2 - 1) := by
      have : bp * (1 + E) * (a ^ 2 - 1) - bp * (1 - E) * (a ^ 2 + 1) = 2 * bp * (E * a ^ 2 - 1) := by ring
      have : 0 ≤ 2 * bp * (E * a ^ 2 - 1) := mul_nonneg (by positivity) (by linarith)
      linarith
    have hb : bp * (1 - E) * (a ^ 2 + 1) - m * (a ^ 2 - 1) * (1 + r * E) ≤ 0 := by
      have : m * (a ^ 2 - 1) * (1 + r * E) = m * (1 + r * E) * (a ^ 2 - 1) := by ring
      linarith
    exact mul_nonneg_of_nonpos_of_nonpos (div_nonpos_of_nonpos_of_nonneg ha2 (by positivity)) hb

/-! ### The generator bound -/

/-- **The generator bound** `L h ≥ (κα²/2)/cosh(α(Y − Y₀))` for `0 < α ≤ 1/2`, `κα ≤ min(b₊, −b₋)`. -/
theorem lowGen_ge {κ bm bp α : ℝ} (hbm : bm < 0) (hbp : 0 < bp) (hα0 : 0 < α) (hα : α ≤ 1 / 2)
    (hαp : κ * α ≤ bp) (hαm : κ * α ≤ -bm) (Y : ℝ) :
    κ * α ^ 2 / 2 / cosh (α * (Y - lowY0 bm bp)) ≤ lowGen κ bm bp α (lowY0 bm bp) Y := by
  have hkey := lowDrift_mul_ge hbm hbp hαp hαm hα0.le hα Y
  set c := cosh (α * (Y - lowY0 bm bp)) with hc
  set s := sinh (α * (Y - lowY0 bm bp)) with hs
  set b := lowDrift bm bp Y with hb
  have hc0 : 0 < c := cosh_pos _
  unfold lowGen lowH2 lowH1
  rw [← hc, ← hs, ← hb]
  have e : κ / 2 * (α ^ 2 * (c ^ 2 - 2 * s ^ 2) / c ^ 3) + b * (α * s / c ^ 2) =
      κ * α ^ 2 / 2 / c + α * (b * s * c - κ * α * s ^ 2) / c ^ 3 := by
    field_simp
    ring
  rw [e]
  have : 0 ≤ α * (b * s * c - κ * α * s ^ 2) / c ^ 3 := by
    refine div_nonneg (mul_nonneg hα0.le ?_) (by positivity)
    linarith
  linarith

/-- `h'² ≤ (2/κ) L h`. -/
theorem sq_lowH1_le_lowGen {κ bm bp α : ℝ} (hbm : bm < 0) (hbp : 0 < bp) (hα0 : 0 < α) (hα : α ≤ 1 / 2)
    (hκ : 0 < κ) (hαp : κ * α ≤ bp) (hαm : κ * α ≤ -bm) (Y : ℝ) :
    lowH1 α (lowY0 bm bp) Y ^ 2 ≤ 2 / κ * lowGen κ bm bp α (lowY0 bm bp) Y := by
  refine (sq_lowH1_le α _ Y).trans ?_
  have h := lowGen_ge hbm hbp hα0 hα hαp hαm Y
  have e : α ^ 2 / cosh (α * (Y - lowY0 bm bp)) =
      2 / κ * (κ * α ^ 2 / 2 / cosh (α * (Y - lowY0 bm bp))) := by
    field_simp
  rw [e]
  exact mul_le_mul_of_nonneg_left h (by positivity)

/-- **Absorbing the drift difference**: `(L h)/o² − h' D/o ≥ (L h)/(2o²) − D²/κ`. -/
theorem lowGen_sub_ge {κ bm bp α : ℝ} (hbm : bm < 0) (hbp : 0 < bp) (hα0 : 0 < α) (hα : α ≤ 1 / 2)
    (hκ : 0 < κ) (hαp : κ * α ≤ bp) (hαm : κ * α ≤ -bm) (Y : ℝ) {o : ℝ} (ho : 0 < o) (D : ℝ) :
    lowGen κ bm bp α (lowY0 bm bp) Y / (2 * o ^ 2) - D ^ 2 / κ ≤
      lowGen κ bm bp α (lowY0 bm bp) Y / o ^ 2 - lowH1 α (lowY0 bm bp) Y * D / o := by
  set G := lowGen κ bm bp α (lowY0 bm bp) Y
  set x := lowH1 α (lowY0 bm bp) Y
  have hx := sq_lowH1_le_lowGen hbm hbp hα0 hα hκ hαp hαm Y
  have hsq : 0 ≤ (Real.sqrt κ * x / (2 * o) - D / Real.sqrt κ) ^ 2 := sq_nonneg _
  have hs : Real.sqrt κ ^ 2 = κ := Real.sq_sqrt hκ.le
  have hs0 : 0 < Real.sqrt κ := Real.sqrt_pos.2 hκ
  have hamgm : x * D / o ≤ κ / 4 * (x ^ 2 / o ^ 2) + D ^ 2 / κ := by
    have e : (Real.sqrt κ * x / (2 * o) - D / Real.sqrt κ) ^ 2 =
        κ / 4 * (x ^ 2 / o ^ 2) + D ^ 2 / κ - x * D / o := by
      field_simp
      rw [hs]
      ring
    linarith
  have h2 : κ / 4 * (x ^ 2 / o ^ 2) ≤ G / (2 * o ^ 2) := by
    have : κ / 4 * (x ^ 2 / o ^ 2) ≤ κ / 4 * (2 / κ * G / o ^ 2) :=
      mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hx (sq_nonneg o)) (by positivity)
    refine this.trans (le_of_eq ?_)
    field_simp
    ring
  have h3 : G / o ^ 2 = G / (2 * o ^ 2) + G / (2 * o ^ 2) := by field_simp; ring
  linarith

/-! ### The budget against the generator -/

/-- `cosh(α(Y − Y₀)) ≤ 2 cosh(Y₀/2) cosh²(Y/2)` for `0 ≤ α ≤ 1/2`. -/
theorem cosh_alpha_le {α : ℝ} (hα0 : 0 ≤ α) (hα : α ≤ 1 / 2) (Y₀ Y : ℝ) :
    cosh (α * (Y - Y₀)) ≤ 2 * cosh (Y₀ / 2) * cosh (Y / 2) ^ 2 := by
  have h1 : |α * (Y - Y₀)| ≤ |Y / 2| + |Y₀ / 2| := by
    rw [abs_mul, abs_of_nonneg hα0, abs_div, abs_div, abs_two]
    have := abs_sub Y Y₀
    have h3 : α * |Y - Y₀| ≤ 1 / 2 * |Y - Y₀| := mul_le_mul_of_nonneg_right hα (abs_nonneg _)
    linarith
  have h2 : cosh (α * (Y - Y₀)) ≤ cosh (|Y / 2| + |Y₀ / 2|) := by
    rw [cosh_le_cosh, abs_of_nonneg (add_nonneg (abs_nonneg (Y / 2)) (abs_nonneg (Y₀ / 2)))]
    exact h1
  have h3 : cosh (|Y / 2| + |Y₀ / 2|) ≤ 2 * cosh (Y₀ / 2) * cosh (Y / 2) := by
    rw [cosh_add, cosh_abs, cosh_abs]
    have ha := sinh_lt_cosh (x := |Y / 2|)
    have hb := sinh_lt_cosh (x := |Y₀ / 2|)
    have ha0 : 0 ≤ sinh |Y / 2| := sinh_nonneg_iff.2 (abs_nonneg _)
    have hb0 : 0 ≤ sinh |Y₀ / 2| := sinh_nonneg_iff.2 (abs_nonneg _)
    rw [cosh_abs] at ha hb
    have : sinh |Y / 2| * sinh |Y₀ / 2| ≤ cosh (Y / 2) * cosh (Y₀ / 2) :=
      mul_le_mul ha.le hb.le hb0 (cosh_pos _).le
    linarith
  have h4 : cosh (Y / 2) ≤ cosh (Y / 2) ^ 2 := by
    have := one_le_cosh (Y / 2)
    nlinarith
  calc cosh (α * (Y - Y₀)) ≤ 2 * cosh (Y₀ / 2) * cosh (Y / 2) := h2.trans h3
    _ ≤ 2 * cosh (Y₀ / 2) * cosh (Y / 2) ^ 2 :=
        mul_le_mul_of_nonneg_left h4 (by positivity)

/-- `cosh²(Y/2) = (o + e)²/(4oe)` for `Y = log o − log e`. -/
theorem cosh_half_sq {o e : ℝ} (ho : 0 < o) (he : 0 < e) :
    cosh ((log o - log e) / 2) ^ 2 = (o + e) ^ 2 / (4 * o * e) := by
  have h1 : cosh (log o - log e) = (o / e + (o / e)⁻¹) / 2 := by
    rw [← log_div ho.ne' he.ne', cosh_log (div_pos ho he)]
  have h2 : cosh (log o - log e) = 2 * cosh ((log o - log e) / 2) ^ 2 - 1 := by
    have := cosh_two_mul ((log o - log e) / 2)
    rw [show 2 * ((log o - log e) / 2) = log o - log e by ring] at this
    rw [this, sinh_sq]
    ring
  have h3 : cosh ((log o - log e) / 2) ^ 2 = (cosh (log o - log e) + 1) / 2 := by linarith
  rw [h3, h1]
  field_simp
  ring

/-- **The budget in the clock of `o`**: `(4e/(u²o) + 4e/u³) o² ≤ 2/cosh²(Y/2)`, `u = o + e`. -/
theorem budget_le_cosh {o e : ℝ} (ho : 0 < o) (he : 0 < e) :
    4 * e / ((o + e) ^ 2 * o) + 4 * e / (o + e) ^ 3 ≤
      2 / (o ^ 2 * cosh ((log o - log e) / 2) ^ 2) := by
  rw [cosh_half_sq ho he]
  have hu : 0 < o + e := by linarith
  have h1 : 4 * e / (o + e) ^ 3 ≤ 4 * e / ((o + e) ^ 2 * o) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have : (o + e) ^ 2 * o ≤ (o + e) ^ 3 := by
      rw [pow_succ]; exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    exact mul_le_mul_of_nonneg_left this (by positivity)
  have h2 : 4 * e / ((o + e) ^ 2 * o) + 4 * e / ((o + e) ^ 2 * o) =
      2 / (o ^ 2 * ((o + e) ^ 2 / (4 * o * e))) := by
    field_simp
    ring
  linarith

/-- **The budget against the generator**: `4e/(u²o) + 4e/u³ ≤ c₃ (L h)(Y)/o²` with
`c₃ = 8 cosh(Y₀/2)/(κα²)`. -/
theorem budget_le_lowGen {κ bm bp α : ℝ} (hbm : bm < 0) (hbp : 0 < bp) (hα0 : 0 < α) (hα : α ≤ 1 / 2)
    (hκ : 0 < κ) (hαp : κ * α ≤ bp) (hαm : κ * α ≤ -bm) {o e : ℝ} (ho : 0 < o) (he : 0 < e) :
    4 * e / ((o + e) ^ 2 * o) + 4 * e / (o + e) ^ 3 ≤
      8 * cosh (lowY0 bm bp / 2) / (κ * α ^ 2) *
        (lowGen κ bm bp α (lowY0 bm bp) (log o - log e) / o ^ 2) := by
  set Y := log o - log e
  set Y₀ := lowY0 bm bp
  refine (budget_le_cosh ho he).trans ?_
  have hG := lowGen_ge hbm hbp hα0 hα hαp hαm Y
  have hC := cosh_alpha_le hα0.le hα Y₀ Y
  have hc0 : 0 < cosh (α * (Y - Y₀)) := cosh_pos _
  have hcY : 0 < cosh (Y / 2) := cosh_pos _
  have hcY₀ : 0 < cosh (Y₀ / 2) := cosh_pos _
  -- `2/(o² cosh²(Y/2)) ≤ 4 cosh(Y₀/2)/(o² cosh(α(Y − Y₀)))`
  have h1 : 2 / (o ^ 2 * cosh (Y / 2) ^ 2) ≤ 4 * cosh (Y₀ / 2) / (o ^ 2 * cosh (α * (Y - Y₀))) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_le_mul_of_nonneg_left hC (show (0 : ℝ) ≤ 2 * o ^ 2 by positivity)
    nlinarith
  refine h1.trans ?_
  have e : 4 * cosh (Y₀ / 2) / (o ^ 2 * cosh (α * (Y - Y₀))) =
      8 * cosh (Y₀ / 2) / (κ * α ^ 2) * (κ * α ^ 2 / 2 / cosh (α * (Y - Y₀)) / o ^ 2) := by
    field_simp
    ring
  rw [e]
  refine mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hG (sq_nonneg o)) (by positivity)

end G12Low

end Supp7

end InteractingSLE
