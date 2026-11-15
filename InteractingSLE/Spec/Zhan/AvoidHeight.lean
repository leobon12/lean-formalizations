/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Foundations.SLE.SpaceFilling.SwallowBoundary
import InteractingSLE.Spec.Sec4.Prob41Avoid
import QuantumZipper.Proofs.Thm11.ForwardClock

/-!
# The strip height bound in half-plane coordinates (deterministic)

Packet PROVE-ZHAN-B. Astra, *Formalization proofs and dependency audit* (`source/external/AstraIG1/`,
text dump L1312–1381), §3 "Simplicity and the strip height bound" (3.20) and the last step of
"Uniform avoidance of compact real intervals" (ruling R35).

The strip chart of the avoidance lemma sends two real points `r₊ < r₋ < 0` to the ends of the strip
`{0 < Im < π}` and `0` to `0`. Everything it uses is explicit in half-plane coordinates, so no strip
Loewner theory is needed here. Let `W` be a continuous driver, `f_t = g_t(z) − W_t` the centred flow of
a point `z ∈ ℍ`, and `a_t = g_t(r₋) − W_t`, `c_t = g_t(r₊) − W_t` the centred flows of the two real
points, with `c_t < a_t < 0`. Then:

* the **strip height** of `g_t(z)` is the angle `Y_t = arg(f_t − a_t) − arg(f_t − c_t) ∈ (0, π)` under
  which the segment `[c_t, a_t]` is seen from `f_t` (the strip image of `[r₊, r₋]` is the upper
  boundary). `f_t − a_t = g_t(z) − g_t(r₋)` involves no driving noise, so `Y` is differentiable:
  `Y' = p_t · Im(2/f_t)` with `p_t = 1/c_t − 1/a_t > 0`;
* the **strip clock** is `s(t) = ∫₀ᵗ p²`;
* **(3.20)**: `G_t = cos²(Y_t/2) = (1 + cos Y_t)/2` satisfies `G' ≤ p² G`
  (`hasDerivWithinAt_heightCos`, `heightCos_deriv_le`; the strip inequality `Y' ≥ −cot(Y/2)` per unit
  strip time, equivalent to the elementary `2uv y² ≤ |f|² (|P| + Re P)` of `two_mul_mul_sq_le`), hence
  `G_t ≤ G_0 e^{s(t)}` (Grönwall, `heightCos_le`);
* **never swallowed** (`swallowTime_eq_top_of_heightCos`): if `G_0 e^{S} < 1` where `S` bounds the
  whole strip clock, then `Y` stays away from `0`, so `|f_t|` stays away from `0`, the Loewner clock
  `∫ 1/|f|²` stays bounded, and `z` is never swallowed.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology
open QuantumZipper QuantumZipper.RS
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Zhan

/-! ### Algebra -/

/-- **The strip height inequality, algebraic core.** For reals `u, v, x, y`, with `F = x² + y²`,
`X = F − (u + v) x + u v`, `Z = (u − v) y` and `N = √(X² + Z²)`: `2 u v y² ≤ F (N + X)`.
(`F²(X² + Z²) − (2uvy² − FX)² = y² ((u + v)F − 2uvx)²`.) -/
theorem two_mul_mul_sq_le (u v x y : ℝ) :
    2 * (u * v) * y ^ 2 ≤ (x ^ 2 + y ^ 2) *
      (Real.sqrt (((x ^ 2 + y ^ 2) - (u + v) * x + u * v) ^ 2 + ((u - v) * y) ^ 2) +
        ((x ^ 2 + y ^ 2) - (u + v) * x + u * v)) := by
  set F := x ^ 2 + y ^ 2 with hF
  set X := F - (u + v) * x + u * v with hX
  set Z := (u - v) * y with hZ
  have hF0 : 0 ≤ F := by positivity
  have hid : (F * Real.sqrt (X ^ 2 + Z ^ 2)) ^ 2 - (2 * (u * v) * y ^ 2 - F * X) ^ 2 =
      y ^ 2 * ((u + v) * F - 2 * (u * v) * x) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by positivity), hZ, hX, hF]
    ring
  have hle : 2 * (u * v) * y ^ 2 - F * X ≤ F * Real.sqrt (X ^ 2 + Z ^ 2) := by
    have h0 : 0 ≤ F * Real.sqrt (X ^ 2 + Z ^ 2) := mul_nonneg hF0 (Real.sqrt_nonneg _)
    refine le_trans (le_abs_self _) (abs_le_of_sq_le_sq' ?_ h0).2
    rw [sq_abs]
    nlinarith [mul_nonneg (sq_nonneg y) (sq_nonneg ((u + v) * F - 2 * (u * v) * x))]
  nlinarith

/-! ### The angle of `[c, a]` seen from `f` -/

/-- The product `(f − a)·conj(f − c)` for real `a, c`: real part `|f|² − (a + c) Re f + a c`,
imaginary part `(a − c) Im f`. -/
theorem re_mul_conj_sub (f : ℂ) (a c : ℝ) :
    ((f - a) * (starRingEnd ℂ) (f - c)).re = (f.re ^ 2 + f.im ^ 2) - (a + c) * f.re + a * c := by
  simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re, Complex.conj_re, Complex.sub_im,
    Complex.ofReal_im, Complex.conj_im, sub_zero]
  ring

theorem im_mul_conj_sub (f : ℂ) (a c : ℝ) :
    ((f - a) * (starRingEnd ℂ) (f - c)).im = (a - c) * f.im := by
  simp only [Complex.mul_im, Complex.sub_re, Complex.ofReal_re, Complex.conj_re, Complex.sub_im,
    Complex.ofReal_im, Complex.conj_im, sub_zero]
  ring

theorem norm_mul_conj_sub (f : ℂ) (a c : ℝ) :
    ‖f - a‖ * ‖f - c‖ = Real.sqrt (((f.re ^ 2 + f.im ^ 2) - (a + c) * f.re + a * c) ^ 2 +
      ((a - c) * f.im) ^ 2) := by
  rw [← re_mul_conj_sub, ← im_mul_conj_sub, ← Complex.norm_conj (f - c), ← norm_mul,
    Complex.norm_eq_sqrt_sq_add_sq]

/-- The cosine of the angle `arg(f − a) − arg(f − c)` (both points off the real line). -/
theorem cos_arg_sub_arg (f : ℂ) (a c : ℝ) (hf : 0 < f.im) :
    Real.cos (arg (f - a) - arg (f - c)) =
      ((f.re ^ 2 + f.im ^ 2) - (a + c) * f.re + a * c) / (‖f - a‖ * ‖f - c‖) := by
  have h1 : (f - a) ≠ 0 := fun h => by
    have := congrArg Complex.im h; simp at this; linarith
  have h2 : (f - c) ≠ 0 := fun h => by
    have := congrArg Complex.im h; simp at this; linarith
  rw [Real.cos_sub, Complex.cos_arg h1, Complex.cos_arg h2, Complex.sin_arg, Complex.sin_arg]
  have hn1 : ‖f - a‖ ≠ 0 := norm_ne_zero_iff.2 h1
  have hn2 : ‖f - c‖ ≠ 0 := norm_ne_zero_iff.2 h2
  field_simp
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero]
  ring

theorem sin_arg_sub_arg (f : ℂ) (a c : ℝ) (hf : 0 < f.im) :
    Real.sin (arg (f - a) - arg (f - c)) = (a - c) * f.im / (‖f - a‖ * ‖f - c‖) := by
  have h1 : (f - a) ≠ 0 := fun h => by
    have := congrArg Complex.im h; simp at this; linarith
  have h2 : (f - c) ≠ 0 := fun h => by
    have := congrArg Complex.im h; simp at this; linarith
  rw [Real.sin_sub, Complex.cos_arg h1, Complex.cos_arg h2, Complex.sin_arg, Complex.sin_arg]
  have hn1 : ‖f - a‖ ≠ 0 := norm_ne_zero_iff.2 h1
  have hn2 : ‖f - c‖ ≠ 0 := norm_ne_zero_iff.2 h2
  field_simp
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, sub_zero]
  ring

/-! ### The height along the flow -/

/-- The pure inequality behind `G' ≤ p² G`: with `F = x² + y²`, `X = F − (a + c)x + ac`, `N` as in
`two_mul_mul_sq_le` and `p = 1/c − 1/a`, `−sin Y · p · Im(2/f)/2 ≤ p² (1 + cos Y)/2` where
`sin Y = (a − c)y/N`, `cos Y = X/N`, `Im(2/f) = −2y/F`. -/
theorem heightCos_ineq (a c x y : ℝ) (ha : a < 0) (hc : c < 0) (hy : 0 < y) {N : ℝ} (hN : 0 < N)
    (hNeq : N = Real.sqrt (((x ^ 2 + y ^ 2) - (a + c) * x + a * c) ^ 2 + ((a - c) * y) ^ 2)) :
    -((a - c) * y / N * ((1 / c - 1 / a) * (-2 * y / (x ^ 2 + y ^ 2)))) / 2 ≤
      (1 / c - 1 / a) ^ 2 * ((1 + ((x ^ 2 + y ^ 2) - (a + c) * x + a * c) / N) / 2) := by
  have key := two_mul_mul_sq_le a c x y
  rw [← hNeq] at key
  have hF : 0 < x ^ 2 + y ^ 2 := by positivity
  have ha0 : a ≠ 0 := ha.ne
  have hc0 : c ≠ 0 := hc.ne
  have hp : (a - c) = (1 / c - 1 / a) * (a * c) := by field_simp
  rw [hp]
  set p := 1 / c - 1 / a
  set F := x ^ 2 + y ^ 2
  set X := F - (a + c) * x + a * c
  have hlhs : -(p * (a * c) * y / N * (p * (-2 * y / F))) / 2 =
      p ^ 2 * (a * c * y ^ 2) / (N * F) := by
    field_simp
  have hrhs : p ^ 2 * ((1 + X / N) / 2) = p ^ 2 * (F * (N + X)) / (2 * N * F) := by
    field_simp
  rw [hlhs, hrhs, div_le_div_iff₀ (by positivity) (by positivity)]
  have hm := mul_le_mul_of_nonneg_left key (by positivity : 0 ≤ p ^ 2 * N * F)
  nlinarith [hm]

section Flow

variable {W : ℝ → ℝ} {z : ℂ} {rm rp T : ℝ} {f ua uc : ℝ → ℂ}

/-- The strip height `Y_t = arg(f_t − a_t) − arg(f_t − c_t)` of `g_t(z)` relative to the images of
`r₋` (centred flow `a = ua`) and `r₊` (centred flow `c = uc`). -/
def stripHeight (f ua uc : ℝ → ℂ) (t : ℝ) : ℝ := arg (f t - ua t) - arg (f t - uc t)

/-- `G_t = cos²(Y_t/2) = (1 + cos Y_t)/2`. -/
def heightCos (f ua uc : ℝ → ℂ) (t : ℝ) : ℝ := (1 + Real.cos (stripHeight f ua uc t)) / 2

/-- The strip clock rate `p_t² = (1/c_t − 1/a_t)²`. -/
def stripRate (ua uc : ℝ → ℂ) (t : ℝ) : ℝ := (1 / (uc t).re - 1 / (ua t).re) ^ 2

theorem ofReal_re_of_isForwardSol (hW : Continuous W) {x : ℝ} {u : ℝ → ℂ}
    (hu : IsForwardSol W (x : ℂ) T u) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) : ((u t).re : ℂ) = u t := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  have him := im_isForwardSol_real hW hT hu t ht
  exact Complex.ext (by simp) (by simp [him])

/-- `g_t(z) − g_t(x) = f_t(z) − u_t(x)` has derivative `2/f − 2/u` (no driving noise). -/
theorem hasDerivWithinAt_sub_of_isForwardSol {x : ℂ} {u : ℝ → ℂ} (hf : IsForwardSol W z T f)
    (hu : IsForwardSol W x T u) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt (fun s => f s - u s) (2 / f t - 2 / u t) (Icc 0 T) t := by
  have h := (FwdHolo.hasDerivWithinAt_shift hf ht).sub (FwdHolo.hasDerivWithinAt_shift hu ht)
  have e : (fun s => f s - u s) = (fun s => f s + (W s : ℂ)) - (fun s => u s + (W s : ℂ)) := by
    funext r; simp only [Pi.sub_apply]; ring
  rw [e]; exact h

/-- The imaginary part of `log` of a point with positive imaginary part is differentiable along a
differentiable path. -/
theorem hasDerivWithinAt_arg {g : ℝ → ℂ} {g' : ℂ} {s : Set ℝ} {t : ℝ}
    (hg : HasDerivWithinAt g g' s t) (him : 0 < (g t).im) :
    HasDerivWithinAt (fun r => arg (g r)) (g' / g t).im s t := by
  have hslit : g t ∈ slitPlane := Or.inr him.ne'
  have hl := hg.clog_real hslit
  have hi := Complex.imCLM.hasFDerivAt.comp_hasDerivWithinAt t hl
  simp only [Function.comp_def, Complex.imCLM_apply, Complex.log_im] at hi
  exact hi

/-- The algebra of `Y'`: `(2/w − 2/a)/(w − a) − (2/w − 2/c)/(w − c) = (2/w)(1/c − 1/a)`. -/
theorem deriv_alg (w : ℂ) (a c : ℝ) (hw : w ≠ 0) (ha : a ≠ 0) (hc : c ≠ 0) (h1 : w - a ≠ 0)
    (h2 : w - c ≠ 0) :
    (2 / w - 2 / a) / (w - a) - (2 / w - 2 / c) / (w - c) = 2 / w * ((1 / c - 1 / a : ℝ) : ℂ) := by
  have ha' : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 ha
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc
  push_cast
  field_simp
  ring

theorem hasDerivWithinAt_stripHeight (hW : Continuous W) (hz : 0 < z.im)
    (hf : IsForwardSol W z T f) (ha : IsForwardSol W (rm : ℂ) T ua)
    (hc : IsForwardSol W (rp : ℂ) T uc) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt (stripHeight f ua uc) ((1 / (uc t).re - 1 / (ua t).re) * (2 / f t).im)
      (Icc 0 T) t := by
  have hfi : 0 < (f t).im := FwdClock.sol_im_pos hW hz hf ht
  have har := ofReal_re_of_isForwardSol hW ha ht
  have hcr := ofReal_re_of_isForwardSol hW hc ht
  have ha0 : ua t ≠ 0 := (ha.2 t ht).1
  have hc0 : uc t ≠ 0 := (hc.2 t ht).1
  have hf0 : f t ≠ 0 := (hf.2 t ht).1
  have h1i : 0 < (f t - ua t).im := by rw [← har]; simpa using hfi
  have h2i : 0 < (f t - uc t).im := by rw [← hcr]; simpa using hfi
  have h1 := hasDerivWithinAt_arg (hasDerivWithinAt_sub_of_isForwardSol hf ha ht) h1i
  have h2 := hasDerivWithinAt_arg (hasDerivWithinAt_sub_of_isForwardSol hf hc ht) h2i
  have hd := h1.sub h2
  refine hd.congr_deriv ?_
  have hne1 : f t - ((ua t).re : ℂ) ≠ 0 := fun h => by rw [har] at h; rw [h] at h1i; simp at h1i
  have hne2 : f t - ((uc t).re : ℂ) ≠ 0 := fun h => by rw [hcr] at h; rw [h] at h2i; simp at h2i
  have hre1 : (ua t).re ≠ 0 := fun h => ha0 (by rw [← har, h]; simp)
  have hre2 : (uc t).re ≠ 0 := fun h => hc0 (by rw [← hcr, h]; simp)
  have halg := deriv_alg (f t) (ua t).re (uc t).re hf0 hre1 hre2 hne1 hne2
  rw [har, hcr] at halg
  rw [← Complex.sub_im, halg, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, mul_zero,
    zero_add, mul_comm]

theorem hasDerivWithinAt_heightCos (hW : Continuous W) (hz : 0 < z.im)
    (hf : IsForwardSol W z T f) (ha : IsForwardSol W (rm : ℂ) T ua)
    (hc : IsForwardSol W (rp : ℂ) T uc) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    HasDerivWithinAt (heightCos f ua uc)
      (-(Real.sin (stripHeight f ua uc t) * ((1 / (uc t).re - 1 / (ua t).re) * (2 / f t).im)) / 2)
      (Icc 0 T) t := by
  have h := ((hasDerivWithinAt_stripHeight hW hz hf ha hc ht).cos.const_add 1).div_const 2
  refine h.congr_deriv ?_
  ring

/-- **(3.20), differential form**: `G' ≤ p² G` while `c_t < a_t < 0`. -/
theorem heightCos_deriv_le (hW : Continuous W) (hz : 0 < z.im)
    (hf : IsForwardSol W z T f) (ha : IsForwardSol W (rm : ℂ) T ua)
    (hc : IsForwardSol W (rp : ℂ) T uc) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T)
    (hca : (uc t).re < (ua t).re) (han : (ua t).re < 0) :
    -(Real.sin (stripHeight f ua uc t) * ((1 / (uc t).re - 1 / (ua t).re) * (2 / f t).im)) / 2 ≤
      stripRate ua uc t * heightCos f ua uc t := by
  have hfi : 0 < (f t).im := FwdClock.sol_im_pos hW hz hf ht
  have har := ofReal_re_of_isForwardSol hW ha ht
  have hcr := ofReal_re_of_isForwardSol hW hc ht
  set a := (ua t).re with hadef
  set c := (uc t).re with hcdef
  set w := f t with hwdef
  have hY : stripHeight f ua uc t = arg (w - a) - arg (w - c) := by
    simp only [stripHeight, hwdef, har, hcr]
  have hw1 : w - (a : ℂ) ≠ 0 := fun h => by
    have := congrArg Complex.im h; simp at this; linarith
  have hw2 : w - (c : ℂ) ≠ 0 := fun h => by
    have := congrArg Complex.im h; simp at this; linarith
  have hN : 0 < ‖w - a‖ * ‖w - c‖ := mul_pos (norm_pos_iff.2 hw1) (norm_pos_iff.2 hw2)
  have hNeq := norm_mul_conj_sub w a c
  have him2 : (2 / w).im = -2 * w.im / (w.re ^ 2 + w.im ^ 2) := by
    rw [FwdClock.im_two_div, Complex.sq_norm, Complex.normSq_apply]; ring_nf
  simp only [heightCos, stripRate, hY]
  rw [sin_arg_sub_arg w a c hfi, cos_arg_sub_arg w a c hfi, him2]
  exact heightCos_ineq a c w.re w.im han (hca.trans han) hfi hN hNeq

/-- The strip clock rate is continuous on `[0, T]`. -/
theorem continuousOn_stripRate (hW : Continuous W) (ha : IsForwardSol W (rm : ℂ) T ua)
    (hc : IsForwardSol W (rp : ℂ) T uc) : ContinuousOn (stripRate ua uc) (Icc 0 T) := by
  have hne : ∀ {x : ℝ} {u : ℝ → ℂ}, IsForwardSol W (x : ℂ) T u → ∀ s ∈ Icc (0 : ℝ) T,
      (u s).re ≠ 0 := fun {x u} hu s hs h => (hu.2 s hs).1 (by
        rw [← ofReal_re_of_isForwardSol hW hu hs, h]; simp)
  refine ((continuousOn_const.div (Complex.continuous_re.comp_continuousOn hc.1)
    (hne hc)).sub (continuousOn_const.div (Complex.continuous_re.comp_continuousOn ha.1)
    (hne ha))).pow 2

/-- **(3.20), integrated (Grönwall)**: `G_t ≤ G_0 e^{s(t)}` with `s(t) = ∫₀ᵗ p²`. -/
theorem heightCos_le (hW : Continuous W) (hz : 0 < z.im)
    (hf : IsForwardSol W z T f) (ha : IsForwardSol W (rm : ℂ) T ua)
    (hc : IsForwardSol W (rp : ℂ) T uc)
    (hord : ∀ t ∈ Icc (0 : ℝ) T, (uc t).re < (ua t).re ∧ (ua t).re < 0) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) :
    heightCos f ua uc t ≤
      heightCos f ua uc 0 * Real.exp (∫ s in (0 : ℝ)..t, stripRate ua uc s) := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  set I : ℝ → ℝ := fun τ => ∫ s in (0 : ℝ)..τ, stripRate ua uc s with hIdef
  set H : ℝ → ℝ := fun τ => heightCos f ua uc τ * Real.exp (-I τ) with hHdef
  have hd : ∀ τ ∈ Icc (0 : ℝ) T, HasDerivWithinAt H
      (-(Real.sin (stripHeight f ua uc τ) * ((1 / (uc τ).re - 1 / (ua τ).re) * (2 / f τ).im)) / 2 *
        Real.exp (-I τ) + heightCos f ua uc τ * (Real.exp (-I τ) * -stripRate ua uc τ))
      (Icc 0 T) τ := by
    intro τ hτ
    have hI := FwdClock.hasDerivWithinAt_integral_Icc (continuousOn_stripRate hW ha hc) hτ
    exact (hasDerivWithinAt_heightCos hW hz hf ha hc hτ).mul hI.neg.exp
  have hanti := FwdClock.antitoneOn_Icc_of_hasDerivWithinAt hd fun τ hτ => by
    have hτ' := Ioo_subset_Icc_self hτ
    have hle := heightCos_deriv_le hW hz hf ha hc hτ' (hord τ hτ').1 (hord τ hτ').2
    have he := Real.exp_pos (-I τ)
    nlinarith
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
  have hle := hanti h0 ht ht.1
  simp only [hHdef, hIdef, intervalIntegral.integral_same, neg_zero, Real.exp_zero, mul_one] at hle
  have he := Real.exp_pos (I t)
  calc heightCos f ua uc t = heightCos f ua uc t * Real.exp (-I t) * Real.exp (I t) := by
        rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
    _ ≤ heightCos f ua uc 0 * Real.exp (I t) := mul_le_mul_of_nonneg_right hle he.le

/-! ### Real flows keep their sign and order -/

/-- The centred flow of a real point `x < 0` stays negative (if `W 0 = 0`). -/
theorem re_neg_of_isForwardSol (hW : Continuous W) (hW0 : W 0 = 0) {x : ℝ} (hx : x < 0)
    {u : ℝ → ℂ} (hu : IsForwardSol W (x : ℂ) T u) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) :
    (u t).re < 0 := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  by_contra hpos
  push Not at hpos
  have hc : ContinuousOn (fun s => (u s).re) (Icc 0 t) :=
    (Complex.continuous_re.comp_continuousOn hu.1).mono (Icc_subset_Icc_right ht.2)
  have h0 : (u 0).re = x := by
    have := (hu.2 0 ⟨le_rfl, hT⟩).2
    rw [this, intervalIntegral.integral_same, hW0]; simp
  obtain ⟨s, hs, hs0⟩ := intermediate_value_Icc ht.1 hc ⟨by rw [h0]; exact hx.le, hpos⟩
  have hs' : s ∈ Icc (0 : ℝ) T := ⟨hs.1, hs.2.trans ht.2⟩
  have hs0' : (u s).re = 0 := hs0
  exact (hu.2 s hs').1 (by rw [← ofReal_re_of_isForwardSol hW hu hs', hs0']; simp)

/-- Two real flows keep their order strictly: `x < y` gives `u_x(t) < u_y(t)` (their difference
solves the linear equation `d' = −2d/(u_x u_y)`). -/
theorem re_lt_re_of_isForwardSol (hW : Continuous W) {x y : ℝ} (hxy : x < y) {ux uy : ℝ → ℂ}
    (hux : IsForwardSol W (x : ℂ) T ux) (huy : IsForwardSol W (y : ℂ) T uy) {t : ℝ}
    (ht : t ∈ Icc (0 : ℝ) T) : (ux t).re < (uy t).re := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hne : ∀ {v : ℝ} {u : ℝ → ℂ}, IsForwardSol W (v : ℂ) T u → ∀ s ∈ Icc (0 : ℝ) T,
      (u s).re ≠ 0 := fun {v u} hu s hs h => (hu.2 s hs).1 (by
        rw [← ofReal_re_of_isForwardSol hW hu hs, h]; simp)
  set q : ℝ → ℝ := fun s => 2 / ((ux s).re * (uy s).re) with hq
  have hqc : ContinuousOn q (Icc 0 T) :=
    continuousOn_const.div ((Complex.continuous_re.comp_continuousOn hux.1).mul
      (Complex.continuous_re.comp_continuousOn huy.1)) fun s hs => mul_ne_zero (hne hux s hs)
      (hne huy s hs)
  set E : ℝ → ℝ := fun s => ((uy s).re - (ux s).re) * Real.exp (∫ r in (0 : ℝ)..s, q r) with hE
  have hd : ∀ s ∈ Icc (0 : ℝ) T, HasDerivWithinAt E 0 (Icc 0 T) s := by
    intro s hs
    have h1 := Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt s
      (hasDerivWithinAt_sub_of_isForwardSol huy hux hs)
    have h2 := (FwdClock.hasDerivWithinAt_integral_Icc hqc hs).exp
    have h3 := h1.mul h2
    refine h3.congr_deriv ?_
    have hx0 := hne hux s hs
    have hy0 := hne huy s hs
    have k : ∀ {v : ℝ} {u : ℝ → ℂ}, IsForwardSol W (v : ℂ) T u → (2 / u s).re = 2 / (u s).re :=
      fun {v u} hu => by
        conv_lhs => rw [← ofReal_re_of_isForwardSol hW hu hs]
        rw [show (2 : ℂ) / ((u s).re : ℂ) = ((2 / (u s).re : ℝ) : ℂ) by push_cast; ring,
          Complex.ofReal_re]
    simp only [Function.comp_apply, Complex.reCLM_apply, Complex.sub_re, k hux, k huy, hq]
    field_simp
    ring
  have hmono := FwdClock.monotoneOn_Icc_of_hasDerivWithinAt hd (fun _ _ => le_rfl)
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
  have hle := hmono h0 ht ht.1
  have hE0 : E 0 = y - x := by
    simp only [hE, intervalIntegral.integral_same, Real.exp_zero, mul_one]
    rw [(huy.2 0 h0).2, (hux.2 0 h0).2, intervalIntegral.integral_same,
      intervalIntegral.integral_same]
    simp
  rw [hE0] at hle
  have hpos : 0 < E t := lt_of_lt_of_le (by linarith) hle
  simp only [hE] at hpos
  have := (mul_pos_iff_of_pos_right (Real.exp_pos _)).1 hpos
  linarith

/-! ### Never swallowed -/

/-- **A height bounded away from `0` keeps `f` away from `0`.** If `(1 + cos Y)/2 ≤ g₀ < 1` for the
angle `Y` of `[c, a]` seen from `w ∈ ℍ`, with `c < a < 0`, `|a|, |c| ≤ M` and `ac ≥ m > 0`, then
`‖w‖ ≥ min 1 ((1 − k) m/(4M + 1))`, `k = max (2g₀ − 1) 0`. -/
theorem le_norm_of_heightCos_le {w : ℂ} (hw : 0 < w.im) {a c M m g₀ : ℝ} (hca : c < a)
    (ha : a < 0) (hMa : |a| ≤ M) (hMc : |c| ≤ M) (hm : m ≤ a * c) (hg : g₀ < 1)
    (hG : (1 + Real.cos (arg (w - a) - arg (w - c))) / 2 ≤ g₀) :
    min 1 ((1 - max (2 * g₀ - 1) 0) * m / (4 * M + 1)) ≤ ‖w‖ := by
  set k := max (2 * g₀ - 1) 0 with hkdef
  have hk0 : 0 ≤ k := le_max_right _ _
  have hk1 : k < 1 := max_lt (by linarith) one_pos
  have hM0 : 0 ≤ M := (abs_nonneg a).trans hMa
  have hw1 : w - (a : ℂ) ≠ 0 := fun h => by
    have := congrArg Complex.im h; simp at this; linarith
  have hw2 : w - (c : ℂ) ≠ 0 := fun h => by
    have := congrArg Complex.im h; simp at this; linarith
  have hN : 0 < ‖w - a‖ * ‖w - c‖ := mul_pos (norm_pos_iff.2 hw1) (norm_pos_iff.2 hw2)
  rw [cos_arg_sub_arg w a c hw] at hG
  set N := ‖w - a‖ * ‖w - c‖ with hNdef
  set X := (w.re ^ 2 + w.im ^ 2) - (a + c) * w.re + a * c with hXdef
  set ε := ‖w‖ with hεdef
  have hXk : X ≤ k * N := by
    have h1 : X / N ≤ 2 * g₀ - 1 := by linarith
    have h2 : X / N ≤ k := h1.trans (le_max_left _ _)
    rwa [div_le_iff₀ hN] at h2
  have hre : |w.re| ≤ ε := Complex.abs_re_le_norm w
  have hac : |a| * |c| = a * c := by
    rw [abs_of_neg ha, abs_of_neg (hca.trans ha)]; ring
  have hXlow : a * c - |a + c| * ε ≤ X := by
    have h1 : -(|a + c| * ε) ≤ -(a + c) * w.re := by
      have := abs_mul (a + c) w.re
      have h2 : |(a + c) * w.re| ≤ |a + c| * ε := by
        rw [this]; exact mul_le_mul_of_nonneg_left hre (abs_nonneg _)
      have h4 := (abs_le.1 h2).2
      have h5 : -(a + c) * w.re = -((a + c) * w.re) := neg_mul _ _
      linarith
    have h3 : 0 ≤ w.re ^ 2 + w.im ^ 2 := by positivity
    rw [hXdef]; linarith
  have hNup : N ≤ (ε + |a|) * (ε + |c|) := by
    have h1 : ‖w - a‖ ≤ ε + |a| := by
      refine (norm_sub_le _ _).trans ?_; rw [Complex.norm_real, Real.norm_eq_abs]
    have h2 : ‖w - c‖ ≤ ε + |c| := by
      refine (norm_sub_le _ _).trans ?_; rw [Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul h1 h2 (norm_nonneg _) (by positivity)
  have hε0 : 0 ≤ ε := norm_nonneg w
  have habs : |a + c| ≤ 2 * M := (abs_add_le a c).trans (by linarith)
  by_contra hlt
  push Not at hlt
  have hε1 : ε < 1 := lt_of_lt_of_le hlt (min_le_left _ _)
  have hε2 : ε < (1 - k) * m / (4 * M + 1) := lt_of_lt_of_le hlt (min_le_right _ _)
  rw [lt_div_iff₀ (by linarith)] at hε2
  -- `(1 − k) a c ≤ (4M + 1) ε`
  have hkey : (1 - k) * (a * c) ≤ (4 * M + 1) * ε := by
    have h1 : X ≤ k * ((ε + |a|) * (ε + |c|)) := hXk.trans (mul_le_mul_of_nonneg_left hNup hk0)
    have h2 : k * ((ε + |a|) * (ε + |c|)) = k * ε ^ 2 + k * (|a| + |c|) * ε + k * (a * c) := by
      rw [← hac]; ring
    have h3 : k * ε ^ 2 ≤ ε := by nlinarith
    have h4 : k * (|a| + |c|) * ε ≤ 2 * M * ε := by
      have : k * (|a| + |c|) ≤ 2 * M := by nlinarith
      exact mul_le_mul_of_nonneg_right this hε0
    have h5 : |a + c| * ε ≤ 2 * M * ε := mul_le_mul_of_nonneg_right habs hε0
    nlinarith
  have hmk : (1 - k) * m ≤ (1 - k) * (a * c) := mul_le_mul_of_nonneg_left hm (by linarith)
  linarith

/-- **(3.20): a point of `ℍ` of large strip height is never swallowed.** Let `W` be continuous with
`W 0 = 0`, `r₊ < r₋ < 0` two real points that are never swallowed, and `S` a bound for the whole strip
clock `∫₀ᵗ (1/c − 1/a)²`. If `cos²(Y₀/2) e^S < 1`, where `Y₀ = arg(z − r₋) − arg(z − r₊)` is the initial
strip height of `z`, then `z` is never swallowed. -/
theorem swallowTime_eq_top_of_heightCos (hW : Continuous W) (hW0 : W 0 = 0) {rm rp : ℝ}
    (hr : rp < rm) (hrm : rm < 0)
    (hA : ∀ T, 0 ≤ T → ∃ u, IsForwardSol W (rm : ℂ) T u)
    (hC : ∀ T, 0 ≤ T → ∃ u, IsForwardSol W (rp : ℂ) T u) {S : ℝ}
    (hS : ∀ t, 0 ≤ t → ∫ s in (0 : ℝ)..t,
      stripRate (fun s => fwdMap W s rm) (fun s => fwdMap W s rp) s ≤ S)
    (hz : 0 < z.im) (hG : (1 + Real.cos (arg (z - rm) - arg (z - rp))) / 2 * Real.exp S < 1) :
    swallowTime W z = ⊤ := by
  by_contra hne
  set σ := (swallowTime W z).toReal with hσdef
  have hσ : swallowTime W z = ENNReal.ofReal σ := (ENNReal.ofReal_toReal hne).symm
  have hσ0 : 0 ≤ σ := ENNReal.toReal_nonneg
  obtain ⟨ua, hua⟩ := hA σ hσ0
  obtain ⟨uc, huc⟩ := hC σ hσ0
  have hord : ∀ s ∈ Icc (0 : ℝ) σ, (uc s).re < (ua s).re ∧ (ua s).re < 0 := fun s hs =>
    ⟨re_lt_re_of_isForwardSol hW hr huc hua hs, re_neg_of_isForwardSol hW hW0 hrm hua hs⟩
  -- bounds on `[0, σ]`
  have hcont_a : ContinuousOn (fun s => (ua s).re) (Icc 0 σ) :=
    Complex.continuous_re.comp_continuousOn hua.1
  have hcont_c : ContinuousOn (fun s => (uc s).re) (Icc 0 σ) :=
    Complex.continuous_re.comp_continuousOn huc.1
  obtain ⟨Ma, hMa⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont_a
  obtain ⟨Mc, hMc⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont_c
  set M := max Ma Mc with hMdef
  obtain ⟨s₀, hs₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hσ0)
    (hcont_a.mul hcont_c)
  set m := (ua s₀).re * (uc s₀).re with hmdef
  have hm0 : 0 < m := mul_pos_of_neg_of_neg (hord s₀ hs₀).2 ((hord s₀ hs₀).1.trans (hord s₀ hs₀).2)
  set G₀ := (1 + Real.cos (arg (z - rm) - arg (z - rp))) / 2 with hG₀def
  have hG₀ : 0 ≤ G₀ := by have := Real.neg_one_le_cos (arg (z - rm) - arg (z - rp)); rw [hG₀def]; linarith
  set g₀ := G₀ * Real.exp S with hg₀def
  set δ := min 1 ((1 - max (2 * g₀ - 1) 0) * m / (4 * M + 1)) with hδdef
  have hM0 : 0 ≤ M := by
    have := hMa 0 ⟨le_rfl, hσ0⟩
    exact (norm_nonneg _).trans (this.trans (le_max_left _ _))
  have hδ : 0 < δ := lt_min one_pos (div_pos (mul_pos (by
    have : max (2 * g₀ - 1) 0 < 1 := max_lt (by linarith) one_pos
    linarith) hm0) (by linarith))
  -- the clock stays bounded before `σ`
  have hclock : ∀ t, 0 ≤ t → t < σ → FwdClock.fwdClock W t z ≤ σ / δ ^ 2 := by
    intro t ht0 htσ
    have hlive : ∃ f, IsForwardSol W z t f := by
      refine exists_isForwardSol_of_not_mem_fwdHull ht0 hz fun hK => ?_
      have := hK.2
      rw [hσ, ENNReal.ofReal_le_ofReal_iff ht0] at this
      linarith
    obtain ⟨f, hf⟩ := hlive
    have htσ' : t ≤ σ := htσ.le
    have hua' := isForwardSol_restrict hua ht0 htσ'
    have huc' := isForwardSol_restrict huc ht0 htσ'
    have hnorm : ∀ s ∈ Icc (0 : ℝ) t, δ ≤ ‖f s‖ := by
      intro s hs
      have hsσ : s ∈ Icc (0 : ℝ) σ := ⟨hs.1, hs.2.trans htσ'⟩
      have hle := heightCos_le hW hz hf hua' huc'
        (fun r hr => hord r ⟨hr.1, hr.2.trans htσ'⟩) hs
      have h0 : heightCos f ua uc 0 = G₀ := by
        have h0' : (0 : ℝ) ∈ Icc (0 : ℝ) t := ⟨le_rfl, ht0⟩
        simp only [heightCos, stripHeight, hG₀def]
        rw [(hf.2 0 h0').2, (hua'.2 0 h0').2, (huc'.2 0 h0').2]
        simp [hW0]
      have hint : ∫ r in (0 : ℝ)..s, stripRate ua uc r =
          ∫ r in (0 : ℝ)..s, stripRate (fun r => fwdMap W r rm) (fun r => fwdMap W r rp) r := by
        refine intervalIntegral.integral_congr fun r hr => ?_
        rw [uIcc_of_le hs.1] at hr
        have hrσ : r ∈ Icc (0 : ℝ) σ := ⟨hr.1, hr.2.trans hsσ.2⟩
        simp only [stripRate, fwdMap_eq_of_isForwardSol hW hua hrσ,
          fwdMap_eq_of_isForwardSol hW huc hrσ]
      have hGs : heightCos f ua uc s ≤ g₀ := by
        refine hle.trans ?_
        rw [h0, hint]
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (hS s hs.1)) hG₀
      have hfs : 0 < (f s).im := FwdClock.sol_im_pos hW hz hf hs
      have har := ofReal_re_of_isForwardSol hW hua hsσ
      have hcr := ofReal_re_of_isForwardSol hW huc hsσ
      have hGs' : (1 + Real.cos (arg (f s - ((ua s).re : ℂ)) - arg (f s - ((uc s).re : ℂ)))) / 2
          ≤ g₀ := by
        rw [har, hcr]; exact hGs
      have hMa' : |(ua s).re| ≤ M := by
        have := hMa s hsσ; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_left _ _)
      have hMc' : |(uc s).re| ≤ M := by
        have := hMc s hsσ; rw [Real.norm_eq_abs] at this; exact this.trans (le_max_right _ _)
      exact le_norm_of_heightCos_le hfs (hord s hsσ).1 (hord s hsσ).2 hMa' hMc' (hmin hsσ)
        hG hGs'
    have hcl : FwdClock.fwdClock W t z ≤ ∫ s in (0 : ℝ)..t, 1 / δ ^ 2 := by
      refine intervalIntegral.integral_mono_on ht0 ?_ intervalIntegrable_const fun s hs => ?_
      · refine ContinuousOn.intervalIntegrable_of_Icc ht0 ?_
        have hc : ContinuousOn (fun r => 1 / ‖f r‖ ^ 2) (Icc 0 t) :=
          continuousOn_const.div ((hf.1.norm).pow 2) fun r hr =>
            pow_ne_zero 2 (norm_ne_zero_iff.2 (hf.2 r hr).1)
        refine hc.congr fun r hr => ?_
        simp only [fwdMap_eq_of_isForwardSol hW hf hr]
      · rw [fwdMap_eq_of_isForwardSol hW hf hs]
        exact one_div_le_one_div_of_le (by positivity)
          (pow_le_pow_left₀ hδ.le (hnorm s hs) 2)
    rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hcl
    calc FwdClock.fwdClock W t z ≤ t * (1 / δ ^ 2) := hcl
      _ ≤ σ * (1 / δ ^ 2) := mul_le_mul_of_nonneg_right htσ.le (by positivity)
      _ = σ / δ ^ 2 := by ring
  obtain ⟨t, ht0, htσ, hlt⟩ := FwdClock.fwdClock_unbounded_of_swallowTime hW hz hσ (σ / δ ^ 2)
  exact absurd (hclock t ht0 htσ) (not_le.2 hlt)

end Flow

/-! ### The trace stays away from the upper arc -/

/-- `cos²(Y/2)` of the strip height of `z`, written without `arg` (`(1 + Re P/|P|)/2`,
`P = (z − r₋)·conj(z − r₊)`); continuous off `{r₋, r₊}`. -/
def heightCosAt (rm rp : ℝ) (z : ℂ) : ℝ :=
  (1 + ((z - rm) * (starRingEnd ℂ) (z - rp)).re / (‖z - rm‖ * ‖z - rp‖)) / 2

theorem heightCosAt_eq (rm rp : ℝ) {z : ℂ} (hz : 0 < z.im) :
    heightCosAt rm rp z = (1 + Real.cos (arg (z - rm) - arg (z - rp))) / 2 := by
  rw [heightCosAt, cos_arg_sub_arg z rm rp hz, re_mul_conj_sub]

theorem heightCosAt_of_mem_Ioo {rm rp x : ℝ} (hx : x ∈ Ioo rp rm) : heightCosAt rm rp x = 0 := by
  have h1 : ((x : ℂ) - rm) * (starRingEnd ℂ) ((x : ℂ) - rp) = (((x - rm) * (x - rp) : ℝ) : ℂ) := by
    simp [Complex.conj_ofReal]
  have h2 : ‖(x : ℂ) - rm‖ * ‖(x : ℂ) - rp‖ = -((x - rm) * (x - rp)) := by
    rw [← Complex.ofReal_sub, ← Complex.ofReal_sub, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_neg (by linarith [hx.2]),
      abs_of_pos (by linarith [hx.1])]
    ring
  have hne : (x - rm) * (x - rp) ≠ 0 := mul_ne_zero (by linarith [hx.2]) (by linarith [hx.1])
  rw [heightCosAt, h1, h2, Complex.ofReal_re, div_neg, div_self hne]
  ring

theorem continuousAt_heightCosAt {rm rp : ℝ} {z : ℂ} (h1 : z ≠ rm) (h2 : z ≠ rp) :
    ContinuousAt (heightCosAt rm rp) z := by
  have hn : ‖z - rm‖ * ‖z - rp‖ ≠ 0 :=
    mul_ne_zero (norm_ne_zero_iff.2 (sub_ne_zero.2 h1)) (norm_ne_zero_iff.2 (sub_ne_zero.2 h2))
  have h1 : ContinuousAt (fun y : ℂ => ((y - rm) * (starRingEnd ℂ) (y - rp)).re) z :=
    Complex.continuous_re.continuousAt.comp ((continuousAt_id.sub continuousAt_const).mul
      (Complex.continuous_conj.continuousAt.comp (continuousAt_id.sub continuousAt_const)))
  have h2 : ContinuousAt (fun y : ℂ => ‖y - rm‖ * ‖y - rp‖) z :=
    ((continuousAt_id.sub continuousAt_const).norm).mul
      ((continuousAt_id.sub continuousAt_const).norm)
  exact (continuousAt_const.add (h1.div h2 hn)).div_const 2

/-- A point of `ℍ` on a generating trace is in every later hull. -/
theorem mem_fwdHull_of_isGeneratingTrace {w : ℝ≥0 → ℝ} {η : ℝ≥0 → ℂ}
    (hη : IsGeneratingTrace w ⊤ η) {t t' : ℝ≥0} (htt' : t ≤ t') (hH : 0 < (η t).im) :
    η t ∈ fwdHull (fun s : ℝ => w s.toNNReal) t' := by
  obtain ⟨-, -, hfill⟩ := hη
  obtain ⟨⟨z, -, hcc⟩, -⟩ := hfill t' ENNReal.coe_lt_top
  by_contra hK
  have hmem : η t ∈ QuantumZipper.H \ fwdHull (fun s : ℝ => w s.toNNReal) t' := ⟨hH, hK⟩
  rw [← hcc] at hmem
  exact (connectedComponentIn_subset _ _ hmem).2 ⟨t, ⟨zero_le, htt'⟩, rfl⟩

/-- **Uniform avoidance, deterministic part.** Let `w` be a continuous driver with `w 0 = 0` and a
continuous generating trace `η` on `[0, ∞)`, let `r₊ < r₋ < 0` be never swallowed, and let the whole
strip clock be bounded by `S`. Then `η` stays at positive distance from every compact `I ⊆ (r₊, r₋)`. -/
theorem exists_pos_le_norm_sub_of_stripClock {w : ℝ≥0 → ℝ}
    (hw : Continuous fun s : ℝ => w s.toNNReal) (hw0 : w 0 = 0) {rm rp : ℝ} (hr : rp < rm)
    (hrm : rm < 0)
    (hA : ∀ T, 0 ≤ T → ∃ u, IsForwardSol (fun s : ℝ => w s.toNNReal) (rm : ℂ) T u)
    (hC : ∀ T, 0 ≤ T → ∃ u, IsForwardSol (fun s : ℝ => w s.toNNReal) (rp : ℂ) T u) {S : ℝ}
    (hS : ∀ t, 0 ≤ t → ∫ s in (0 : ℝ)..t, stripRate (fun s => fwdMap (fun s : ℝ => w s.toNNReal) s rm)
      (fun s => fwdMap (fun s : ℝ => w s.toNNReal) s rp) s ≤ S)
    {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace w ⊤ η) {I : Set ℝ} (hI : IsCompact I)
    (hIsub : I ⊆ Ioo rp rm) : ∃ d > 0, ∀ t : ℝ≥0, ∀ x ∈ I, d ≤ ‖η t - x‖ := by
  set W : ℝ → ℝ := fun s => w s.toNNReal with hWdef
  have hW0 : W 0 = 0 := by simp [hWdef, hw0]
  set g := Real.exp (-S) with hgdef
  -- points of `ℍ` on the trace have `G ≥ e^{−S}`
  have hlow : ∀ t : ℝ≥0, 0 < (η t).im → g ≤ heightCosAt rm rp (η t) := by
    intro t hH
    by_contra hlt
    push Not at hlt
    have hG : (1 + Real.cos (arg (η t - rm) - arg (η t - rp))) / 2 * Real.exp S < 1 := by
      rw [← heightCosAt_eq rm rp hH]
      have := mul_lt_mul_of_pos_right hlt (Real.exp_pos S)
      rwa [hgdef, ← Real.exp_add, neg_add_cancel, Real.exp_zero] at this
    have htop := swallowTime_eq_top_of_heightCos hw hW0 hr hrm hA hC hS hH hG
    have hK := mem_fwdHull_of_isGeneratingTrace hη (le_refl t) hH
    have := hK.2
    rw [htop] at this
    exact ENNReal.ofReal_ne_top (top_le_iff.1 this)
  -- the open set where `G < e^{−S}`
  set U : Set ℂ := {z | z ≠ rm ∧ z ≠ rp ∧ heightCosAt rm rp z < g} with hUdef
  have hUo : IsOpen U := by
    rw [isOpen_iff_mem_nhds]
    intro z hz
    have hc := continuousAt_heightCosAt hz.1 hz.2.1
    have h1 : ∀ᶠ y in 𝓝 z, y ≠ (rm : ℂ) := isOpen_ne.mem_nhds hz.1
    have h2 : ∀ᶠ y in 𝓝 z, y ≠ (rp : ℂ) := isOpen_ne.mem_nhds hz.2.1
    have h3 : ∀ᶠ y in 𝓝 z, heightCosAt rm rp y < g := hc.eventually (gt_mem_nhds hz.2.2)
    filter_upwards [h1, h2, h3] with y hy1 hy2 hy3 using ⟨hy1, hy2, hy3⟩
  have hηc : Continuous η := by
    rw [← continuousOn_univ]; exact hη.2.1.mono fun t _ => show (t : ℝ≥0∞) ≤ ⊤ from le_top
  -- the trace never enters `U`
  have hnot : ∀ t : ℝ≥0, η t ∉ U := by
    have hH : ∀ t : ℝ≥0, 0 < (η t).im → η t ∉ U := fun t hH hU =>
      absurd (hlow t hH) (not_le.2 hU.2.2)
    intro t hU
    rcases (Sec4.im_nonneg_of_isGeneratingTrace hw hw0 hη t).lt_or_eq with hpos | hzero
    · exact hH t hpos hU
    · obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.1 ((hηc.continuousAt (x := t)).preimage_mem_nhds
        (hUo.mem_nhds hU))
      set s₂ : ℝ≥0 := ((t : ℝ) + ε / 2).toNNReal
      have hs₂ : (s₂ : ℝ) = (t : ℝ) + ε / 2 := Real.coe_toNNReal _ (by positivity)
      have hts : t < s₂ := by rw [← NNReal.coe_lt_coe, hs₂]; linarith
      obtain ⟨s, hts', hs₂', hspos⟩ := Sec4.exists_im_pos_of_isGeneratingTrace hw hw0 hη hts
      have hts'' : (t : ℝ) < s := by exact_mod_cast hts'
      have hsle : (s : ℝ) ≤ s₂ := by exact_mod_cast hs₂'
      have hsU : η s ∈ U := hball (by
        rw [Metric.mem_ball, NNReal.dist_eq, abs_of_pos (sub_pos.2 hts'')]
        linarith)
      exact hH s hspos hsU
  -- a uniform distance from the compact image of `I`
  set I' : Set ℂ := (fun x : ℝ => (x : ℂ)) '' I with hI'def
  have hI'c : IsCompact I' := hI.image Complex.continuous_ofReal
  have hI'U : I' ⊆ U := by
    rintro _ ⟨x, hx, rfl⟩
    have hx' := hIsub hx
    refine ⟨fun h => by have := Complex.ofReal_injective h; linarith [hx'.2],
      fun h => by have := Complex.ofReal_injective h; linarith [hx'.1], ?_⟩
    rw [heightCosAt_of_mem_Ioo hx']
    exact Real.exp_pos _
  obtain ⟨d, hd, hsub⟩ := hI'c.exists_cthickening_subset_open hUo hI'U
  refine ⟨d, hd, fun t x hx => ?_⟩
  by_contra hlt
  push Not at hlt
  have hmem : η t ∈ Metric.cthickening d I' :=
    Metric.mem_cthickening_of_dist_le (η t) (x : ℂ) d I' ⟨x, hx, rfl⟩
      (by rw [dist_eq_norm]; exact hlt.le)
  exact hnot t (hsub hmem)

end Zhan

end InteractingSLE
