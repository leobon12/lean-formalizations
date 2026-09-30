import QuantumZipper.Proofs.Thm18.LWExcUpper
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.8, LW-FAR route: explicit harmonic minorants for LW Lemma 4.3 (task LW43-KEY)

Two explicit harmonic functions used in the proof of the lower half of Lawler–Werness's key
estimate (G. F. Lawler, B. M. Werness, *Multi-point Green's functions for SLE and an estimate of
Beffara*, Ann. Probab. 41 (2013), sketch of proof of Lemma 4.3, p. 24,
`literature/1011.3551.pdf`):

* the log-polar minorant on the half-annulus `{r/2 < |z + 1| < 2r} ∩ ℍ` (`s = ±1`,
  `k = π/(2 log 2)`, `σ = log(2|z + 1|/r)`, `φ = s arg(s(z + 1)) ∈ [0, π]`):
  `m(z) = sin(kσ) sinh(kφ)/sinh(kπ) = Im(−s cos(k log(2s(z + 1)/r)))/sinh(kπ)`;
  it vanishes on both semicircles and on the real side where `φ = 0`, and is `≤ 1`;
  on `|z + 1| = r` it is `≥ (k/sinh(kπ)) Im z/r`;
* the far minorant `u(z) = c r Im z/|z + 1|² = Im(−c r/(z + 1))`.

These are the standard separated-variables harmonic functions on a rectangle in log-polar
coordinates (own elementary computation; no source needed beyond the harmonicity of the real and
imaginary parts of an analytic function, Ahlfors, *Complex Analysis*, Ch. 4 §6.1).
-/

noncomputable section

open Filter Set Metric Complex
open scoped Topology Real

namespace QuantumZipper
namespace Thm18Asm
namespace LWFar

/-- `k = π/(2 log 2)`. -/
def lw3k : ℝ := π / (2 * Real.log 2)

lemma lw3k_pos : 0 < lw3k := div_pos Real.pi_pos (by have := Real.log_pos one_lt_two; positivity)

lemma lw3k_log2 : lw3k * Real.log 2 = π / 2 := by
  unfold lw3k; have := Real.log_pos one_lt_two; field_simp

lemma lw3k_log4 : lw3k * Real.log 4 = π := by
  have : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  rw [this]; unfold lw3k; have := Real.log_pos one_lt_two; field_simp

lemma lw3_sinh_pos : 0 < Real.sinh (lw3k * π) :=
  Real.sinh_pos_iff.2 (mul_pos lw3k_pos Real.pi_pos)

/-- The minorant constant `c₀ = k/sinh(kπ)`. -/
def lw3c0 : ℝ := lw3k / Real.sinh (lw3k * π)

lemma lw3c0_pos : 0 < lw3c0 := div_pos lw3k_pos lw3_sinh_pos

lemma lw3c0_le_one : lw3c0 ≤ 1 := by
  rw [lw3c0, div_le_one lw3_sinh_pos]
  have h1 := Real.self_le_sinh_iff.2 (mul_pos lw3k_pos Real.pi_pos).le
  have h2 : lw3k ≤ lw3k * π := le_mul_of_one_le_right lw3k_pos.le (by linarith [Real.pi_gt_three])
  linarith

/-- The log-polar minorant `m = Im(−s cos(k log(2s(z + 1)/r)))/sinh(kπ)`. -/
def lw3Min (s r : ℝ) (z : ℂ) : ℝ :=
  ((((-s / Real.sinh (lw3k * π)) : ℝ) : ℂ) *
    Complex.cos ((lw3k : ℂ) * Complex.log (((2 / r : ℝ) : ℂ) * ((s : ℂ) * (z + 1))))).im

lemma lw3_cos_im (x y : ℝ) :
    (Complex.cos ((x : ℂ) + (y : ℂ) * I)).im = -Real.sin x * Real.sinh y := by
  rw [cos_add_mul_I]
  simp [Complex.sin_ofReal_re, Complex.sinh_ofReal_re, Complex.cos_ofReal_im,
    Complex.cosh_ofReal_im, Complex.sin_ofReal_im, Complex.sinh_ofReal_im]

lemma lw3_s_im_ne {s : ℝ} (hs : s = 1 ∨ s = -1) {z : ℂ} (hz : 0 < z.im) :
    ((s : ℂ) * (z + 1)).im ≠ 0 := by
  rcases hs with rfl | rfl <;> simp <;> linarith

lemma lw3Min_harm {s r : ℝ} (hs : s = 1 ∨ s = -1) (hr : 0 < r) :
    InnerProductSpace.HarmonicOnNhd (lw3Min s r) H := by
  intro w hw
  have hw' : 0 < w.im := hw
  have hW : AnalyticAt ℂ (fun v : ℂ => ((2 / r : ℝ) : ℂ) * ((s : ℂ) * (v + 1))) w :=
    analyticAt_const.mul (analyticAt_const.mul (analyticAt_id.add analyticAt_const))
  have hsl : ((2 / r : ℝ) : ℂ) * ((s : ℂ) * (w + 1)) ∈ slitPlane := by
    rw [mem_slitPlane_iff]; right
    rw [im_ofReal_mul]
    exact mul_ne_zero (by positivity) (lw3_s_im_ne hs hw')
  have hL : AnalyticAt ℂ (fun v : ℂ => Complex.log (((2 / r : ℝ) : ℂ) * ((s : ℂ) * (v + 1)))) w :=
    AnalyticAt.comp (f := fun v : ℂ => ((2 / r : ℝ) : ℂ) * ((s : ℂ) * (v + 1))) (x := w)
      (analyticAt_clog hsl) hW
  have hC : AnalyticAt ℂ (fun v : ℂ => Complex.cos ((lw3k : ℂ) *
      Complex.log (((2 / r : ℝ) : ℂ) * ((s : ℂ) * (v + 1))))) w :=
    AnalyticAt.comp (f := fun v : ℂ => (lw3k : ℂ) *
      Complex.log (((2 / r : ℝ) : ℂ) * ((s : ℂ) * (v + 1)))) (x := w) analyticAt_cos
      (analyticAt_const.mul hL)
  exact (analyticAt_const.mul hC).harmonicAt_im

/-- `φ = s arg(s(z + 1))`. -/
lemma lw3_phi_mem {s : ℝ} (hs : s = 1 ∨ s = -1) {z : ℂ} (hz : 0 < z.im) :
    0 ≤ s * arg ((s : ℂ) * (z + 1)) ∧ s * arg ((s : ℂ) * (z + 1)) ≤ π := by
  rcases hs with rfl | rfl
  · simp only [ofReal_one, one_mul]
    exact ⟨arg_nonneg_iff.2 (by simp; linarith), arg_le_pi _⟩
  · simp only [ofReal_neg, ofReal_one, neg_mul, one_mul]
    have h1 : arg (-(z + 1)) < 0 := arg_neg_iff.2 (by simp; linarith)
    have h2 := neg_pi_lt_arg (-(z + 1))
    constructor <;> linarith

lemma lw3_phi_sin {s : ℝ} (hs : s = 1 ∨ s = -1) (z : ℂ) :
    Real.sin (s * arg ((s : ℂ) * (z + 1))) = z.im / ‖z + 1‖ := by
  rcases hs with rfl | rfl
  · simp [sin_arg]
  · simp [sin_arg, Real.sin_neg]
    have hn : ‖-1 + -z‖ = ‖z + 1‖ := by rw [← norm_neg]; congr 1; ring
    rw [hn]; ring

/-- Real form of the minorant on `ℍ`. -/
lemma lw3Min_eq {s r : ℝ} (hs : s = 1 ∨ s = -1) (hr : 0 < r) (z : ℂ) :
    lw3Min s r z = Real.sin (lw3k * Real.log (2 / r * ‖z + 1‖)) *
      Real.sinh (lw3k * (s * arg ((s : ℂ) * (z + 1)))) / Real.sinh (lw3k * π) := by
  have harg : arg (((2 / r : ℝ) : ℂ) * ((s : ℂ) * (z + 1))) = arg ((s : ℂ) * (z + 1)) :=
    arg_real_mul _ (by positivity)
  have hs1 : ‖(s : ℂ)‖ = 1 := by rcases hs with rfl | rfl <;> simp
  have hnorm : ‖((2 / r : ℝ) : ℂ) * ((s : ℂ) * (z + 1))‖ = 2 / r * ‖z + 1‖ := by
    rw [norm_mul, norm_mul, hs1, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity)]
  have hW : (lw3k : ℂ) * Complex.log (((2 / r : ℝ) : ℂ) * ((s : ℂ) * (z + 1))) =
      ((lw3k * Real.log (2 / r * ‖z + 1‖) : ℝ) : ℂ) +
        ((lw3k * arg ((s : ℂ) * (z + 1)) : ℝ) : ℂ) * I := by
    apply Complex.ext
    · rw [re_ofReal_mul, Complex.log_re, hnorm]; simp
    · rw [im_ofReal_mul, Complex.log_im, harg]; simp
  rw [lw3Min, im_ofReal_mul, hW, lw3_cos_im]
  rcases hs with rfl | rfl
  · simp only [one_mul]; ring
  · simp only [neg_mul, one_mul, Real.sinh_neg, mul_neg]; ring

lemma lw3Min_T_mem {s : ℝ} (hs : s = 1 ∨ s = -1) {z : ℂ} (hz : 0 < z.im) :
    0 ≤ Real.sinh (lw3k * (s * arg ((s : ℂ) * (z + 1)))) / Real.sinh (lw3k * π) ∧
      Real.sinh (lw3k * (s * arg ((s : ℂ) * (z + 1)))) / Real.sinh (lw3k * π) ≤ 1 := by
  obtain ⟨h0, hπ⟩ := lw3_phi_mem hs hz
  have hk := lw3k_pos
  refine ⟨div_nonneg (Real.sinh_nonneg_iff.2 (mul_nonneg hk.le h0)) lw3_sinh_pos.le, ?_⟩
  rw [div_le_one lw3_sinh_pos, Real.sinh_le_sinh]
  exact mul_le_mul_of_nonneg_left hπ hk.le

lemma lw3Min_le_T {s r : ℝ} (hs : s = 1 ∨ s = -1) (hr : 0 < r) {z : ℂ} (hz : 0 < z.im) :
    lw3Min s r z ≤ Real.sinh (lw3k * (s * arg ((s : ℂ) * (z + 1)))) / Real.sinh (lw3k * π) := by
  rw [lw3Min_eq hs hr, mul_div_assoc]
  have hT := lw3Min_T_mem hs hz
  have := Real.sin_le_one (lw3k * Real.log (2 / r * ‖z + 1‖))
  nlinarith

lemma lw3Min_le_S {s r : ℝ} (hs : s = 1 ∨ s = -1) (hr : 0 < r) {z : ℂ} (hz : 0 < z.im) :
    lw3Min s r z ≤ |Real.sin (lw3k * Real.log (2 / r * ‖z + 1‖))| := by
  rw [lw3Min_eq hs hr, mul_div_assoc]
  have hT := lw3Min_T_mem hs hz
  have h1 := le_abs_self (Real.sin (lw3k * Real.log (2 / r * ‖z + 1‖)))
  have h2 := abs_nonneg (Real.sin (lw3k * Real.log (2 / r * ‖z + 1‖)))
  nlinarith

lemma lw3Min_le_one {s r : ℝ} (hs : s = 1 ∨ s = -1) (hr : 0 < r) {z : ℂ} (hz : 0 < z.im) :
    lw3Min s r z ≤ 1 :=
  (lw3Min_le_T hs hr hz).trans (lw3Min_T_mem hs hz).2

/-- On the middle semicircle `|z + 1| = r`: `m(z) ≥ c₀ Im z / r`. -/
lemma lw3Min_circle {s r : ℝ} (hs : s = 1 ∨ s = -1) (hr : 0 < r) {z : ℂ} (hz : 0 < z.im)
    (hzr : ‖z + 1‖ = r) : lw3c0 * (z.im / r) ≤ lw3Min s r z := by
  rw [lw3Min_eq hs hr, hzr, show 2 / r * r = 2 by field_simp, lw3k_log2, Real.sin_pi_div_two,
    one_mul, lw3c0, div_mul_eq_mul_div]
  refine div_le_div_of_nonneg_right ?_ lw3_sinh_pos.le
  obtain ⟨h0, -⟩ := lw3_phi_mem hs hz
  have hk := lw3k_pos
  have h1 := Real.sin_le h0
  rw [lw3_phi_sin hs, hzr] at h1
  have h2 := Real.self_le_sinh_iff.2 (mul_nonneg hk.le h0)
  nlinarith

/-- The far minorant `u(z) = c r Im z/|z + 1|² = Im(−c r/(z + 1))`. -/
def lw3Out (c r : ℝ) (z : ℂ) : ℝ := ((((-(c * r)) : ℝ) : ℂ) * (z + 1)⁻¹).im

lemma lw3Out_eq (c r : ℝ) (z : ℂ) : lw3Out c r z = c * r * z.im / ‖z + 1‖ ^ 2 := by
  rw [lw3Out, im_ofReal_mul, Complex.inv_im, Complex.normSq_eq_norm_sq]
  simp; ring

lemma lw3Out_harm (c r : ℝ) : InnerProductSpace.HarmonicOnNhd (lw3Out c r) H := by
  intro w hw
  have hw' : 0 < w.im := hw
  have hne : w + 1 ≠ 0 := fun h0 => by
    have := congrArg Complex.im h0; simp at this; linarith
  exact (analyticAt_const.mul ((analyticAt_id.add analyticAt_const).inv hne)).harmonicAt_im

end LWFar
end Thm18Asm
end QuantumZipper
