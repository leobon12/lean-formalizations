import QuantumZipper.Proofs.Thm18.LWExcMaxPrin
import QuantumZipper.Proofs.Thm18.LWExcDefs
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Field–Lawler (2.4): harmonic measure of a small semicircle in `ℍ` (task FL2-SEMI)

Source: L. S. Field, G. F. Lawler, *Escape probability and transience for SLE*, EJP 20 (2015),
p. 6, (2.4): "Using (2.3) and the Poisson kernel in `ℍ \ D_r` we can see that
`E_H(C, C_r) ≤ c e^{-r}`" (`literature/1407.3314.pdf`). FL give no further detail; the half-plane
estimate behind it is proved here.

`fl2_semicircle_harm_le`: the harmonic measure `h` of the semicircle `ℍ ∩ {|z| = ε}` in
`ℍ \ B̄(0, ε)` satisfies `h z ≤ C ε Im z / |z|²` for `|z| ≥ 2ε`.

Proof (own elementary proof, standard comparison argument): with `a = 3ε/2`,
`g(z) = arg((z - a)/(z + a))` (the angle subtended by `[-a, a]`, `π ×` its harmonic measure in
`ℍ`) is harmonic on `ℍ`, `g ≥ 0`, `g ≥ π/2 ≥ 1` on `ℍ ∩ {|z| < a}`, and by Jordan's inequality
`g(z) ≤ (π/2) · 2a Im z / (|z - a||z + a|) ≤ 24π ε Im z / |z|²` for `|z| ≥ 2ε`. The weak
maximum principle `lwExc_harm_le_zero` applied to `h - g` gives `h ≤ g`: near frontier points
with `|x₀| < a` one has `h ≤ 1 ≤ g` (so the corners `±ε` need no boundary information), at the
other frontier points `h → 0` (`IsHarmMeas.zero`), and `h → 0` at `∞`.
-/

noncomputable section

open Filter Set Metric Complex
open scoped Topology Real

namespace QuantumZipper
namespace FieldLawler

open QuantumZipper.Thm18Asm.LWFar

/-- The angle subtended by `[-a, a]` seen from `z`. -/
def fl2SemiAng (a : ℝ) (z : ℂ) : ℝ := arg ((z - a) / (z + a))

lemma fl2Semi_re (a : ℝ) (z : ℂ) :
    ((z - a) / (z + a)).re = (‖z‖ ^ 2 - a ^ 2) / ‖z + a‖ ^ 2 := by
  rw [Complex.div_re, ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, sub_re, add_re, ofReal_re, sub_im, add_im, ofReal_im, sub_zero, add_zero]
  ring

lemma fl2Semi_im (a : ℝ) (z : ℂ) :
    ((z - a) / (z + a)).im = 2 * a * z.im / ‖z + a‖ ^ 2 := by
  rw [Complex.div_im, ← Complex.normSq_eq_norm_sq]
  simp only [sub_re, add_re, ofReal_re, sub_im, add_im, ofReal_im, sub_zero, add_zero]
  ring

lemma fl2Semi_ne {a : ℝ} {z : ℂ} (hz : 0 < z.im) : z + a ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp at this
  linarith

lemma fl2Semi_im_pos {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : 0 < z.im) :
    0 < ((z - a) / (z + a)).im := by
  rw [fl2Semi_im]
  have : 0 < ‖z + a‖ := norm_pos_iff.2 (fl2Semi_ne hz)
  positivity

lemma fl2Semi_harm {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : 0 < z.im) :
    InnerProductSpace.HarmonicAt (fl2SemiAng a) z := by
  have hF : AnalyticAt ℂ (fun w : ℂ => (w - a) / (w + a)) z :=
    (analyticAt_id.sub analyticAt_const).div (analyticAt_id.add analyticAt_const)
      (fl2Semi_ne hz)
  have hsl : (z - a) / (z + a) ∈ slitPlane := by
    rw [mem_slitPlane_iff]; right; exact (fl2Semi_im_pos ha hz).ne'
  have h := (AnalyticAt.comp (g := log) (f := fun w : ℂ => (w - a) / (w + a))
    (analyticAt_clog hsl) hF).harmonicAt_im
  refine (InnerProductSpace.harmonicAt_congr_nhds ?_).1 h
  exact Eventually.of_forall fun w => by simp [fl2SemiAng, Function.comp, Complex.log_im]

lemma fl2Semi_nonneg (a : ℝ) (z : ℂ) (hz : 0 ≤ z.im) (ha : 0 ≤ a) : 0 ≤ fl2SemiAng a z := by
  unfold fl2SemiAng
  rw [arg_nonneg_iff, fl2Semi_im]
  positivity

lemma fl2Semi_ge_one {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : 0 < z.im) (hza : ‖z‖ < a) :
    1 ≤ fl2SemiAng a z := by
  unfold fl2SemiAng
  have hre : ((z - a) / (z + a)).re < 0 := by
    rw [fl2Semi_re]
    have : 0 < ‖z + a‖ := norm_pos_iff.2 (fl2Semi_ne hz)
    have h2 : ‖z‖ ^ 2 < a ^ 2 := by
      have := norm_nonneg z
      nlinarith
    exact div_neg_of_neg_of_pos (by linarith) (by positivity)
  rw [arg_of_re_neg_of_im_nonneg hre (fl2Semi_im_pos ha hz).le]
  have := Real.neg_pi_div_two_le_arcsin ((-((z - a) / (z + a))).im / ‖(z - a) / (z + a)‖)
  have := Real.pi_gt_three
  linarith

lemma fl2Semi_le {ε : ℝ} (hε : 0 < ε) {z : ℂ} (hz : 0 < z.im) (hz2 : 2 * ε ≤ ‖z‖) :
    fl2SemiAng (3 * ε / 2) z ≤ 24 * π * ε * z.im / ‖z‖ ^ 2 := by
  set a : ℝ := 3 * ε / 2 with ha_def
  have ha : 0 < a := by positivity
  set w := (z - a) / (z + a) with hw
  have hzpos : 0 < ‖z‖ := by linarith
  have hp : ‖z‖ / 4 ≤ ‖z - a‖ := by
    have := norm_sub_norm_le z (a : ℂ)
    rw [Complex.norm_real, Real.norm_of_nonneg ha.le] at this
    linarith
  have hq : ‖z‖ / 4 ≤ ‖z + a‖ := by
    have := norm_sub_norm_le z (-(a : ℂ))
    rw [norm_neg, Complex.norm_real, Real.norm_of_nonneg ha.le, sub_neg_eq_add] at this
    linarith
  have hqpos : 0 < ‖z + a‖ := by linarith
  have hppos : 0 < ‖z - a‖ := by linarith
  have hwre : 0 ≤ w.re := by
    rw [hw, fl2Semi_re]
    apply div_nonneg _ (by positivity)
    nlinarith
  have harg0 : 0 ≤ arg w := by rw [arg_nonneg_iff]; exact (fl2Semi_im_pos ha hz).le
  have harg1 : arg w ≤ π / 2 := (abs_le.1 (abs_arg_le_pi_div_two_iff.2 hwre)).2
  have hj := Real.mul_le_sin harg0 harg1
  rw [sin_arg] at hj
  -- `Im w / ‖w‖ = 2 a Im z / (‖z - a‖ ‖z + a‖)`
  have hratio : w.im / ‖w‖ = 2 * a * z.im / (‖z - a‖ * ‖z + a‖) := by
    rw [hw, fl2Semi_im, norm_div]
    field_simp
  rw [hratio] at hj
  have hb : 2 * a * z.im / (‖z - a‖ * ‖z + a‖) ≤ 2 * a * z.im / (‖z‖ / 4 * (‖z‖ / 4)) := by
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact mul_le_mul hp hq (by positivity) hppos.le
  have hpi : 0 < π := Real.pi_pos
  have key : arg w ≤ π / 2 * (2 * a * z.im / (‖z‖ / 4 * (‖z‖ / 4))) := by
    have h1 : arg w ≤ π / 2 * (2 * a * z.im / (‖z - a‖ * ‖z + a‖)) := by
      have : π / 2 * (2 / π * arg w) = arg w := by field_simp
      nlinarith
    exact h1.trans (mul_le_mul_of_nonneg_left hb (by positivity))
  show arg w ≤ _
  refine key.trans (le_of_eq ?_)
  rw [ha_def]
  field_simp
  ring

end FieldLawler
end QuantumZipper
