/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.ConstDriftGapProc
import InteractingSLE.Spec.Zhan.StripTailEscape

/-!
# The lower strip gap: the tamed drift and the Lyapunov function

Packet PROVE-ZHAN-A8. In strip time a point of the lower line `ℝ` of `S_π` (chordal point `x ∈ (−1, ∞) ∖ {0}`,
strip point `x₀ = log(1 + x)`) has the lower gap `X = ψ(x₀) − ξ`, which solves

  `X_t = x₀ − ξ_t + ∫₀ᵗ C(X_u) du`,  `C(x) = coth(x/2) = (eˣ + 1)/(eˣ − 1)`,  `ξ_t = √κ β_t + σ t`.

Near `0`, `C(x) ≈ 2/x`, so `X/√κ` is a Bessel process of dimension `1 + 4/κ ≥ 2` for `κ ≤ 4`, which does not reach
`0`. This file prepares the deterministic ingredients:

* the tamed drift `tame c x = C(max x c)` (bounded and Lipschitz for `c > 0`, equal to `C` on `[c, ∞)`);
* the Lyapunov function `lyap a x = −log(1 − e^{−x}) − a x` on `(0, ∞)`, with derivatives `lyapD`, `lyapDD`, and its
  generator bound `lyapD a x (C(x) − σ) + (κ/2) lyapDD x ≤ 0` (`lyap_gen_nonpos`) for `κ ≤ 4`, `σ ≤ 1`, `a ≥ 0` and
  `2a ≥ κ/2 − 1 + σ`: with `y = 1/(eˣ − 1)` the generator is `(κ/2 − 2)y² + (κ/2 − 1 + σ − 2a) y − a(1 − σ)`;
* `lyap` is antitone and tends to `+∞` at `0` (`lyap_antitoneOn`, `neg_log_le_lyap`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Zhan

namespace LowerGap

open Sec4 (cothHalf)

/-! ### `coth(·/2)` and the tamed drift -/

theorem exp_sub_one_pos {x : ℝ} (hx : 0 < x) : 0 < Real.exp x - 1 := by
  have := Real.add_one_lt_exp hx.ne'; linarith

theorem exp_sub_one_ne {x : ℝ} (hx : x ≠ 0) : Real.exp x - 1 ≠ 0 := by
  rw [sub_ne_zero]; exact fun h => hx (Real.exp_eq_one_iff x |>.1 h)

theorem hasDerivAt_cothHalf {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt cothHalf (-(2 * Real.exp x) / (Real.exp x - 1) ^ 2) x := by
  have hd := exp_sub_one_ne hx
  have h := ((Real.hasDerivAt_exp x).add_const 1).div ((Real.hasDerivAt_exp x).sub_const 1) hd
  refine h.congr_deriv ?_
  field_simp
  ring

theorem abs_deriv_cothHalf_le {c x : ℝ} (hc : 0 < c) (hx : c ≤ x) :
    |-(2 * Real.exp x) / (Real.exp x - 1) ^ 2| ≤ 2 / (Real.exp c - 1) + 2 / (Real.exp c - 1) ^ 2 := by
  have hd := exp_sub_one_pos hc
  have hD : Real.exp c - 1 ≤ Real.exp x - 1 := by linarith [Real.exp_le_exp.2 hx]
  have hD0 : 0 < Real.exp x - 1 := hd.trans_le hD
  have he : -(2 * Real.exp x) / (Real.exp x - 1) ^ 2 =
      -(2 / (Real.exp x - 1) + 2 / (Real.exp x - 1) ^ 2) := by
    field_simp; ring
  rw [he, abs_neg, abs_of_pos (by positivity)]
  gcongr

/-- The tamed drift `C(max x c)`. -/
def tame (c x : ℝ) : ℝ := cothHalf (max x c)

theorem tame_of_le {c x : ℝ} (h : c ≤ x) : tame c x = cothHalf x := by
  simp [tame, max_eq_left h]

theorem lipschitzOnWith_cothHalf {c : ℝ} (hc : 0 < c) :
    LipschitzOnWith (Real.toNNReal (2 / (Real.exp c - 1) + 2 / (Real.exp c - 1) ^ 2)) cothHalf (Ici c) := by
  have hd := exp_sub_one_pos hc
  refine (convex_Ici c).lipschitzOnWith_of_nnnorm_hasDerivWithin_le
    (f' := fun x => -(2 * Real.exp x) / (Real.exp x - 1) ^ 2)
    (fun x hx => (hasDerivAt_cothHalf (hc.trans_le hx).ne').hasDerivWithinAt) fun x hx => ?_
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (by positivity), Real.norm_eq_abs]
  exact abs_deriv_cothHalf_le hc hx

theorem lipschitzWith_tame {c : ℝ} (hc : 0 < c) :
    LipschitzWith (Real.toNNReal (2 / (Real.exp c - 1) + 2 / (Real.exp c - 1) ^ 2) * 1) (tame c) := by
  have h := (lipschitzOnWith_cothHalf hc).comp
    ((LipschitzWith.id.max_const c).lipschitzOnWith (s := univ)) fun x _ => le_max_right x c
  exact lipschitzOnWith_univ.1 h

theorem one_le_tame {c : ℝ} (hc : 0 < c) (x : ℝ) : 1 ≤ tame c x :=
  Sec4.one_le_cothHalf (hc.trans_le (le_max_right x c))

theorem tame_le {c : ℝ} (hc : 0 < c) (x : ℝ) : tame c x ≤ cothHalf c :=
  Sec4.cothHalf_le_cothHalf hc (le_max_right x c)

theorem abs_tame_le {c : ℝ} (hc : 0 < c) (x : ℝ) : |tame c x| ≤ cothHalf c := by
  rw [abs_of_pos (zero_lt_one.trans_le (one_le_tame hc x))]
  exact tame_le hc x

/-! ### The Lyapunov function -/

/-- The Lyapunov function `−log(1 − e^{−x}) − a x` of the lower gap. -/
def lyap (a x : ℝ) : ℝ := -Real.log (1 - Real.exp (-x)) - a * x

/-- Its derivative `−(eˣ − 1)⁻¹ − a`. -/
def lyapD (a x : ℝ) : ℝ := -(Real.exp x - 1)⁻¹ - a

/-- Its second derivative `eˣ/(eˣ − 1)²`. -/
def lyapDD (x : ℝ) : ℝ := Real.exp x / (Real.exp x - 1) ^ 2

theorem one_sub_exp_neg_pos {x : ℝ} (hx : 0 < x) : 0 < 1 - Real.exp (-x) := by
  have := Real.exp_lt_exp.2 (neg_lt_zero.2 hx)
  rw [Real.exp_zero] at this
  linarith

theorem hasDerivAt_lyap (a : ℝ) {x : ℝ} (hx : 0 < x) : HasDerivAt (lyap a) (lyapD a x) x := by
  have h1 : HasDerivAt (fun y => 1 - Real.exp (-y)) (Real.exp (-x)) x := by
    have := ((Real.hasDerivAt_exp (-x)).comp x (hasDerivAt_neg x)).const_sub 1
    simpa using this
  have h2 := ((h1.log (one_sub_exp_neg_pos hx).ne').neg).sub ((hasDerivAt_id x).const_mul a)
  refine h2.congr_deriv ?_
  have hd := exp_sub_one_pos hx
  have hn := one_sub_exp_neg_pos hx
  rw [lyapD, Real.exp_neg]
  have he : (0 : ℝ) < Real.exp x := Real.exp_pos x
  field_simp

theorem hasDerivAt_lyapD (a : ℝ) {x : ℝ} (hx : x ≠ 0) : HasDerivAt (lyapD a) (lyapDD x) x := by
  have h := (((Real.hasDerivAt_exp x).sub_const 1).inv (exp_sub_one_ne hx)).neg.sub_const a
  refine h.congr_deriv ?_
  rw [lyapDD]
  ring

theorem contDiffOn_lyap (a : ℝ) : ContDiffOn ℝ (⊤ : ℕ∞) (lyap a) (Ioi 0) := by
  unfold lyap
  have h1 : ContDiffOn ℝ (⊤ : ℕ∞) (fun y : ℝ => 1 - Real.exp (-y)) (Ioi 0) :=
    (contDiff_const.sub (Real.contDiff_exp.comp contDiff_neg)).contDiffOn
  exact (h1.log fun y hy => (one_sub_exp_neg_pos hy).ne').neg.sub (contDiffOn_const.mul contDiffOn_id)

theorem contDiffAt_lyap (a : ℝ) {x : ℝ} (hx : 0 < x) {n : ℕ∞} : ContDiffAt ℝ n (lyap a) x :=
  ((contDiffOn_lyap a).contDiffAt (isOpen_Ioi.mem_nhds hx)).of_le (by exact_mod_cast le_top)

/-- **The generator bound**: `lyapD a x (C(x) − σ) + (κ/2) lyapDD x ≤ 0` for `x > 0`. -/
theorem lyap_gen_nonpos {κ σ a x : ℝ} (hκ : κ ≤ 4) (hσ : σ ≤ 1) (ha : 0 ≤ a) (ha' : κ / 2 - 1 + σ ≤ 2 * a)
    (hx : 0 < x) : lyapD a x * (cothHalf x - σ) + κ / 2 * lyapDD x ≤ 0 := by
  have hd := exp_sub_one_pos hx
  set D := Real.exp x - 1 with hD
  have hE : Real.exp x = D + 1 := by rw [hD]; ring
  set y := D⁻¹ with hy
  have hy0 : 0 < y := inv_pos.2 hd
  have hD0 : D ≠ 0 := hd.ne'
  have hc : cothHalf x = 1 + 2 * y := by
    rw [cothHalf, hE, hy, add_sub_cancel_right]; field_simp; ring
  have hdd : lyapDD x = y + y ^ 2 := by
    rw [lyapDD, hE, add_sub_cancel_right, hy]; field_simp
  rw [lyapD, ← hD, ← hy, hc, hdd]
  have e : (-y - a) * (1 + 2 * y - σ) + κ / 2 * (y + y ^ 2) =
      (κ / 2 - 2) * y ^ 2 + (κ / 2 - 1 + σ - 2 * a) * y - a * (1 - σ) := by ring
  rw [e]
  have h1 : (κ / 2 - 2) * y ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  have h2 : (κ / 2 - 1 + σ - 2 * a) * y ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by linarith) hy0.le
  have h3 : 0 ≤ a * (1 - σ) := mul_nonneg ha (by linarith)
  linarith

/-- `lyap a` is antitone on `(0, ∞)` for `a ≥ 0`. -/
theorem lyap_antitoneOn {a : ℝ} (ha : 0 ≤ a) {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : lyap a y ≤ lyap a x := by
  have h1 : 1 - Real.exp (-x) ≤ 1 - Real.exp (-y) := by
    linarith [Real.exp_le_exp.2 (neg_le_neg hxy)]
  have h2 := Real.log_le_log (one_sub_exp_neg_pos hx) h1
  have h3 : a * x ≤ a * y := mul_le_mul_of_nonneg_left hxy ha
  unfold lyap
  linarith

/-- `lyap a x ≥ −log x − a x` for `x > 0`; in particular `lyap a x → ∞` as `x → 0⁺`. -/
theorem neg_log_le_lyap (a : ℝ) {x : ℝ} (hx : 0 < x) : -Real.log x - a * x ≤ lyap a x := by
  have h1 : 1 - Real.exp (-x) ≤ x := by linarith [Real.add_one_le_exp (-x)]
  have h2 := Real.log_le_log (one_sub_exp_neg_pos hx) h1
  unfold lyap
  linarith

end LowerGap

end Zhan

end InteractingSLE
