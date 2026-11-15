/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.CounterflowWords

/-!
# §7.4: deterministic steps of the pocket constructions (Aux. lemmas 119, 130; supplement §5.3–§5.4)

Packet PROVE-SEC7-D (specification §7.4, `source/spec/p385-432.md` L3–L55 (Aux. lemma 119, (PW13.2)–(PW13.4)),
L401–L424 (Aux. lemma 130); supplement §5.3–§5.4, `source/spec/p433-480.md` L952–L1000).

* **Aux. lemma 119, (PW13.3).** For real `q < v`, the Möbius map `M(w) = (w − v)/(w − q)` with lift
  `L_M(w) = log(v − q) − 2 Log(w − q)` (`pw133Map`, `pw133Lift`): `M` preserves `ℍ` (`mapsTo_pw133Map`), takes `v` to
  `0` (`pw133Map_self`), `L_M` is a derivative lift on `ℍ` (`isDerivLog_pw133Map`), its argument is exactly zero on
  `(q, ∞)` and `−2π` on `(−∞, q)` (`im_pw133Lift_of_lt`, `im_pw133Lift_of_gt`), and these are boundary limits
  (`continuousWithinAt_im_pw133Lift`). The alternative positive affine chart `w ↦ w − v` has derivative lift `0`
  (`isDerivLog_sub_const`).
* **Aux. lemma 130, boundary heights.** With `a, b ≥ λ + πχ/2` and `a', b' ≥ λ + 3πχ/2`, the four cumulative values of
  (5.4)–(5.5) are nonnegative for every angle in `[−π/2, π/2]`, hence at least `κ/2 − 2` (`aux130_heights`).
* **Supplement §5.3.** Two angles with difference strictly between `0` and `2π` give common-side heights that differ by
  a non-lattice amount: `(θ − θ')χ ∉ 2πχℤ` (`sub_mul_chiC_ne_two_pi_mul_int`).
* **Supplement §5.4.** The forbidden equation `επ/2 + π − θ + 2πn = 0` (`ε = ±1`, `n ∈ ℤ`) has no solution with
  `−π/2 < θ < π/2` (`forbidden_attachment_equation`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology
open scoped Real
open QuantumZipper (H chiC)

namespace InteractingSLE

namespace Sec7

open DerivLog

/-! ### Aux. lemma 119: the transition `M_p` of (PW13.3) -/

/-- `M(w) = (w − v)/(w − q)` (PW13.3), with `q = q_p < v = v_p`. -/
def pw133Map (q v : ℝ) (w : ℂ) : ℂ := (w - v) / (w - q)

/-- `L_M(w) = log(v − q) − 2 Log(w − q)` (PW13.3), the branch with `0 < Im Log(w − q) < π` on `ℍ`. -/
def pw133Lift (q v : ℝ) (w : ℂ) : ℂ := (Real.log (v - q) : ℂ) - 2 * log (w - q)

variable {q v : ℝ}

theorem pw133Map_self (q v : ℝ) : pw133Map q v v = 0 := by simp [pw133Map]

/-- `M` preserves `ℍ` (positive determinant `v − q`). -/
theorem mapsTo_pw133Map (hqv : q < v) : MapsTo (pw133Map q v) H H := by
  intro w hw
  have := Sec4.div_add_mem_H hw (show -v < -q by linarith)
  simpa [pw133Map, sub_eq_add_neg] using this

/-- `L_M` is a derivative lift of `M` on `ℍ`: `M'(w) = (v − q)/(w − q)²`. -/
theorem isDerivLog_pw133Map (hqv : q < v) : IsDerivLog (pw133Map q v) (pw133Lift q v) H := by
  refine ⟨fun w hw => ?_, fun w hw => ?_⟩
  · have hs : w - q ∈ slitPlane := mem_slitPlane_of_mem_H (sub_ofReal_mem_H hw q)
    exact (((differentiableAt_const _).sub
      (((differentiableAt_id.sub_const _).clog hs).const_mul 2))).differentiableWithinAt
  · have hne : w - q ≠ 0 := ne_zero_of_mem_H (sub_ofReal_mem_H hw q)
    have hd : HasDerivAt (pw133Map q v) ((1 * (w - q) - (w - v) * 1) / (w - q) ^ 2) w :=
      ((hasDerivAt_id w).sub_const _).div ((hasDerivAt_id w).sub_const _) hne
    rw [hd.deriv, pw133Lift, exp_sub, ← ofReal_exp, Real.exp_log (by linarith),
      show (2 : ℂ) * log (w - q) = (2 : ℕ) * log (w - q) by norm_num, exp_nat_mul, exp_log hne]
    push_cast
    ring

theorem im_pw133Lift (q v : ℝ) (w : ℂ) : (pw133Lift q v w).im = -2 * arg (w - q) := by
  simp [pw133Lift, log_im]

/-- The derivative argument of `M` is exactly zero on `(q, ∞)`. -/
theorem im_pw133Lift_of_lt {x : ℝ} (hx : q < x) : (pw133Lift q v x).im = 0 := by
  rw [im_pw133Lift, ← ofReal_sub, arg_ofReal_of_nonneg (by linarith)]; ring

/-- On `(−∞, q)` it is `−2π`. -/
theorem im_pw133Lift_of_gt {x : ℝ} (hx : x < q) : (pw133Lift q v x).im = -2 * π := by
  rw [im_pw133Lift, ← ofReal_sub, arg_ofReal_of_neg (by linarith)]

/-- The boundary values above are limits from `ℍ`. -/
theorem continuousWithinAt_im_pw133Lift {x : ℝ} (hx : x ≠ q) :
    ContinuousWithinAt (fun w => (pw133Lift q v w).im) {w : ℂ | 0 ≤ w.im} x := by
  simp only [im_pw133Lift]
  have hne : (x : ℂ) - q ≠ 0 := by
    rw [← ofReal_sub]; exact ofReal_ne_zero.2 (sub_ne_zero.2 hx)
  have hg : ContinuousWithinAt (fun w : ℂ => w - (q : ℂ)) {w : ℂ | 0 ≤ w.im} (x : ℂ) :=
    (continuous_sub_right _).continuousWithinAt
  have h := ContinuousWithinAt.comp (g := arg) (f := fun w : ℂ => w - (q : ℂ))
    (t := {w : ℂ | 0 ≤ w.im}) (Sec4.continuousWithinAt_arg_closedUpper hne (by simp)) hg
    (fun w (hw : 0 ≤ w.im) => by show 0 ≤ (w - (q : ℂ)).im; simpa using hw)
  exact continuousWithinAt_const.mul h

/-- The positive affine chart `w ↦ w − v` (the case where `y₀` is the original target) has derivative lift `0`. -/
theorem isDerivLog_sub_const (v : ℝ) (D : Set ℂ) : IsDerivLog (fun w : ℂ => w - v) (fun _ => 0) D := by
  refine ⟨differentiableOn_const _, fun w _ => ?_⟩
  have hd : HasDerivAt (fun w : ℂ => w - v) 1 w := (hasDerivAt_id' w).sub_const _
  rw [hd.deriv, exp_zero]

/-! ### Aux. lemma 130: large original boundary heights -/

/-- **Aux. lemma 130, boundary heights**: for `0 < κ < 4`, `θ ∈ [−π/2, π/2]`, `a, b ≥ λ + πχ/2` and
`a', b' ≥ λ + 3πχ/2`, the four cumulative values of (5.4)–(5.5) are nonnegative, hence at least `κ/2 − 2`. -/
theorem aux130_heights {κ θ a b a' b' : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
    (hθ : θ ∈ Icc (-(π / 2)) (π / 2)) (ha : sleLambda κ + π * chiC κ / 2 ≤ a)
    (hb : sleLambda κ + π * chiC κ / 2 ≤ b) (ha' : sleLambda κ + 3 * π * chiC κ / 2 ≤ a')
    (hb' : sleLambda κ + 3 * π * chiC κ / 2 ≤ b') :
    (0 ≤ (a - θ * chiC κ) / sleLambda κ - 1 ∧ 0 ≤ (b + θ * chiC κ) / sleLambda κ - 1 ∧
      0 ≤ (a' - (θ + π) * chiC κ) / sleLambda κ - 1 ∧ 0 ≤ (b' + (θ - π) * chiC κ) / sleLambda κ - 1) ∧
    (κ / 2 - 2 ≤ (a - θ * chiC κ) / sleLambda κ - 1 ∧ κ / 2 - 2 ≤ (b + θ * chiC κ) / sleLambda κ - 1 ∧
      κ / 2 - 2 ≤ (a' - (θ + π) * chiC κ) / sleLambda κ - 1 ∧
      κ / 2 - 2 ≤ (b' + (θ - π) * chiC κ) / sleLambda κ - 1) := by
  have hl := Sec4.sleLambda_pos hκ
  have hχ := Sec4.chiC_pos hκ hκ4
  have h1 : θ * chiC κ ≤ π / 2 * chiC κ := mul_le_mul_of_nonneg_right hθ.2 hχ.le
  have h2 : -(π / 2) * chiC κ ≤ θ * chiC κ := mul_le_mul_of_nonneg_right hθ.1 hχ.le
  have key : ∀ x : ℝ, sleLambda κ ≤ x → 0 ≤ x / sleLambda κ - 1 := fun x hx => by
    rw [sub_nonneg, le_div_iff₀ hl, one_mul]; exact hx
  have e1 : 0 ≤ (a - θ * chiC κ) / sleLambda κ - 1 := key _ (by nlinarith)
  have e2 : 0 ≤ (b + θ * chiC κ) / sleLambda κ - 1 := key _ (by nlinarith)
  have e3 : 0 ≤ (a' - (θ + π) * chiC κ) / sleLambda κ - 1 := key _ (by nlinarith)
  have e4 : 0 ≤ (b' + (θ - π) * chiC κ) / sleLambda κ - 1 := key _ (by nlinarith)
  have hk : κ / 2 - 2 < 0 := by linarith
  exact ⟨⟨e1, e2, e3, e4⟩, ⟨by linarith, by linarith, by linarith, by linarith⟩⟩

/-! ### Supplement §5.3–§5.4: angle-lattice exclusions -/

/-- **Supplement §5.3**: two angles with `0 < |θ − θ'| < 2π` give common-side heights differing by
`(θ − θ')χ`, which is not in the branch lattice `2πχℤ` (`χ ≠ 0`). -/
theorem sub_mul_chiC_ne_two_pi_mul_int {θ θ' X : ℝ} (hX : X ≠ 0) (h0 : θ ≠ θ') (h2 : |θ - θ'| < 2 * π)
    (n : ℤ) : (θ - θ') * X ≠ 2 * π * n * X := by
  intro h
  have he : θ - θ' = 2 * π * n := mul_right_cancel₀ hX (by linarith [h])
  have hπ := Real.pi_pos
  rcases lt_trichotomy n 0 with hn | rfl | hn
  · have : (n : ℝ) ≤ -1 := by exact_mod_cast Int.le_sub_one_of_lt hn
    rw [he, abs_lt] at h2; nlinarith [h2.1]
  · simp at he; exact h0 (by linarith)
  · have : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [he, abs_lt] at h2; nlinarith [h2.2]

/-- **Supplement §5.4, the forbidden equation**: progress of a contained strict-angle attachment during a no-`C`
interval would give `επ/2 + π − θ + 2πn = 0` with `ε = ±1`, `n ∈ ℤ`; for `−π/2 < θ < π/2` it has no solution. -/
theorem forbidden_attachment_equation {θ : ℝ} (hθ : θ ∈ Ioo (-(π / 2)) (π / 2)) {ε : ℝ}
    (hε : ε = -1 ∨ ε = 1) (n : ℤ) : ε * (π / 2) + π - θ + 2 * π * n ≠ 0 := by
  have hπ := Real.pi_pos
  obtain ⟨h1, h2⟩ := hθ
  intro h
  rcases le_or_gt n (-1) with hn | hn
  · have : (n : ℝ) ≤ -1 := by exact_mod_cast hn
    rcases hε with rfl | rfl <;> nlinarith
  · have : (0 : ℝ) ≤ n := by exact_mod_cast (show (0 : ℤ) ≤ n by omega)
    rcases hε with rfl | rfl <;> nlinarith

end Sec7

end InteractingSLE
