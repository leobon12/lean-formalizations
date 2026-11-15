/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.WordsEnergy
import InteractingSLE.Spec.Zhan.UpperPoint

/-!
# The left side error in strip coordinates

Packet PROVE-ZHAN-B4. In the strip chart of R36 whose left end is the outermost left mark `v` (Astra §3,
"map the outermost … group to the … strip end", L1586–L1592), a lower left mark `y` (`v < y < w`) has strip gap
`X = ξ − p = log((w − v)/(y − v))`, and the chordal side error term is a coth error:

  `(w − v)⁻¹ − (w − y)⁻¹ = −½ (coth(X/2) − 1)/(w − v)`   (`inv_sub_inv_eq_cothHalf`).

Hence the chordal energy of the left side error on `[0, S]` is the strip-time energy of the left coth error
`leftStripErr = Σᵢ (ρᵢ/2)(coth(Xᵢ/2) − 1)` on `[0, t(S)]` (`integral_sq_sideErr_eq`, substitution `u = t(s)`,
`dt/ds = (w − v)⁻²`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Zhan

open Strip

variable {n : ℕ} {w v : ℝ → ℝ} {S : ℝ}

theorem inv_sub_inv_eq_cothHalf {w v y : ℝ} (hvy : v < y) (hyw : y < w) :
    (w - v)⁻¹ - (w - y)⁻¹ = -(1 / 2) * (Sec4.cothHalf (Real.log ((w - v) / (y - v))) - 1) / (w - v) := by
  have h1 : 0 < y - v := by linarith
  have h2 : 0 < w - y := by linarith
  have h3 : 0 < w - v := by linarith
  rw [Sec4.cothHalf, Real.exp_log (div_pos h3 h1), div_add_one h1.ne', div_sub_one h1.ne',
    div_div_div_cancel_right₀ h1.ne']
  have e1 : w - v - (y - v) = w - y := by ring
  rw [e1]
  field_simp
  ring

/-- **The left coth error in strip time**: `Σᵢ (ρᵢ/2)(coth(Xᵢ/2) − 1)`, `Xᵢ = ξ − pᵢ` for the lower left marks `yᵢ`. -/
def leftStripErr (ρ : Fin n → ℝ) (w v : ℝ → ℝ) (y : Fin n → ℝ → ℝ) (u : ℝ) : ℝ :=
  ∑ i, ρ i / 2 * (Sec4.cothHalf (stripDriver w v u - stripPoint w v (y i) u) - 1)

/-- The strip gap at the strip time of a chordal time. -/
theorem stripDriver_sub_stripPoint (h : IsSepMark w v S) {y : ℝ → ℝ} {r : ℝ} (hr : r ∈ Icc 0 S)
    (hvy : v r < y r) :
    stripDriver w v (stripClock w v r) - stripPoint w v y (stripClock w v r) =
      Real.log ((w r - v r) / (y r - v r)) := by
  rw [stripDriver, stripPoint, h.chordalTime_stripClock hr, abs_of_pos (sub_pos.2 hvy),
    Real.log_div (sub_pos.2 (h.lt r hr)).ne' (sub_pos.2 hvy).ne']
  ring

/-- **The chordal side error is the strip coth error**: for a left side `Fin (n + 1)` whose last mark is the end
mark `v`, `sideErr ρ w vL = −leftStripErr/(w − v)` at chordal times of `[0, S]`. -/
theorem sideErr_eq_leftStripErr (h : IsSepMark w v S) {ρ : Fin (n + 1) → ℝ} {vL : Fin (n + 1) → ℝ → ℝ}
    (hlast : vL (Fin.last n) = v) {r : ℝ} (hr : r ∈ Icc 0 S)
    (hgap : ∀ i : Fin n, v r < vL i.castSucc r ∧ vL i.castSucc r < w r) :
    sideErr ρ (w r) (fun i => vL i r) =
      -leftStripErr (fun i => ρ i.castSucc) w v (fun i => vL i.castSucc) (stripClock w v r) / (w r - v r) := by
  simp only [sideErr, lastOf_eq_last, hlast, leftStripErr]
  rw [Fin.sum_univ_castSucc, hlast, sub_self, mul_zero, add_zero, ← Finset.sum_neg_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inv_sub_inv_eq_cothHalf (hgap i).1 (hgap i).2,
    stripDriver_sub_stripPoint h hr (hgap i).1]
  ring

/-- The strip gap of a lower left mark is positive at every strip time of `[0, t(S)]`. -/
theorem stripDriver_sub_stripPoint_pos (h : IsSepMark w v S) {y : ℝ → ℝ}
    (hgap : ∀ r ∈ Icc 0 S, v r < y r ∧ y r < w r) {u : ℝ} (hu : u ∈ Icc 0 (stripClock w v S)) :
    0 < stripDriver w v u - stripPoint w v y u := by
  have hs := h.chordalTime_mem hu
  obtain ⟨h1, h2⟩ := hgap _ hs
  rw [stripDriver, stripPoint, abs_of_pos (sub_pos.2 h1)]
  have := Real.log_lt_log (sub_pos.2 h1) (show y (chordalTime w v u) - v (chordalTime w v u) <
    w (chordalTime w v u) - v (chordalTime w v u) by linarith)
  linarith

theorem continuousOn_cothHalf_of_ne : ContinuousOn Sec4.cothHalf {x | x ≠ 0} := by
  refine ((Real.continuous_exp.add continuous_const).continuousOn).div
    ((Real.continuous_exp.sub continuous_const).continuousOn) fun x hx => ?_
  rw [sub_ne_zero]
  exact fun he => hx (Real.exp_eq_one_iff x |>.1 he)

/-- The left coth error is continuous on `[0, t(S)]`. -/
theorem continuousOn_leftStripErr (h : IsSepMark w v S) (ρ : Fin n → ℝ) {y : Fin n → ℝ → ℝ}
    (hy : ∀ i, ContinuousOn (y i) (Icc 0 S)) (hgap : ∀ r ∈ Icc 0 S, ∀ i, v r < y i r ∧ y i r < w r) :
    ContinuousOn (leftStripErr ρ w v y) (Icc 0 (stripClock w v S)) := by
  refine continuousOn_finsetSum _ fun i _ => ?_
  have hd : ContinuousOn (fun u => stripDriver w v u - stripPoint w v (y i) u) (Icc 0 (stripClock w v S)) :=
    h.continuousOn_stripDriver.sub (h.continuousOn_stripPoint (hy i) fun r hr => (hgap r hr i).1.ne')
  refine continuousOn_const.mul ((continuousOn_cothHalf_of_ne.comp hd fun u hu => ?_).sub continuousOn_const)
  exact (stripDriver_sub_stripPoint_pos h (fun r hr => hgap r hr i) hu).ne'

/-- **Chordal side energy = strip-time coth energy** on `[0, S]` (substitution `u = t(s)`). -/
theorem integral_sq_sideErr_eq (h : IsSepMark w v S) {ρ : Fin (n + 1) → ℝ} {vL : Fin (n + 1) → ℝ → ℝ}
    (hlast : vL (Fin.last n) = v) (hy : ∀ i : Fin n, ContinuousOn (vL i.castSucc) (Icc 0 S))
    (hgap : ∀ r ∈ Icc 0 S, ∀ i : Fin n, v r < vL i.castSucc r ∧ vL i.castSucc r < w r) :
    ∫ r in (0 : ℝ)..S, (sideErr ρ (w r) (fun i => vL i r)) ^ 2 =
      ∫ u in (0 : ℝ)..(stripClock w v S),
        (leftStripErr (fun i => ρ i.castSucc) w v (fun i => vL i.castSucc) u) ^ 2 := by
  have hS := h.nonneg
  have hcont := continuousOn_leftStripErr h (fun i => ρ i.castSucc) hy hgap
  have hcs := intervalIntegral.integral_comp_mul_deriv'' (a := 0) (b := S) (f := stripClock w v)
    (f' := fun r => ((w r - v r) ^ 2)⁻¹)
    (g := fun u => (leftStripErr (fun i => ρ i.castSucc) w v (fun i => vL i.castSucc) u) ^ 2)
    (by rw [uIcc_of_le hS]; exact h.continuousOn_stripClock)
    (fun x hx => by
      rw [min_eq_left hS, max_eq_right hS] at hx
      exact (h.hasDerivAt_stripClock hx).hasDerivWithinAt)
    (by rw [uIcc_of_le hS]; exact h.continuousOn_inv_sq)
    (by
      rw [uIcc_of_le hS]
      refine (hcont.pow 2).mono ?_
      rintro _ ⟨r, hr, rfl⟩
      exact ⟨h.stripClock_nonneg hr, h.strictMonoOn_stripClock.monotoneOn hr ⟨hS, le_rfl⟩ hr.2⟩)
  have h0 : stripClock w v 0 = 0 := by simp [stripClock]
  rw [h0] at hcs
  rw [← hcs]
  refine intervalIntegral.integral_congr fun r hr => ?_
  rw [uIcc_of_le hS] at hr
  have hw : w r - v r ≠ 0 := (sub_pos.2 (h.lt r hr)).ne'
  simp only [Function.comp_apply]
  rw [sideErr_eq_leftStripErr h hlast hr (hgap r hr)]
  field_simp

end InteractingSLE.Zhan
