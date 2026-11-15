/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInRealLanding
import InteractingSLE.Spec.Sec7.CounterflowWords

/-!
# Exact initial heights through the compatible Aux. 120 inversion

PROVE-POCKET-SIDEIN. The boundary limits use the inherited inverse lift
2πi - 2 Log z. On the negative real side Log is continuous from the closed
upper half-plane, not from a full complex neighborhood. The limits retain
the exact integer branch and yield the centered seed heights of Aux. 120.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology Complex
open scoped Real
open QuantumZipper (H Hbar chiC)

namespace InteractingSLE.Sec7.PocketStopSide

/-- The compatible inverse lift has the exact one-sided boundary values
0 on the negative half-line and 2π on the positive half-line. -/
theorem tendsto_im_compatible_inverse_lift {x : ℝ} (hx : x ≠ 0) :
    Tendsto (fun z : ℂ => (2 * π * I - 2 * log z).im) (𝓝[H] (x : ℂ))
      (𝓝 (if x < 0 then 0 else 2 * π)) := by
  have hlog : ContinuousWithinAt log Hbar (x : ℂ) := by
    rcases lt_or_gt_of_ne hx with hneg | hpos
    · exact continuousWithinAt_log_of_re_neg_of_im_zero (by simpa using hneg) (by simp)
    · exact (continuousAt_clog (Or.inl (by simpa using hpos))).continuousWithinAt
  have hΛ : ContinuousWithinAt (fun z : ℂ => (2 * π * I - 2 * log z).im) Hbar (x : ℂ) :=
    Complex.continuous_im.continuousAt.comp_continuousWithinAt
      (continuousWithinAt_const.sub (continuousWithinAt_const.mul hlog))
  have hlim := (hΛ.mono QuantumZipper.H_subset_Hbar).tendsto
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · simpa only [ite_eq_left hneg, im_inv_lift_of_neg hneg] using hlim
  · simpa only [ite_eq_right (not_lt.2 hpos.le), im_inv_lift_of_pos hpos] using hlim

/-- A finite exact height is transported through the actual inversion and
its compatible inherited inverse lift. No independent branch is selected. -/
theorem tendsto_height_through_compatible_inversion {M : ℂ → ℝ} {x : ℝ} (hx : x ≠ 0)
    {b X c : ℝ} (hHeight : Tendsto M (𝓝[H] (-((x : ℂ)⁻¹))) (𝓝 b)) :
    Tendsto (fun z => -coordChange X (fun w => -w⁻¹)
      (fun w => 2 * π * I - 2 * log w) M z + c) (𝓝[H] (x : ℂ))
      (𝓝 (-b + X * (if x < 0 then 0 else 2 * π) + c)) := by
  have hxn : (x : ℂ) ≠ 0 := ofReal_ne_zero.2 hx
  have hInv : Tendsto (fun z : ℂ => -z⁻¹) (𝓝[H] (x : ℂ))
      (𝓝[H] (-((x : ℂ)⁻¹))) := by
    refine tendsto_nhdsWithin_iff.2
      ⟨((continuousAt_id.inv₀ hxn).neg).tendsto.mono_left nhdsWithin_le_nhds, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact Chart.isConformal_infinitySourceChart.2.1 hz
  have hlim := ((hHeight.comp hInv).neg.add
    ((tendsto_im_compatible_inverse_lift hx).const_mul X)).add_const c
  refine hlim.congr fun z => ?_
  dsimp only [coordChange, Function.comp_def]
  ring

/-- Aux. 120's displayed initial heights are actual boundary limits when
the original flow-coordinate mean has the corresponding exact wall height. -/
theorem tendsto_if91Height_of_flow_height {κ θ₁ θ₂ c : ℝ} {M : ℂ → ℝ} {x : ℝ} (hx : x ≠ 0)
    (hFlowHeight : Tendsto M (𝓝[H] (-((x : ℂ)⁻¹)))
      (𝓝 (cf92Lower κ θ₁ θ₂ (-x⁻¹)))) :
    Tendsto (fun z => -coordChange (chiC κ) (fun w => -w⁻¹)
      (fun w => 2 * π * I - 2 * log w) M z + c) (𝓝[H] (x : ℂ))
      (𝓝 (if91Heights κ θ₁ θ₂ c x)) := by
  have hlim := tendsto_height_through_compatible_inversion (X := chiC κ) (c := c) hx hFlowHeight
  have hreal : (-((x : ℂ)⁻¹)).re = -x⁻¹ := by simp
  have harg : (2 * π * I - 2 * log (x : ℂ)).im = if x < 0 then 0 else 2 * π := by
    rcases lt_or_gt_of_ne hx with hneg | hpos
    · simpa only [ite_eq_left hneg] using im_inv_lift_of_neg hneg
    · simpa only [ite_eq_right (not_lt.2 hpos.le)] using im_inv_lift_of_pos hpos
  have heq := if91Heights_eq_coordChange (κ := κ) (θ₁ := θ₁) (θ₂ := θ₂) (c := c) hx
  dsimp only [coordChange] at heq
  rw [hreal, harg] at heq
  have heq' : -cf92Lower κ θ₁ θ₂ (-x⁻¹) +
      chiC κ * (if x < 0 then 0 else 2 * π) + c = if91Heights κ θ₁ θ₂ c x := by
    linarith only [heq]
  rwa [heq'] at hlim

/-- The centered negative incoming height is the exact left seed height. -/
theorem tendsto_centered_initial_height_neg {κ θ₁ θ₂ : ℝ} (hκ : 0 < κ)
    {M : ℂ → ℝ} {x : ℝ} (hx : x < 0)
    (hFlowHeight : Tendsto M (𝓝[H] (-((x : ℂ)⁻¹)))
      (𝓝 (cf92Lower κ θ₁ θ₂ (-x⁻¹)))) :
    Tendsto (fun z => -coordChange (chiC κ) (fun w => -w⁻¹)
      (fun w => 2 * π * I - 2 * log w) M z - π * chiC κ) (𝓝[H] (x : ℂ))
      (𝓝 (-sleLambda (16 / κ) * (1 + cf95RhoL κ θ₁))) := by
  have hlim := tendsto_if91Height_of_flow_height (c := -(π * chiC κ)) hx.ne hFlowHeight
  rw [if91Heights_centered_neg hκ hx] at hlim
  simpa only [sub_eq_add_neg] using hlim

/-- The centered positive incoming height is the exact right seed height. -/
theorem tendsto_centered_initial_height_pos {κ θ₁ θ₂ : ℝ} (hκ : 0 < κ)
    {M : ℂ → ℝ} {x : ℝ} (hx : 0 < x)
    (hFlowHeight : Tendsto M (𝓝[H] (-((x : ℂ)⁻¹)))
      (𝓝 (cf92Lower κ θ₁ θ₂ (-x⁻¹)))) :
    Tendsto (fun z => -coordChange (chiC κ) (fun w => -w⁻¹)
      (fun w => 2 * π * I - 2 * log w) M z - π * chiC κ) (𝓝[H] (x : ℂ))
      (𝓝 (sleLambda (16 / κ) * (1 + cf95RhoR κ θ₂))) := by
  have hlim := tendsto_if91Height_of_flow_height (c := -(π * chiC κ)) hx.ne' hFlowHeight
  rw [if91Heights_centered_pos hκ hx] at hlim
  simpa only [sub_eq_add_neg] using hlim

end InteractingSLE.Sec7.PocketStopSide
