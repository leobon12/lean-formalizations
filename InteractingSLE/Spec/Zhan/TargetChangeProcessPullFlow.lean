/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.TargetChangeProcessTime
import QuantumZipper.Proofs.Loewner.ForwardODE

/-!
# The retargeting family carries the complex Loewner flow

Packet PROVE-SEC7-C10 (step R6 of `planning/handoffs/PROVE-SEC7-C8.md`, the trace pullback; Specification §7.3,
pp. 378–379, and supplement Lemma LP9, p. 486). PROVE-SEC7-C8 proved that `M_t(x) = β_t + α_t/(V_t − x)` carries
the real Loewner flow of every force point to the Loewner flow driven by `W̃ = M(W)` in the clock
`ds = α² q⁻⁴ dt` (`mob_eq_add_integral`). This file proves the same for the complex flow of a point `z ∈ ℍ`: if `u`
solves the centered forward flow of `W` from `z` on `[0, S]` (so `g_s(z) = u_s + W_s`), then

  `ũ(r) = M_s(g_s(z)) − M_s(W_s)`,  `s = C⁻¹(r)`,

solves the centered forward flow of `W̃` from `ψ(z) = M_0(z)` on `[0, C(S)]` (`isForwardSol_retarget`).

Here the flow of `z` is `C¹` (its velocity `2/u` is continuous and `u ≠ 0`), the target `V` is `C¹` before the
separation, and the ordinary fundamental theorem of calculus applies; the algebra is that of `mob_deriv_alg` over `ℂ`
(`mobC_deriv_alg`), and the change of variables is `integral_clk_eq` for complex integrands
(`IsRate.integral_clk_eq_complex`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal
open QuantumZipper (IsForwardSol)

namespace InteractingSLE

namespace Zhan

namespace Retarget

/-! ### The complex retargeting map -/

/-- The retargeting map at time `t` on `ℂ`, `M_t(ζ) = β_t + α_t/(V_t − ζ)`. -/
def mobC (xk : ℝ) (w vk : ℝ≥0 → ℝ) (t : ℝ) (ζ : ℂ) : ℂ :=
  (beta xk w vk t : ℂ) + (alpha xk w vk t : ℂ) / ((vk t.toNNReal : ℂ) - ζ)

theorem mobC_ofReal (xk : ℝ) (w vk : ℝ≥0 → ℝ) (t x : ℝ) :
    mobC xk w vk t (x : ℂ) = (mob xk w vk t x : ℂ) := by
  simp only [mobC, mob]
  push_cast
  ring

/-- At time `0`, `M_0(z) = z/(x_k − z)` (the target change `ψ` of (C1)) when `V_0 = x_k`. -/
theorem mobC_zero {xk : ℝ} {w vk : ℝ≥0 → ℝ} (h0 : vk 0 = xk) {z : ℂ} (hz : (xk : ℂ) - z ≠ 0) :
    mobC xk w vk 0 z = z / ((xk : ℂ) - z) := by
  simp only [mobC, beta_zero, alpha_zero, Real.toNNReal_zero, h0]
  field_simp
  push_cast
  ring

/-- The algebra of the target change over `ℂ` (`mob_deriv_alg` with a complex `D`): with `q = V − w` real,
`D = V − g` and `a = g − w = q − D`, `β' + α' D⁻¹ − α D'/D² = (α²/q⁴) · 2/(α/D − α/q)`. -/
theorem mobC_deriv_alg {α q : ℝ} {D : ℂ} (hα : α ≠ 0) (hq : q ≠ 0) (hD : D ≠ 0) (ha : (q : ℂ) - D ≠ 0) :
    -2 * ((α : ℂ) / (q : ℂ) ^ 3) + (-2 * (α : ℂ) * ((q : ℂ) ^ 2)⁻¹ * D⁻¹ +
        (α : ℂ) * (-(2 / (q : ℂ) - 2 / ((q : ℂ) - D)) / D ^ 2)) =
      ((α ^ 2 / q ^ 4 : ℝ) : ℂ) * (2 / ((α : ℂ) / D - (α : ℂ) / q)) := by
  have hα' : (α : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hα
  have hq' : (q : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hq
  have h1 : (α : ℂ) / D - α / q = α * (q - D) / (D * q) := by field_simp
  rw [h1]
  push_cast
  field_simp
  ring

/-! ### The change of variables for complex integrands -/

namespace IsRate

variable {σ : ℝ → ℝ} {S : ℝ}

/-- **Change of variables** `u = C(s)` for a complex integrand: `∫₀^{C(S)} g = ∫₀^S σ · (g ∘ C)`. -/
theorem integral_clk_eq_complex (h : IsRate σ S) (g : ℝ → ℂ) :
    ∫ u in (0 : ℝ)..clk σ S, g u = ∫ s in (0 : ℝ)..S, (σ s : ℂ) * g (clk σ s) := by
  have hC0 : 0 ≤ clk σ S := h.clk_nonneg ⟨h.nonneg, le_rfl⟩
  rw [intervalIntegral.integral_of_le hC0, intervalIntegral.integral_of_le h.nonneg,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo, ← h.image_clk_Ioo,
    integral_image_eq_integral_abs_deriv_smul measurableSet_Ioo
      (fun s hs => (h.hasDerivAt_clk hs).hasDerivWithinAt)
      (h.strictMonoOn_clk.injOn.mono Ioo_subset_Icc_self) g]
  refine setIntegral_congr_fun measurableSet_Ioo fun s hs => ?_
  rw [abs_of_pos (h.pos s (Ioo_subset_Icc_self hs)), Complex.real_smul]

end IsRate

/-! ### Forward solutions -/

section Flow

variable {w vk : ℝ≥0 → ℝ} {S xk : ℝ}

/-- A forward solution started in `ℍ` stays in `ℍ`, for a driver only continuous on `[0, S]` (extend it by the
projection onto `[0, S]` and use QuantumZipper's `im_isForwardSol_le`). -/
theorem im_pos_of_isForwardSol (hS : 0 ≤ S) (hw : ContinuousOn (fun s : ℝ => w s.toNNReal) (Icc 0 S))
    {z : ℂ} (hz : 0 < z.im) {u : ℝ → ℂ} (hu : IsForwardSol (fun s : ℝ => w s.toNNReal) z S u) :
    ∀ s ∈ Icc 0 S, 0 < (u s).im := by
  set W' : ℝ → ℝ := fun s => w ((projIcc 0 S hS s : ℝ)).toNNReal with hW'
  have hW'c : Continuous W' :=
    hw.comp_continuous (continuous_subtype_val.comp continuous_projIcc) fun s => (projIcc 0 S hS s).2
  have hu' : IsForwardSol W' z S u := QuantumZipper.isForwardSol_congr_drive
    (fun r hr => by simp only [hW', projIcc_of_mem hS hr]) hu
  exact (QuantumZipper.im_isForwardSol_le hW'c hz hu').2

/-- The non-centered flow `g_s(z) = u_s + W_s` is `z + ∫₀ˢ 2/u`. -/
theorem add_eq_add_integral {z : ℂ} {u : ℝ → ℂ} (hu : IsForwardSol (fun s : ℝ => w s.toNNReal) z S u)
    {s : ℝ} (hs : s ∈ Icc 0 S) :
    u s + (w s.toNNReal : ℂ) = z + ∫ r in (0 : ℝ)..s, 2 / u r := by
  rw [(hu.2 s hs).2]
  ring

/-- A path `x + ∫₀ˢ f` with `f` continuous on `[0, S]` has derivative `f s` at interior times. -/
theorem hasDerivAt_of_eq_add_integral_complex {g f : ℝ → ℂ} {x : ℂ} (hf : ContinuousOn f (Icc 0 S))
    (hg : ∀ s ∈ Icc 0 S, g s = x + ∫ r in (0 : ℝ)..s, f r) {s : ℝ} (hs : s ∈ Ioo 0 S) :
    HasDerivAt g (f s) s := by
  have hfo : ContinuousOn f (Ioo 0 S) := hf.mono Ioo_subset_Icc_self
  have hI : HasDerivAt (fun t => ∫ r in (0 : ℝ)..t, f r) (f s) s :=
    intervalIntegral.integral_hasDerivAt_right
      ((hf.mono (uIcc_subset_Icc ⟨le_rfl, hs.1.le.trans hs.2.le⟩ ⟨hs.1.le, hs.2.le⟩)).intervalIntegrable)
      (hfo.stronglyMeasurableAtFilter isOpen_Ioo s hs) (hfo.continuousAt (isOpen_Ioo.mem_nhds hs))
  refine (hI.const_add x).congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht using hg t (Ioo_subset_Icc_self ht)

/-- **The image of the complex flow in the original clock**: for a forward solution `u` from `z ∈ ℍ` on `[0, S]`,
`M_S(g_S(z)) = M_0(z) + ∫₀ˢ rate · 2/(M(g(z)) − M(W))`, with `g_s(z) = u_s + W_s`. -/
theorem mobC_flow_eq (h : IsSep w vk S) (hxk : 0 < xk)
    (hk : ∀ s ∈ Icc 0 S, vk s.toNNReal = xk + ∫ u in (0 : ℝ)..s, 2 / (vk u.toNNReal - w u.toNNReal))
    {z : ℂ} (hz : 0 < z.im) {u : ℝ → ℂ} (hu : IsForwardSol (fun s : ℝ => w s.toNNReal) z S u) :
    mobC xk w vk S (u S + (w S.toNNReal : ℂ)) = mobC xk w vk 0 z +
      ∫ s in (0 : ℝ)..S, (rate xk w vk s : ℂ) *
        (2 / (mobC xk w vk s (u s + (w s.toNNReal : ℂ)) - (mobPath xk w vk w s : ℂ))) := by
  have hS := h.nonneg
  set g : ℝ → ℂ := fun s => u s + (w s.toNNReal : ℂ) with hgdef
  have him := im_pos_of_isForwardSol hS h.cont_w hz hu
  have hu0 : ∀ s ∈ Icc 0 S, u s ≠ 0 := fun s hs => (hu.2 s hs).1
  have hcW : ContinuousOn (fun s : ℝ => ((w s.toNNReal : ℝ) : ℂ)) (Icc 0 S) :=
    Complex.continuous_ofReal.comp_continuousOn h.cont_w
  have hcV : ContinuousOn (fun s : ℝ => ((vk s.toNNReal : ℝ) : ℂ)) (Icc 0 S) :=
    Complex.continuous_ofReal.comp_continuousOn h.cont_vk
  have hcg : ContinuousOn g (Icc 0 S) := hu.1.add hcW
  have hD : ∀ s ∈ Icc 0 S, ((vk s.toNNReal : ℝ) : ℂ) - g s ≠ 0 := fun s hs he => by
    have := congrArg Complex.im he
    simp only [hgdef, Complex.sub_im, Complex.ofReal_im, Complex.add_im, Complex.zero_im] at this
    linarith [him s hs]
  have hcG : ContinuousOn (fun s => mobC xk w vk s (g s)) (Icc 0 S) :=
    (Complex.continuous_ofReal.comp_continuousOn h.continuousOn_beta).add
      ((Complex.continuous_ofReal.comp_continuousOn h.continuousOn_alpha).div (hcV.sub hcg) hD)
  have hcM : ContinuousOn (fun s => ((mobPath xk w vk w s : ℝ) : ℂ)) (Icc 0 S) :=
    Complex.continuous_ofReal.comp_continuousOn h.continuousOn_mobPath_w
  -- `M(g) − M(W) = α/D − α/q ≠ 0`
  have hdiff : ∀ s ∈ Icc 0 S, mobC xk w vk s (g s) - (mobPath xk w vk w s : ℂ) =
      (alpha xk w vk s : ℂ) / (((vk s.toNNReal : ℝ) : ℂ) - g s) -
        (alpha xk w vk s : ℂ) / (gap w vk s : ℂ) := fun s _ => by
    simp only [mobC, mobPath, mob, gap]
    push_cast
    ring
  have hne : ∀ s ∈ Icc 0 S, mobC xk w vk s (g s) - (mobPath xk w vk w s : ℂ) ≠ 0 := fun s hs => by
    rw [hdiff s hs]
    have hq : (gap w vk s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (h.gap_ne hs)
    have hα : (alpha xk w vk s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (alpha_pos hxk w vk s).ne'
    have hDs := hD s hs
    have e : (alpha xk w vk s : ℂ) / (((vk s.toNNReal : ℝ) : ℂ) - g s) -
        (alpha xk w vk s : ℂ) / (gap w vk s : ℂ) =
        (alpha xk w vk s : ℂ) * u s / ((((vk s.toNNReal : ℝ) : ℂ) - g s) * (gap w vk s : ℂ)) := by
      field_simp
      simp only [hgdef, gap]
      push_cast
      ring
    rw [e]
    exact div_ne_zero (mul_ne_zero hα (hu0 s hs)) (mul_ne_zero hDs hq)
  have hcf : ContinuousOn (fun s => (rate xk w vk s : ℂ) *
      (2 / (mobC xk w vk s (g s) - (mobPath xk w vk w s : ℂ)))) (Icc 0 S) :=
    (Complex.continuous_ofReal.comp_continuousOn h.continuousOn_rate).mul
      (continuousOn_const.div (hcG.sub hcM) hne)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hS hcG ?_
    (hcf.intervalIntegrable_of_Icc hS)
  · have hg0 : g 0 = z := by
      have := add_eq_add_integral hu (s := 0) ⟨le_rfl, hS⟩
      simpa [hgdef] using this
    simp only [hgdef] at hFTC hg0
    rw [hFTC, hg0]
    ring
  -- the derivative at interior times
  intro s hs
  have hsI : s ∈ Icc 0 S := Ioo_subset_Icc_self hs
  have hcu : ContinuousOn (fun r => 2 / u r) (Icc 0 S) := continuousOn_const.div hu.1 hu0
  have hgd : HasDerivAt g (2 / u s) s :=
    hasDerivAt_of_eq_add_integral_complex hcu (fun r hr => add_eq_add_integral hu hr) hs
  have hcq : ContinuousOn (fun r : ℝ => 2 / (vk r.toNNReal - w r.toNNReal)) (Icc 0 S) :=
    continuousOn_const.div h.continuousOn_gap fun _ hr => h.gap_ne hr
  have hVd : HasDerivAt (fun r : ℝ => vk r.toNNReal) (2 / (vk s.toNNReal - w s.toNNReal)) s := by
    have hI : HasDerivAt (fun t => ∫ r in (0 : ℝ)..t, 2 / (vk r.toNNReal - w r.toNNReal))
        (2 / (vk s.toNNReal - w s.toNNReal)) s :=
      intervalIntegral.integral_hasDerivAt_right
        ((hcq.mono (uIcc_subset_Icc ⟨le_rfl, hS⟩ ⟨hs.1.le, hs.2.le⟩)).intervalIntegrable)
        ((hcq.mono Ioo_subset_Icc_self).stronglyMeasurableAtFilter isOpen_Ioo s hs)
        ((hcq.mono Ioo_subset_Icc_self).continuousAt (isOpen_Ioo.mem_nhds hs))
    exact hasDerivAt_of_eq_add_integral hk hs hI
  have hVd' := hVd.ofReal_comp
  have hαd := (h.hasDerivAt_alpha (xk := xk) hs).ofReal_comp
  have hβd := (h.hasDerivAt_beta (xk := xk) hs).ofReal_comp
  have hDs := hD s hsI
  have hGd := hβd.add (hαd.mul ((hVd'.sub hgd).inv hDs))
  have hfun : (fun r => mobC xk w vk r (g r)) = fun r => ((beta xk w vk r : ℝ) : ℂ) +
      ((alpha xk w vk r : ℝ) : ℂ) * (((vk r.toNNReal : ℝ) : ℂ) - g r)⁻¹ := by
    funext r
    simp only [mobC, div_eq_mul_inv]
  rw [hfun]
  refine hGd.congr_deriv ?_
  have hq : gap w vk s ≠ 0 := h.gap_ne hsI
  have hα : alpha xk w vk s ≠ 0 := (alpha_pos hxk w vk s).ne'
  have hus : (gap w vk s : ℂ) - (((vk s.toNNReal : ℝ) : ℂ) - g s) = u s := by
    simp only [hgdef, gap]
    push_cast
    ring
  have ha : (gap w vk s : ℂ) - (((vk s.toNNReal : ℝ) : ℂ) - g s) ≠ 0 := by
    rw [hus]; exact hu0 s hsI
  have key := mobC_deriv_alg hα hq hDs ha
  rw [hus] at key
  rw [hdiff s hsI]
  have e1 : ((2 / (vk s.toNNReal - w s.toNNReal) : ℝ) : ℂ) = 2 / (gap w vk s : ℂ) := by
    simp only [gap]; push_cast; ring
  rw [e1, rate, ← key]
  simp only [Pi.sub_apply, Pi.inv_apply]
  push_cast
  ring

/-- The centered image flow in the new clock, `ũ(r) = M_s(g_s(z)) − M_s(W_s)` at `s = C⁻¹(r)`. -/
def newFlow (xk : ℝ) (w vk : ℝ≥0 → ℝ) (u : ℝ → ℂ) (r : ℝ) : ℂ :=
  mobC xk w vk (invClk (rate xk w vk) r)
      (u (invClk (rate xk w vk) r) + (w (invClk (rate xk w vk) r).toNNReal : ℂ)) -
    (mobPath xk w vk w (invClk (rate xk w vk) r) : ℂ)

/-- **The retargeting family maps the complex Loewner flow to the Loewner flow of `W̃`** (R6, flow identity). If
`u` is a forward solution of `W` from `z ∈ ℍ` on `[0, S]`, and `W̃` is the new driver `M(W) ∘ C⁻¹` on `[0, C(S)]`,
then `ũ = newFlow` is a forward solution of `W̃` from `M_0(z)` on `[0, C(S)]`. -/
theorem isForwardSol_retarget (h : IsSep w vk S) (hxk : 0 < xk)
    (hk : ∀ s ∈ Icc 0 S, vk s.toNNReal = xk + ∫ u in (0 : ℝ)..s, 2 / (vk u.toNNReal - w u.toNNReal))
    {Wn : ℝ → ℝ}
    (hWn : ∀ r ∈ Icc 0 (clk (rate xk w vk) S), Wn r = mobPath xk w vk w (invClk (rate xk w vk) r))
    {z : ℂ} (hz : 0 < z.im) {u : ℝ → ℂ} (hu : IsForwardSol (fun s : ℝ => w s.toNNReal) z S u) :
    IsForwardSol Wn (mobC xk w vk 0 z) (clk (rate xk w vk) S) (newFlow xk w vk u) := by
  have hS := h.nonneg
  have hR := h.isRate hxk
  -- the identity at every `s ∈ [0, S]`
  have hflow : ∀ s ∈ Icc 0 S, mobC xk w vk s (u s + (w s.toNNReal : ℂ)) = mobC xk w vk 0 z +
      ∫ s' in (0 : ℝ)..s, (rate xk w vk s' : ℂ) *
        (2 / (mobC xk w vk s' (u s' + (w s'.toNNReal : ℂ)) - (mobPath xk w vk w s' : ℂ))) := fun s hs =>
    mobC_flow_eq (h.mono hs.1 hs.2) hxk (fun r hr => hk r ⟨hr.1, hr.2.trans hs.2⟩) hz
      (QuantumZipper.isForwardSol_restrict hu hs.1 hs.2)
  -- continuity and nonvanishing in the original clock
  have him := im_pos_of_isForwardSol hS h.cont_w hz hu
  have hcW : ContinuousOn (fun s : ℝ => ((w s.toNNReal : ℝ) : ℂ)) (Icc 0 S) :=
    Complex.continuous_ofReal.comp_continuousOn h.cont_w
  have hcV : ContinuousOn (fun s : ℝ => ((vk s.toNNReal : ℝ) : ℂ)) (Icc 0 S) :=
    Complex.continuous_ofReal.comp_continuousOn h.cont_vk
  have hcg : ContinuousOn (fun s => u s + (w s.toNNReal : ℂ)) (Icc 0 S) := hu.1.add hcW
  have hD : ∀ s ∈ Icc 0 S, ((vk s.toNNReal : ℝ) : ℂ) - (u s + (w s.toNNReal : ℂ)) ≠ 0 := fun s hs he => by
    have := congrArg Complex.im he
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.add_im, Complex.zero_im] at this
    linarith [him s hs]
  have hcF : ContinuousOn (fun s => mobC xk w vk s (u s + (w s.toNNReal : ℂ)) - (mobPath xk w vk w s : ℂ))
      (Icc 0 S) :=
    ((Complex.continuous_ofReal.comp_continuousOn h.continuousOn_beta).add
      ((Complex.continuous_ofReal.comp_continuousOn h.continuousOn_alpha).div (hcV.sub hcg) hD)).sub
      (Complex.continuous_ofReal.comp_continuousOn h.continuousOn_mobPath_w)
  have hne : ∀ s ∈ Icc 0 S, mobC xk w vk s (u s + (w s.toNNReal : ℂ)) - (mobPath xk w vk w s : ℂ) ≠ 0 := by
    intro s hs
    have hq : (gap w vk s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (h.gap_ne hs)
    have hα : (alpha xk w vk s : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (alpha_pos hxk w vk s).ne'
    have e : mobC xk w vk s (u s + (w s.toNNReal : ℂ)) - (mobPath xk w vk w s : ℂ) =
        (alpha xk w vk s : ℂ) * u s /
          ((((vk s.toNNReal : ℝ) : ℂ) - (u s + (w s.toNNReal : ℂ))) * (gap w vk s : ℂ)) := by
      have hDs := hD s hs
      simp only [mobC, mobPath, mob, gap] at hq ⊢
      push_cast at hq ⊢
      field_simp
      ring
    rw [e]
    exact div_ne_zero (mul_ne_zero hα (hu.2 s hs).1) (mul_ne_zero (hD s hs) hq)
  -- the new clock
  have hmem : ∀ r ∈ Icc 0 (clk (rate xk w vk) S), invClk (rate xk w vk) r ∈ Icc 0 S := fun r hr => hR.invClk_mem hr
  refine ⟨hcF.comp hR.continuousOn_invClk hmem, fun r hr => ⟨hne _ (hmem r hr), ?_⟩⟩
  set s₀ := invClk (rate xk w vk) r with hs₀
  have hs₀m := hmem r hr
  have hclk : clk (rate xk w vk) s₀ = r := hR.clk_invClk hr
  have hR0 : IsRate (rate xk w vk) s₀ := hR.mono hs₀m.1 hs₀m.2
  have hint : ∫ s' in (0 : ℝ)..s₀, (rate xk w vk s' : ℂ) *
      (2 / (mobC xk w vk s' (u s' + (w s'.toNNReal : ℂ)) - (mobPath xk w vk w s' : ℂ))) =
      ∫ r' in (0 : ℝ)..r, 2 / newFlow xk w vk u r' := by
    rw [← hclk, hR0.integral_clk_eq_complex]
    refine intervalIntegral.integral_congr fun s' hs' => ?_
    rw [uIcc_of_le hs₀m.1] at hs'
    have hs'S : s' ∈ Icc 0 S := ⟨hs'.1, hs'.2.trans hs₀m.2⟩
    simp only [newFlow]
    rw [hR.invClk_clk hs'S]
  show newFlow xk w vk u r = mobC xk w vk 0 z - (Wn r : ℂ) + ∫ r' in (0 : ℝ)..r, 2 / newFlow xk w vk u r'
  rw [hWn r hr, ← hint]
  simp only [newFlow]
  rw [hflow s₀ hs₀m]
  ring

end Flow

end Retarget

end Zhan

end InteractingSLE
