/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.TargetChangeProcessClock
import InteractingSLE.Spec.Zhan.StripTimeGap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# The retargeting Möbius family along a driving path

Packet PROVE-SEC7-C8 (§7.3, the one-sided step, (C1)–(C2), pp. 378–379; supplement Lemma LP9, p. 485). Let
`(w, v)` be a Loewner driving path with force points, and `V = v_k` a force point (the new target) with
`q = V − w > 0` on `[0, S]`. The family

  `M_t(x) = β_t + α_t/(V_t − x)`,  `α_t = x_k e^{−2∫₀ᵗ q⁻²}`,  `β_t = −1 − 2∫₀ᵗ α q⁻³`

starts at `M_0(x) = x/(x_k − x)` (the map `ψ` of (C1)) and carries the Loewner flow `ẋ = 2/(x − w)` to the Loewner
flow driven by `w̃ = M_t(w_t)` in the clock `ds = α² q⁻⁴ dt` (`rate`): for every force point `v ≠ V`,

  `M_t(v_t) = M_0(v_0) + ∫₀ᵗ rate · 2/(M_s(v_s) − M_s(w_s)) ds`   (`mob_eq_add_integral`),

and the old target, at `β_t = M_t(∞)`, satisfies `β_t = −1 + ∫₀ᵗ rate · 2/(β − M(w))` (`beta_eq_add_integral`). The
coefficients `α' = −2α/q²`, `β' = −2α/q³` and the clock are the unique choice: the coefficients of `1/p`, `1/p²` and
the constant in `p = V − x` all match (checked in the proof of `hasDerivAt_mob_core`).

The force points only have integrable velocities (they may collide with the driver on a Lebesgue-null set), so the
proof is the fundamental theorem of calculus for absolutely continuous functions
(`AbsolutelyContinuousOnInterval.integral_deriv_eq_sub`) with Lebesgue's differentiation theorem.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology
open scoped NNReal

namespace InteractingSLE

namespace Zhan

namespace Retarget

/-! ### The coefficients -/

/-- The target gap `q = V − w` in real time. -/
def gap (w vk : ℝ≥0 → ℝ) (s : ℝ) : ℝ := vk s.toNNReal - w s.toNNReal

/-- `α_t = x_k e^{−2∫₀ᵗ q⁻²}`. -/
def alpha (xk : ℝ) (w vk : ℝ≥0 → ℝ) (t : ℝ) : ℝ :=
  xk * Real.exp (-2 * ∫ s in (0 : ℝ)..t, (gap w vk s ^ 2)⁻¹)

/-- `β_t = −1 − 2∫₀ᵗ α q⁻³`. -/
def beta (xk : ℝ) (w vk : ℝ≥0 → ℝ) (t : ℝ) : ℝ :=
  -1 - 2 * ∫ s in (0 : ℝ)..t, alpha xk w vk s / gap w vk s ^ 3

/-- The clock rate `α² q⁻⁴`. -/
def rate (xk : ℝ) (w vk : ℝ≥0 → ℝ) (s : ℝ) : ℝ := alpha xk w vk s ^ 2 / gap w vk s ^ 4

/-- The retargeting map at time `t`, `M_t(x) = β_t + α_t/(V_t − x)`. -/
def mob (xk : ℝ) (w vk : ℝ≥0 → ℝ) (t x : ℝ) : ℝ := beta xk w vk t + alpha xk w vk t / (vk t.toNNReal - x)

/-- The data on `[0, S]`: the driver and the target are continuous and `q > 0`. -/
structure IsSep (w vk : ℝ≥0 → ℝ) (S : ℝ) : Prop where
  nonneg : 0 ≤ S
  cont_w : ContinuousOn (fun s : ℝ => w s.toNNReal) (Icc 0 S)
  cont_vk : ContinuousOn (fun s : ℝ => vk s.toNNReal) (Icc 0 S)
  pos : ∀ s ∈ Icc 0 S, 0 < gap w vk s

@[simp] theorem alpha_zero (xk : ℝ) (w vk : ℝ≥0 → ℝ) : alpha xk w vk 0 = xk := by simp [alpha]

@[simp] theorem beta_zero (xk : ℝ) (w vk : ℝ≥0 → ℝ) : beta xk w vk 0 = -1 := by simp [beta]

theorem alpha_pos {xk : ℝ} (hxk : 0 < xk) (w vk : ℝ≥0 → ℝ) (t : ℝ) : 0 < alpha xk w vk t :=
  mul_pos hxk (Real.exp_pos _)

theorem rate_pos {xk : ℝ} (hxk : 0 < xk) {w vk : ℝ≥0 → ℝ} {s : ℝ} (hq : 0 < gap w vk s) :
    0 < rate xk w vk s :=
  div_pos (pow_pos (alpha_pos hxk w vk s) 2) (pow_pos hq 4)

/-- The image of the driver is `β + α/q`. -/
theorem mob_w (xk : ℝ) (w vk : ℝ≥0 → ℝ) (t : ℝ) :
    mob xk w vk t (w t.toNNReal) = beta xk w vk t + alpha xk w vk t / gap w vk t := rfl

/-- At time `0`, `M_0(x) = x/(x_k − x)` when `V_0 = x_k`. -/
theorem mob_zero {xk : ℝ} {w vk : ℝ≥0 → ℝ} (h0 : vk 0 = xk) {x : ℝ} (hx : xk - x ≠ 0) :
    mob xk w vk 0 x = x / (xk - x) := by
  simp only [mob, beta_zero, alpha_zero, Real.toNNReal_zero, h0]
  field_simp
  ring

/-! ### Regularity on `[0, S]` -/

namespace IsSep

variable {w vk : ℝ≥0 → ℝ} {S xk : ℝ}

theorem continuousOn_gap (h : IsSep w vk S) : ContinuousOn (gap w vk) (Icc 0 S) :=
  h.cont_vk.sub h.cont_w

theorem gap_ne (h : IsSep w vk S) {s : ℝ} (hs : s ∈ Icc 0 S) : gap w vk s ≠ 0 := (h.pos s hs).ne'

theorem continuousOn_inv_sq (h : IsSep w vk S) : ContinuousOn (fun s => (gap w vk s ^ 2)⁻¹) (Icc 0 S) :=
  (h.continuousOn_gap.pow 2).inv₀ fun _ hs => pow_ne_zero 2 (h.gap_ne hs)

theorem continuousOn_alpha (h : IsSep w vk S) : ContinuousOn (alpha xk w vk) (Icc 0 S) := by
  have hI := intervalIntegral.continuousOn_primitive_interval (μ := volume) (a := 0) (b := S)
    (f := fun s => (gap w vk s ^ 2)⁻¹) (by rw [uIcc_of_le h.nonneg]; exact h.continuousOn_inv_sq.integrableOn_Icc)
  rw [uIcc_of_le h.nonneg] at hI
  exact continuousOn_const.mul ((continuousOn_const.mul hI).rexp)

theorem continuousOn_alpha_div (h : IsSep w vk S) :
    ContinuousOn (fun s => alpha xk w vk s / gap w vk s ^ 3) (Icc 0 S) :=
  h.continuousOn_alpha.div (h.continuousOn_gap.pow 3) fun _ hs => pow_ne_zero 3 (h.gap_ne hs)

theorem continuousOn_rate (h : IsSep w vk S) : ContinuousOn (rate xk w vk) (Icc 0 S) :=
  (h.continuousOn_alpha.pow 2).div (h.continuousOn_gap.pow 4) fun _ hs => pow_ne_zero 4 (h.gap_ne hs)

/-- The clock rate is a rate on `[0, S]` (`x_k > 0`). -/
theorem isRate (h : IsSep w vk S) (hxk : 0 < xk) : IsRate (rate xk w vk) S :=
  ⟨h.nonneg, h.continuousOn_rate, fun s hs => rate_pos hxk (h.pos s hs)⟩

theorem mono (h : IsSep w vk S) {S' : ℝ} (h0 : 0 ≤ S') (hS : S' ≤ S) : IsSep w vk S' :=
  ⟨h0, h.cont_w.mono (Icc_subset_Icc_right hS), h.cont_vk.mono (Icc_subset_Icc_right hS),
    fun s hs => h.pos s ⟨hs.1, hs.2.trans hS⟩⟩

/-- `α' = −2α q⁻²` at interior times. -/
theorem hasDerivAt_alpha (h : IsSep w vk S) {s : ℝ} (hs : s ∈ Ioo 0 S) :
    HasDerivAt (alpha xk w vk) (-2 * alpha xk w vk s * (gap w vk s ^ 2)⁻¹) s := by
  have hc : ContinuousOn (fun s => (gap w vk s ^ 2)⁻¹) (Ioo 0 S) :=
    h.continuousOn_inv_sq.mono Ioo_subset_Icc_self
  have hI : HasDerivAt (fun t => ∫ u in (0 : ℝ)..t, (gap w vk u ^ 2)⁻¹) (gap w vk s ^ 2)⁻¹ s :=
    intervalIntegral.integral_hasDerivAt_right
      ((h.continuousOn_inv_sq.mono (uIcc_subset_Icc ⟨le_rfl, h.nonneg⟩ ⟨hs.1.le, hs.2.le⟩)).intervalIntegrable)
      (hc.stronglyMeasurableAtFilter isOpen_Ioo s hs) (hc.continuousAt (isOpen_Ioo.mem_nhds hs))
  exact (((hI.const_mul (-2)).exp).const_mul xk).congr_deriv (by simp only [alpha]; ring)

/-- `β' = −2α q⁻³` at interior times. -/
theorem hasDerivAt_beta (h : IsSep w vk S) {s : ℝ} (hs : s ∈ Ioo 0 S) :
    HasDerivAt (beta xk w vk) (-2 * (alpha xk w vk s / gap w vk s ^ 3)) s := by
  have hc : ContinuousOn (fun s => alpha xk w vk s / gap w vk s ^ 3) (Ioo 0 S) :=
    h.continuousOn_alpha_div.mono Ioo_subset_Icc_self
  have hI := intervalIntegral.integral_hasDerivAt_right
    ((h.continuousOn_alpha_div (xk := xk)).mono
      (uIcc_subset_Icc ⟨le_rfl, h.nonneg⟩ ⟨hs.1.le, hs.2.le⟩)).intervalIntegrable
    (hc.stronglyMeasurableAtFilter isOpen_Ioo s hs) (hc.continuousAt (isOpen_Ioo.mem_nhds hs))
  exact ((hI.const_mul 2).const_sub (-1)).congr_deriv (by ring)

theorem ac_beta (h : IsSep w vk S) : AbsolutelyContinuousOnInterval (beta xk w vk) 0 S := by
  have hi : IntervalIntegrable (fun s => alpha xk w vk s / gap w vk s ^ 3) volume 0 S :=
    (h.continuousOn_alpha_div.mono (by rw [uIcc_of_le h.nonneg])).intervalIntegrable
  have h1 := (hi.absolutelyContinuousOnInterval_intervalIntegral (c := 0) left_mem_uIcc).const_mul (-2)
  have h2 : AbsolutelyContinuousOnInterval (fun _ : ℝ => (-1 : ℝ)) 0 S :=
    (LipschitzWith.const (-1 : ℝ)).lipschitzOnWith.absolutelyContinuousOnInterval
  refine (h2.add h1).congr fun s _ => ?_
  simp only [beta, Pi.add_apply]
  ring

theorem ac_alpha (h : IsSep w vk S) : AbsolutelyContinuousOnInterval (alpha xk w vk) 0 S := by
  have hi : IntervalIntegrable (fun s => (gap w vk s ^ 2)⁻¹) volume 0 S :=
    (h.continuousOn_inv_sq.mono (by rw [uIcc_of_le h.nonneg])).intervalIntegrable
  have h1 := Zhan.absolutelyContinuousOnInterval_exp_comp
    ((hi.absolutelyContinuousOnInterval_intervalIntegral (c := 0) left_mem_uIcc).const_mul (-2))
  exact h1.const_mul xk

end IsSep

/-! ### Absolutely continuous paths -/

/-- A constant is absolutely continuous. -/
theorem ac_const (c a b : ℝ) : AbsolutelyContinuousOnInterval (fun _ : ℝ => c) a b :=
  (LipschitzWith.const c).lipschitzOnWith.absolutelyContinuousOnInterval

/-- A path `x + ∫₀ˢ f` (on `[0, S]`, `f` integrable) is absolutely continuous. -/
theorem ac_of_eq_add_integral {g f : ℝ → ℝ} {x S : ℝ} (hS : 0 ≤ S) (hf : IntervalIntegrable f volume 0 S)
    (hg : ∀ s ∈ Icc 0 S, g s = x + ∫ u in (0 : ℝ)..s, f u) : AbsolutelyContinuousOnInterval g 0 S :=
  ((ac_const x 0 S).add (hf.absolutelyContinuousOnInterval_intervalIntegral (c := 0) left_mem_uIcc)).congr
    fun s hs => (hg s (by rwa [uIcc_of_le hS] at hs)).symm

/-- The inverse of an absolutely continuous function bounded away from `0` is absolutely continuous. -/
theorem ac_inv {g : ℝ → ℝ} {a b c : ℝ} (hg : AbsolutelyContinuousOnInterval g a b) (hc : 0 < c)
    (hgc : ∀ s ∈ uIcc a b, c ≤ |g s|) : AbsolutelyContinuousOnInterval (fun s => (g s)⁻¹) a b := by
  have hL : LipschitzOnWith (Real.toNNReal (c ^ 2)⁻¹) (fun x : ℝ => x⁻¹) {x | c ≤ |x|} := by
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    have hx0 : 0 < |x| := hc.trans_le hx
    have hy0 : 0 < |y| := hc.trans_le hy
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by positivity), inv_sub_inv (abs_pos.1 hx0)
      (abs_pos.1 hy0), abs_div, abs_mul, abs_sub_comm y x]
    rw [div_le_iff₀ (mul_pos hx0 hy0)]
    have : c ^ 2 ≤ |x| * |y| := by rw [sq]; exact mul_le_mul hx hy hc.le (abs_nonneg _)
    calc |x - y| = (c ^ 2)⁻¹ * |x - y| * c ^ 2 := by field_simp
      _ ≤ (c ^ 2)⁻¹ * |x - y| * (|x| * |y|) := by gcongr
  exact hL.comp_absolutelyContinuousOnInterval (g := g) (fun s hs => hgc s hs) hg

/-- **FTC with an almost-everywhere derivative**: an absolutely continuous `F` on `[0, S]` with `F' = g` almost
everywhere is `F 0 + ∫₀ˢ g`. -/
theorem eq_add_integral_of_ae_hasDerivAt {F g : ℝ → ℝ} {S : ℝ} (hS0 : 0 ≤ S)
    (hF : AbsolutelyContinuousOnInterval F 0 S) (hd : ∀ᵐ s, s ∈ Ioo 0 S → HasDerivAt F (g s) s) :
    F S = F 0 + ∫ s in (0 : ℝ)..S, g s := by
  have h := hF.integral_deriv_eq_sub
  have he : ∫ s in (0 : ℝ)..S, deriv F s = ∫ s in (0 : ℝ)..S, g s := by
    refine intervalIntegral.integral_congr_ae ?_
    have hS : ∀ᵐ s : ℝ, s ≠ S := by simp [ae_iff, measure_singleton]
    filter_upwards [hd, hS] with s hs hsS hsI
    rw [uIoc_of_le hS0] at hsI
    exact (hs ⟨hsI.1, lt_of_le_of_ne hsI.2 hsS⟩).deriv
  linarith

/-! ### The core identity: the derivative of `M_t(v_t)` -/

/-- The algebra of the target change: with `q = V − w`, `D = V − v`, `a = v − w = q − D`, the derivative
`β' + α' D⁻¹ − α D'/D²` (`β' = −2α/q³`, `α' = −2α/q²`, `D' = 2/q − 2/a`) is the new clock rate `α²/q⁴` times the
new Loewner velocity `2/(M(v) − M(w)) = 2/(α/D − α/q)`. -/
theorem mob_deriv_alg {α q D : ℝ} (hα : α ≠ 0) (hq : q ≠ 0) (hD : D ≠ 0) (ha : q - D ≠ 0) :
    -2 * (α / q ^ 3) + -2 * α * (q ^ 2)⁻¹ * D⁻¹ + α * (-(D ^ 2)⁻¹ * (2 / q - 2 / (q - D))) =
      α ^ 2 / q ^ 4 * (2 / (α / D - α / q)) := by
  have h1 : α / D - α / q = α * (q - D) / (D * q) := by field_simp
  rw [h1]
  field_simp
  ring

/-! ### The retargeted Loewner equations in the original time -/

section Marks

variable {w vk v : ℝ≥0 → ℝ} {S xk x : ℝ}

/-- A function continuous and nonvanishing on `[0, S]` is bounded away from `0` there. -/
theorem exists_pos_le_abs {D : ℝ → ℝ} (hS : 0 ≤ S) (hc : ContinuousOn D (Icc 0 S))
    (hD : ∀ s ∈ Icc 0 S, D s ≠ 0) : ∃ c > 0, ∀ s ∈ Icc 0 S, c ≤ |D s| := by
  obtain ⟨s₀, hs₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hS) hc.abs
  exact ⟨|D s₀|, abs_pos.2 (hD s₀ hs₀), fun s hs => hmin hs⟩

/-- A path with an integral representation on `[0, S]` is differentiable at interior Lebesgue points. -/
theorem hasDerivAt_of_eq_add_integral {g f : ℝ → ℝ} (hg : ∀ s ∈ Icc 0 S, g s = x + ∫ u in (0 : ℝ)..s, f u)
    {s : ℝ} (hs : s ∈ Ioo 0 S) (hd : HasDerivAt (fun t => ∫ u in (0 : ℝ)..t, f u) (f s) s) :
    HasDerivAt g (f s) s := by
  refine (hd.const_add x).congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioo.mem_nhds hs] with t ht using hg t (Ioo_subset_Icc_self ht)

/-- **The retargeted mark equation** (Specification §7.3, (C1)–(C2); Lemma LP9): for a force point `v ≠ V` with
`v = x + ∫ 2/(v − w)` on `[0, S]`, `M_S(v_S) = M_0(x) + ∫₀ˢ rate · 2/(M(v) − M(w))`: the image of the Loewner flow
is the Loewner flow driven by `M(w)` in the clock `rate`. -/
theorem mob_eq_add_integral (h : IsSep w vk S) (hxk : 0 < xk)
    (hk : ∀ s ∈ Icc 0 S, vk s.toNNReal = xk + ∫ u in (0 : ℝ)..s, 2 / (vk u.toNNReal - w u.toNNReal))
    (hv : ∀ s ∈ Icc 0 S, v s.toNNReal = x + ∫ u in (0 : ℝ)..s, 2 / (v u.toNNReal - w u.toNNReal))
    (hvi : IntervalIntegrable (fun u => 2 / (v u.toNNReal - w u.toNNReal)) volume 0 S)
    (hcol : ∀ᵐ s, s ∈ Icc 0 S → v s.toNNReal ≠ w s.toNNReal)
    (hD : ∀ s ∈ Icc 0 S, v s.toNNReal ≠ vk s.toNNReal) :
    mob xk w vk S (v S.toNNReal) = mob xk w vk 0 x +
      ∫ s in (0 : ℝ)..S, rate xk w vk s *
        (2 / (mob xk w vk s (v s.toNNReal) - mob xk w vk s (w s.toNNReal))) := by
  have hS := h.nonneg
  have hv0 : v 0 = x := by simpa using hv 0 ⟨le_rfl, hS⟩
  have hki : IntervalIntegrable (fun u => 2 / (vk u.toNNReal - w u.toNNReal)) volume 0 S := by
    refine (ContinuousOn.intervalIntegrable ?_)
    rw [uIcc_of_le hS]
    exact continuousOn_const.div h.continuousOn_gap fun _ hs => h.gap_ne hs
  set D : ℝ → ℝ := fun s => vk s.toNNReal - v s.toNNReal with hDdef
  have hacD : AbsolutelyContinuousOnInterval D 0 S :=
    (ac_of_eq_add_integral hS hki hk).sub (ac_of_eq_add_integral hS hvi hv)
  obtain ⟨c, hc, hcD⟩ := exists_pos_le_abs hS (hacD.continuousOn.mono (by rw [uIcc_of_le hS]))
    fun s hs => sub_ne_zero.2 (hD s hs).symm
  have hacF : AbsolutelyContinuousOnInterval (fun s => beta xk w vk s + alpha xk w vk s * (D s)⁻¹) 0 S :=
    h.ac_beta.add (h.ac_alpha.fun_mul (ac_inv hacD hc fun s hs => hcD s (by rwa [uIcc_of_le hS] at hs)))
  have hF := eq_add_integral_of_ae_hasDerivAt (g := fun s => rate xk w vk s *
      (2 / (mob xk w vk s (v s.toNNReal) - mob xk w vk s (w s.toNNReal)))) hS hacF ?_
  · simp only [hDdef] at hF
    simp only [mob, div_eq_mul_inv, Real.toNNReal_zero] at hF ⊢
    rw [hF, hv0]
  · filter_upwards [hvi.ae_hasDerivAt_integral, hki.ae_hasDerivAt_integral, hcol] with s h1 h2 h3 hs
    have hsI : s ∈ Icc 0 S := Ioo_subset_Icc_self hs
    have hsU : s ∈ uIcc 0 S := by rwa [uIcc_of_le hS]
    have hvd := hasDerivAt_of_eq_add_integral hv hs (h1 hsU 0 left_mem_uIcc)
    have hkd := hasDerivAt_of_eq_add_integral hk hs (h2 hsU 0 left_mem_uIcc)
    have hDs : D s ≠ 0 := sub_ne_zero.2 (hD s hsI).symm
    have hDd := (hkd.sub hvd).inv hDs
    have hFd := (h.hasDerivAt_beta (xk := xk) hs).add ((h.hasDerivAt_alpha (xk := xk) hs).mul hDd)
    refine hFd.congr_deriv ?_
    have hq : gap w vk s ≠ 0 := h.gap_ne hsI
    have hα : alpha xk w vk s ≠ 0 := (alpha_pos hxk w vk s).ne'
    have ha : gap w vk s - D s ≠ 0 := by
      simp only [gap, hDdef]
      rw [show vk s.toNNReal - w s.toNNReal - (vk s.toNNReal - v s.toNNReal) = v s.toNNReal - w s.toNNReal
        by ring]
      exact sub_ne_zero.2 (h3 hsI)
    have e1 : (2 : ℝ) / (vk s.toNNReal - w s.toNNReal) = 2 / gap w vk s := rfl
    have e2 : (2 : ℝ) / (v s.toNNReal - w s.toNNReal) = 2 / (gap w vk s - D s) := by
      congr 1; simp only [gap, hDdef]; ring
    have e3 : mob xk w vk s (v s.toNNReal) - mob xk w vk s (w s.toNNReal) =
        alpha xk w vk s / D s - alpha xk w vk s / gap w vk s := by
      simp only [mob, gap, hDdef]; ring
    have key := mob_deriv_alg hα hq hDs ha
    have eD : vk s.toNNReal - v s.toNNReal = D s := rfl
    simp only [Pi.sub_apply, Pi.inv_apply, eD, e1, e2, e3, rate]
    rw [← key]
    ring

/-- **The old target** `β_t = M_t(∞)` follows the new Loewner flow: `β_S = −1 + ∫₀ˢ rate · 2/(β − M(w))`. -/
theorem beta_eq_add_integral (h : IsSep w vk S) (hxk : 0 < xk) :
    beta xk w vk S = -1 + ∫ s in (0 : ℝ)..S, rate xk w vk s *
      (2 / (beta xk w vk s - mob xk w vk s (w s.toNNReal))) := by
  have e : ∀ s ∈ uIcc 0 S, rate xk w vk s * (2 / (beta xk w vk s - mob xk w vk s (w s.toNNReal))) =
      -2 * (alpha xk w vk s / gap w vk s ^ 3) := by
    intro s hs
    rw [uIcc_of_le h.nonneg] at hs
    have hq := h.gap_ne hs
    have hα := (alpha_pos hxk w vk s).ne'
    rw [mob_w, rate, show beta xk w vk s - (beta xk w vk s + alpha xk w vk s / gap w vk s) =
      -(alpha xk w vk s / gap w vk s) by ring]
    field_simp
  rw [intervalIntegral.integral_congr e, intervalIntegral.integral_const_mul, beta]
  ring

end Marks

end Retarget

end Zhan

end InteractingSLE
