/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.SeedClock
import InteractingSLE.Foundations.Loewner.RealPoints

/-!
# Lemma G11, deterministic part: complex points near the separated mark are not swallowed

Packet PROVE-G11-G4. Specification supplement §7.9, Lemma G11 (p. 503, `source/spec/p481-528.md` L538–L572). For the
two-mark word (seed group `r` at `0⁺`, mark `ρ` at `1`) write `w` for the driver, `v₀` for the seed force point,
`v₁` for the mark, and

  `u₁ = v₁ − w` (the gap to the mark), `o = v₀ − w ≥ 0` (the seed gap), `e = v₁ − v₀` (the span).

Before the mark is swallowed (`u₁ > 0` on `[0, T]`) this file proves, for every continuous driver:

* `IsSeedMarkPath.span_eq_exp`: `e(t) = exp(−∫₀ᵗ 2/(u₁ o))`, across the (Lebesgue-null) seed collisions, by the
  fundamental theorem of calculus for absolutely continuous functions;
* `IsSeedMarkPath.not_mem_fwdHull`: if `∫₀ᵀ β ≤ C` for the **budget** `β = 4e/(u₁² o) + 4e/u₁³` and `z ∈ ℍ` satisfies
  `‖z − 1‖ e^{C/2} < 1/2`, then `z ∉ K_T`.

The second statement replaces the Koebe estimate `dist(1, K_t) ≥ c (V¹ − V⁰)/g_t'(1)` of the source's strip argument
by a direct comparison of forward flows: the difference `D = f_t(z) − u₁` solves `D' = −2D/(f_t(z) u₁)`, and the span
solves `e' = −2e/(u₁ o)`; as long as `‖D‖ ≤ e/2`,

  `d/dt log(‖D‖/e) = 2/(u₁ o) − 2 Re(1/f_t(z))/u₁ ≤ β/2`,

so the budget keeps `f_t(z)` in the disk `B(u₁, e/2)`, at distance `≥ u₁/2` from `0`, and the forward clock of `z` stays
bounded. Since `∫₀ᵀ (4/(u₁ o) − 4/u₁²) = 4 ∫₀ᵀ e/(u₁² o)` and `−log g_T'(1) = ∫₀ᵀ 2/u₁²`, the budget is the source's
`−log((V¹ − V⁰)/g_T'(1))` (twice) plus a term that is finite once the strip gap escapes linearly.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Complex
open scoped NNReal ENNReal

namespace InteractingSLE

namespace Supp7

namespace G11

/-- The pathwise data of the two-mark word (seed group at `0⁺`, mark at `1`) on `[0, T]`, before the mark is swallowed:
a continuous driver `w` with `w 0 = 0`, the integrated force-point equations for the seed `v₀` and the mark `v₁`, the
order `w ≤ v₀ ≤ v₁`, `w < v₁`, an integrable reciprocal seed gap and Lebesgue-null seed collisions. -/
structure IsSeedMarkPath (w v0 v1 : ℝ → ℝ) (T : ℝ) : Prop where
  nonneg : 0 ≤ T
  cont_w : Continuous w
  w_zero : w 0 = 0
  cont_v0 : ContinuousOn v0 (Icc 0 T)
  cont_v1 : ContinuousOn v1 (Icc 0 T)
  w_le_v0 : ∀ t ∈ Icc 0 T, w t ≤ v0 t
  v0_le_v1 : ∀ t ∈ Icc 0 T, v0 t ≤ v1 t
  w_lt_v1 : ∀ t ∈ Icc 0 T, w t < v1 t
  v0_eq : ∀ t ∈ Icc 0 T, v0 t = 0 + ∫ s in (0 : ℝ)..t, 2 / (v0 s - w s)
  v1_eq : ∀ t ∈ Icc 0 T, v1 t = 1 + ∫ s in (0 : ℝ)..t, 2 / (v1 s - w s)
  int_v0 : IntervalIntegrable (fun s => (v0 s - w s)⁻¹) volume 0 T
  ae_ne : ∀ᵐ s, s ∈ Icc 0 T → v0 s ≠ w s

/-- The rate `2/(u₁ o)` of the logarithmic span. -/
def spanRate (w v0 v1 : ℝ → ℝ) (s : ℝ) : ℝ := 2 / ((v1 s - w s) * (v0 s - w s))

/-- The **budget** `β = 4e/(u₁² o) + 4e/u₁³`. -/
def budget (w v0 v1 : ℝ → ℝ) (s : ℝ) : ℝ :=
  4 * (v1 s - v0 s) / ((v1 s - w s) ^ 2 * (v0 s - w s)) + 4 * (v1 s - v0 s) / (v1 s - w s) ^ 3

/-! ### Two real-analysis helpers -/

/-- A function continuous on `[0, t]` agrees there with a function continuous on `ℝ`. -/
theorem exists_continuous_eqOn_Icc {E : Type*} [TopologicalSpace E] {φ : ℝ → E} {t : ℝ} (ht : 0 ≤ t)
    (hφ : ContinuousOn φ (Icc 0 t)) : ∃ φ' : ℝ → E, Continuous φ' ∧ EqOn φ' φ (Icc 0 t) := by
  refine ⟨fun s => φ (projIcc 0 t ht s),
    hφ.comp_continuous (continuous_subtype_val.comp continuous_projIcc) (fun s => Subtype.mem _),
    fun s hs => ?_⟩
  simp only [projIcc_of_mem ht hs]

/-- Interval integrals over `[0, r] ⊆ [0, t]` only see the integrand on `[0, t]`. -/
theorem integral_congr_Icc {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {φ φ' : ℝ → E} {t : ℝ}
    (h : EqOn φ' φ (Icc 0 t)) {r : ℝ} (hr : r ∈ Icc 0 t) :
    ∫ s in (0 : ℝ)..r, φ' s = ∫ s in (0 : ℝ)..r, φ s := by
  refine intervalIntegral.integral_congr fun s hs => h ?_
  rw [uIcc_of_le hr.1] at hs
  exact ⟨hs.1, hs.2.trans hr.2⟩

/-- **A linear equation with continuous coefficient**: if `f = f 0 + ∫₀ʳ (−g f)` on `[0, t]` with `f`, `g`
continuous there, then `f r = f 0 · exp(−∫₀ʳ g)`. -/
theorem eq_mul_cexp_of_eq_integral {f g : ℝ → ℂ} {t : ℝ} (ht : 0 ≤ t) (hf : ContinuousOn f (Icc 0 t))
    (hg : ContinuousOn g (Icc 0 t))
    (heq : ∀ r ∈ Icc 0 t, f r = f 0 + ∫ s in (0 : ℝ)..r, -(g s * f s)) :
    ∀ r ∈ Icc 0 t, f r = f 0 * cexp (-∫ s in (0 : ℝ)..r, g s) := by
  obtain ⟨g', hg'c, hg'⟩ := exists_continuous_eqOn_Icc ht hg
  obtain ⟨k', hk'c, hk'⟩ := exists_continuous_eqOn_Icc ht (hg.mul hf).neg
  set F : ℝ → ℂ := fun r => (f 0 + ∫ s in (0 : ℝ)..r, k' s) * cexp (∫ s in (0 : ℝ)..r, g' s) with hF
  have hderiv : ∀ x, HasDerivAt F (k' x * cexp (∫ s in (0 : ℝ)..x, g' s) +
      (f 0 + ∫ s in (0 : ℝ)..x, k' s) * (cexp (∫ s in (0 : ℝ)..x, g' s) * g' x)) x := fun x =>
    ((hk'c.integral_hasStrictDerivAt 0 x).hasDerivAt.const_add (f 0)).mul
      ((hg'c.integral_hasStrictDerivAt 0 x).hasDerivAt.cexp)
  have hval : ∀ x ∈ Icc 0 t, f 0 + ∫ s in (0 : ℝ)..x, k' s = f x := fun x hx => by
    rw [integral_congr_Icc hk' hx, heq x hx]
    rfl
  have hconst := constant_of_has_deriv_right_zero (f := F) (a := 0) (b := t)
    (fun x _ => (hderiv x).continuousAt.continuousWithinAt) fun x hx => by
      have hx' : x ∈ Icc 0 t := Ico_subset_Icc_self hx
      refine ((hderiv x).congr_deriv ?_).hasDerivWithinAt
      rw [hk' hx', hg' hx', hval x hx']
      simp only [Pi.neg_apply, Pi.mul_apply]
      ring
  intro r hr
  have h1 := hconst r hr
  have hF0 : F 0 = f 0 := by simp [hF]
  rw [hF0] at h1
  simp only [hF, hval r hr, integral_congr_Icc hg' hr] at h1
  rw [Complex.exp_neg, ← h1, mul_assoc, mul_inv_cancel₀ (Complex.exp_ne_zero _), mul_one]

/-- `Re (1/(c + D)) ≥ 1/c − 2‖D‖/c²` for `c > 0`, `‖D‖ ≤ c/2`. -/
theorem re_inv_add_ge {c : ℝ} (hc : 0 < c) {D : ℂ} (hD : ‖D‖ ≤ c / 2) :
    1 / c - 2 * ‖D‖ / c ^ 2 ≤ ((c : ℂ) + D)⁻¹.re := by
  have hcD : c / 2 ≤ ‖(c : ℂ) + D‖ := by
    have h1 : ‖(c : ℂ)‖ ≤ ‖(c : ℂ) + D‖ + ‖D‖ := by
      have := norm_sub_le ((c : ℂ) + D) D
      simpa using this
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc] at h1
    linarith
  have hne : (c : ℂ) + D ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hcD; linarith
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hdiff : ((c : ℂ) + D)⁻¹ - (c : ℂ)⁻¹ = -D / ((c : ℂ) * ((c : ℂ) + D)) := by
    field_simp
    ring
  have hnorm : ‖((c : ℂ) + D)⁻¹ - (c : ℂ)⁻¹‖ ≤ 2 * ‖D‖ / c ^ 2 := by
    rw [hdiff, norm_div, norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_le_mul_of_nonneg_left hcD (by positivity : (0 : ℝ) ≤ 2 * ‖D‖ * c)
    nlinarith [norm_nonneg D]
  have hre := Complex.abs_re_le_norm (((c : ℂ) + D)⁻¹ - (c : ℂ)⁻¹)
  rw [Complex.sub_re, ← Complex.ofReal_inv, Complex.ofReal_re] at hre
  have := neg_abs_le ((((c : ℂ) + D)⁻¹).re - c⁻¹)
  rw [← Complex.ofReal_inv] at hnorm
  rw [one_div]
  linarith

variable {w v0 v1 : ℝ → ℝ} {T : ℝ}

namespace IsSeedMarkPath

variable (h : IsSeedMarkPath w v0 v1 T)
include h

theorem continuousOn_gap : ContinuousOn (fun s => v1 s - w s) (Icc 0 T) :=
  h.cont_v1.sub h.cont_w.continuousOn

/-- The gap to the mark is bounded below on `[0, T]`. -/
theorem exists_pos_le_gap : ∃ δ > 0, ∀ t ∈ Icc 0 T, δ ≤ v1 t - w t := by
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 h.nonneg) h.continuousOn_gap
  exact ⟨v1 t₀ - w t₀, sub_pos.2 (h.w_lt_v1 t₀ ht₀), fun t ht => hmin ht⟩

theorem intervalIntegrable_inv_gap : IntervalIntegrable (fun s => (v1 s - w s)⁻¹) volume 0 T := by
  refine (h.continuousOn_gap.inv₀ fun t ht => ?_).intervalIntegrable_of_Icc h.nonneg
  exact (sub_pos.2 (h.w_lt_v1 t ht)).ne'

/-- `2/(u₁ o)` is integrable on `[0, T]`: a bounded continuous factor times the integrable `1/o`. -/
theorem intervalIntegrable_spanRate : IntervalIntegrable (spanRate w v0 v1) volume 0 T := by
  have hc : ContinuousOn (fun s => 2 * (v1 s - w s)⁻¹) (Icc 0 T) :=
    continuousOn_const.mul (h.continuousOn_gap.inv₀ fun t ht => (sub_pos.2 (h.w_lt_v1 t ht)).ne')
  have hc' : ContinuousOn (fun s => 2 * (v1 s - w s)⁻¹) (uIcc 0 T) := by
    rwa [uIcc_of_le h.nonneg]
  have := h.int_v0.continuousOn_mul hc'
  refine this.congr fun s _ => ?_
  simp only [spanRate]
  rw [div_eq_mul_inv, mul_inv, mul_assoc]

/-- The span solves `e(t) = 1 + ∫₀ᵗ (2/u₁ − 2/o)`. -/
theorem span_eq_add_integral (t : ℝ) (ht : t ∈ Icc 0 T) :
    v1 t - v0 t = 1 + ∫ s in (0 : ℝ)..t, (2 / (v1 s - w s) - 2 / (v0 s - w s)) := by
  have h1 : IntervalIntegrable (fun s => 2 / (v1 s - w s)) volume 0 t := by
    have := (h.intervalIntegrable_inv_gap.const_mul 2).mono_set
      (uIcc_subset_uIcc_left (by rw [uIcc_of_le h.nonneg]; exact ht))
    simpa [div_eq_mul_inv] using this
  have h0 : IntervalIntegrable (fun s => 2 / (v0 s - w s)) volume 0 t := by
    have := (h.int_v0.const_mul 2).mono_set
      (uIcc_subset_uIcc_left (by rw [uIcc_of_le h.nonneg]; exact ht))
    simpa [div_eq_mul_inv] using this
  rw [h.v1_eq t ht, h.v0_eq t ht, intervalIntegral.integral_sub h1 h0]
  ring

theorem intervalIntegrable_spanDrift :
    IntervalIntegrable (fun s => 2 / (v1 s - w s) - 2 / (v0 s - w s)) volume 0 T := by
  have h1 := h.intervalIntegrable_inv_gap.const_mul 2
  have h0 := h.int_v0.const_mul 2
  simpa [div_eq_mul_inv] using h1.sub h0

/-- **The span is `e(t) = exp(−∫₀ᵗ 2/(u₁ o))`** on `[0, T]`. -/
theorem span_eq_exp (t : ℝ) (ht : t ∈ Icc 0 T) :
    v1 t - v0 t = Real.exp (-∫ s in (0 : ℝ)..t, spanRate w v0 v1 s) := by
  set a : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, spanRate w v0 v1 s with ha
  have hT := h.nonneg
  have hacE : AbsolutelyContinuousOnInterval (fun t => v1 t - v0 t) 0 T :=
    WangWu.Span.absolutelyContinuousOnInterval_of_eq_add_integral hT h.intervalIntegrable_spanDrift
      h.span_eq_add_integral
  have hacA : AbsolutelyContinuousOnInterval a 0 T :=
    WangWu.Span.absolutelyContinuousOnInterval_of_eq_add_integral (g := a) (c := 0) hT
      h.intervalIntegrable_spanRate
      (fun t _ => by simp [ha])
  -- `a` is bounded on `[0, T]`, so `exp ∘ a` is absolutely continuous
  obtain ⟨M, hM⟩ : ∃ M, ∀ x ∈ uIcc 0 T, a x ∈ Iic M := by
    obtain ⟨M, hM⟩ := (isCompact_uIcc.image_of_continuousOn hacA.continuousOn).isBounded.bddAbove
    exact ⟨M, fun x hx => hM (mem_image_of_mem a hx)⟩
  have hexpL : LipschitzOnWith (Real.toNNReal (Real.exp M)) Real.exp (Iic M) := by
    refine (convex_Iic M).lipschitzOnWith_of_nnnorm_hasDerivWithin_le (f' := Real.exp)
      (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) fun x hx => ?_
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (Real.exp_pos M).le, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos x)]
    exact Real.exp_le_exp.2 hx
  have hacExp : AbsolutelyContinuousOnInterval (Real.exp ∘ a) 0 T :=
    hexpL.comp_absolutelyContinuousOnInterval hM hacA
  have hacY : AbsolutelyContinuousOnInterval (fun t => (v1 t - v0 t) * Real.exp (a t)) 0 T :=
    hacE.mul hacExp
  -- its derivative vanishes almost everywhere
  have hd0 : ∀ᵐ x, x ∈ uIcc 0 T → HasDerivAt (fun t => (v1 t - v0 t) * Real.exp (a t)) 0 x := by
    have hE := WangWu.Span.ae_hasDerivAt_of_eq_add_integral hT h.intervalIntegrable_spanDrift h.span_eq_add_integral
    have hA := WangWu.Span.ae_hasDerivAt_of_eq_add_integral (g := a) (c := 0) hT h.intervalIntegrable_spanRate
      (fun t _ => by simp [ha])
    have h0 : ∀ᵐ x : ℝ, x ≠ 0 := by simp [ae_iff, measure_singleton]
    have hT' : ∀ᵐ x : ℝ, x ≠ T := by simp [ae_iff, measure_singleton]
    filter_upwards [hE, hA, h.ae_ne, h0, hT'] with x hEx hAx hne hx0 hxT hx
    rw [uIcc_of_le hT] at hx
    have hxI : x ∈ Ioo 0 T := ⟨lt_of_le_of_ne hx.1 (Ne.symm hx0), lt_of_le_of_ne hx.2 hxT⟩
    have hu : v1 x - w x ≠ 0 := (sub_pos.2 (h.w_lt_v1 x hx)).ne'
    have ho : v0 x - w x ≠ 0 := sub_ne_zero.2 (hne hx)
    have key : 2 / (v1 x - w x) - 2 / (v0 x - w x) +
        (v1 x - v0 x) * (2 / ((v1 x - w x) * (v0 x - w x))) = 0 := by
      field_simp
      ring
    refine ((hEx hxI).mul ((hAx hxI).exp)).congr_deriv ?_
    simp only [spanRate]
    linear_combination (Real.exp (a x)) * key
  obtain ⟨C, hC⟩ := hacY.const_of_ae_hasDerivAt_zero hd0
  have h0mem : (0 : ℝ) ∈ uIcc 0 T := by simp [hT]
  have htmem : t ∈ uIcc 0 T := by rw [uIcc_of_le hT]; exact ht
  have hY0 : (v1 0 - v0 0) * Real.exp (a 0) = 1 := by
    have h1 := h.v1_eq 0 ⟨le_rfl, hT⟩
    have h2 := h.v0_eq 0 ⟨le_rfl, hT⟩
    simp only [intervalIntegral.integral_same, add_zero] at h1 h2
    simp [ha, h1, h2]
  have hYt := hC t htmem
  rw [← hC 0 h0mem, hY0] at hYt
  rw [Real.exp_neg]
  exact eq_inv_of_mul_eq_one_left hYt

theorem gap_pos (t : ℝ) (ht : t ∈ Icc 0 T) : 0 < v1 t - w t := sub_pos.2 (h.w_lt_v1 t ht)

theorem span_pos (t : ℝ) (ht : t ∈ Icc 0 T) : 0 < v1 t - v0 t := by
  rw [h.span_eq_exp t ht]; exact Real.exp_pos _

theorem span_le_gap (t : ℝ) (ht : t ∈ Icc 0 T) : v1 t - v0 t ≤ v1 t - w t := by
  linarith [h.w_le_v0 t ht]

/-- The real solution from `1` is the gap to the mark. -/
theorem gapC_eq (t : ℝ) (ht : t ∈ Icc 0 T) :
    (((v1 t - w t : ℝ)) : ℂ) = 1 - w t + ∫ s in (0 : ℝ)..t, 2 / (((v1 s - w s : ℝ)) : ℂ) := by
  have h1 := h.v1_eq t ht
  have hI : (∫ s in (0 : ℝ)..t, 2 / (((v1 s - w s : ℝ)) : ℂ)) =
      ((∫ s in (0 : ℝ)..t, 2 / (v1 s - w s) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    refine intervalIntegral.integral_congr fun s _ => ?_
    push_cast
    rfl
  rw [hI]
  push_cast
  rw [h1]
  push_cast
  ring

theorem continuousOn_gapC : ContinuousOn (fun s => (((v1 s - w s : ℝ)) : ℂ)) (Icc 0 T) :=
  Complex.continuous_ofReal.comp_continuousOn h.continuousOn_gap

/-- **The difference of forward flows** `D = f_r(z) − u₁(r)` solves `D' = −2D/(f_r(z) u₁)`. -/
theorem sub_gapC_eq {z : ℂ} {t : ℝ} (ht : t ∈ Icc 0 T) {v : ℝ → ℂ}
    (hv : QuantumZipper.IsForwardSol w z t v) :
    ∀ r ∈ Icc 0 t, v r - ((v1 r - w r : ℝ) : ℂ) =
      (z - 1) * cexp (-∫ s in (0 : ℝ)..r, 2 / (v s * ((v1 s - w s : ℝ) : ℂ))) := by
  have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
  have hgc : ContinuousOn (fun s => (((v1 s - w s : ℝ)) : ℂ)) (Icc 0 t) := h.continuousOn_gapC.mono hsub
  have hg0 : ∀ s ∈ Icc 0 t, (((v1 s - w s : ℝ)) : ℂ) ≠ 0 := fun s hs => by
    exact_mod_cast (h.gap_pos s (hsub hs)).ne'
  have hv0 : ∀ s ∈ Icc 0 t, v s ≠ 0 := fun s hs => (hv.2 s hs).1
  have hD := eq_mul_cexp_of_eq_integral (f := fun s => v s - ((v1 s - w s : ℝ) : ℂ))
    (g := fun s => 2 / (v s * ((v1 s - w s : ℝ) : ℂ))) ht.1 (hv.1.sub hgc)
    ((continuousOn_const.div (hv.1.mul hgc) fun s hs => mul_ne_zero (hv0 s hs) (hg0 s hs))) ?_
  · intro r hr
    have h0 := hD r hr
    have hv00 : v 0 = z := by
      have := (hv.2 0 ⟨le_rfl, ht.1⟩).2
      rw [intervalIntegral.integral_same, h.w_zero] at this
      simpa using this
    have hg00 : (((v1 0 - w 0 : ℝ)) : ℂ) = 1 := by
      have := h.v1_eq 0 ⟨le_rfl, h.nonneg⟩
      rw [intervalIntegral.integral_same] at this
      rw [this, h.w_zero]; norm_num
    simpa only [hv00, hg00] using h0
  · intro r hr
    have hr' : r ∈ Icc 0 T := hsub hr
    have hrr : Icc 0 r ⊆ Icc 0 t := Icc_subset_Icc_right hr.2
    have hi1 : IntervalIntegrable (fun s => 2 / v s) volume 0 r := by
      refine ContinuousOn.intervalIntegrable_of_Icc hr.1 ?_
      exact continuousOn_const.div (hv.1.mono hrr) fun s hs => hv0 s (hrr hs)
    have hi2 : IntervalIntegrable (fun s => 2 / (((v1 s - w s : ℝ)) : ℂ)) volume 0 r := by
      refine ContinuousOn.intervalIntegrable_of_Icc hr.1 ?_
      exact continuousOn_const.div (hgc.mono hrr) fun s hs => hg0 s (hrr hs)
    have hcongr : (∫ s in (0 : ℝ)..r, -(2 / (v s * ((v1 s - w s : ℝ) : ℂ)) *
        (v s - ((v1 s - w s : ℝ) : ℂ)))) =
        ∫ s in (0 : ℝ)..r, (2 / v s - 2 / (((v1 s - w s : ℝ)) : ℂ)) := by
      refine intervalIntegral.integral_congr fun s hs => ?_
      rw [uIcc_of_le hr.1] at hs
      have h1 := hv0 s (hrr hs)
      have h2 := hg0 s (hrr hs)
      field_simp
      ring
    have hvr := (hv.2 r hr).2
    have hv00 : v 0 = z := by
      have := (hv.2 0 ⟨le_rfl, ht.1⟩).2
      simpa [intervalIntegral.integral_same, h.w_zero] using this
    have hg00 : (((v1 0 - w 0 : ℝ)) : ℂ) = 1 := by
      have := h.v1_eq 0 ⟨le_rfl, h.nonneg⟩
      rw [intervalIntegral.integral_same, add_zero] at this
      rw [this, h.w_zero]; norm_num
    have hgr := h.gapC_eq r hr'
    rw [hcongr, intervalIntegral.integral_sub hi1 hi2, hvr, hgr, hv00, hg00]
    ring

/-- The norm of `D` in terms of the span: `‖D(r)‖ = ‖z − 1‖ · exp(∫₀ʳ (2/(u₁ o) − Re 2/(f u₁))) · e(r)`. -/
theorem norm_sub_gapC_eq {z : ℂ} {t : ℝ} (ht : t ∈ Icc 0 T) {v : ℝ → ℂ}
    (hv : QuantumZipper.IsForwardSol w z t v) (r : ℝ) (hr : r ∈ Icc 0 t) :
    ‖v r - ((v1 r - w r : ℝ) : ℂ)‖ = ‖z - 1‖ *
      Real.exp (∫ s in (0 : ℝ)..r, (spanRate w v0 v1 s - (2 / (v s * ((v1 s - w s : ℝ) : ℂ))).re)) *
      (v1 r - v0 r) := by
  have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
  have hr' : r ∈ Icc 0 T := hsub hr
  have hrr : Icc 0 r ⊆ Icc 0 t := Icc_subset_Icc_right hr.2
  have hgc : ContinuousOn (fun s => (((v1 s - w s : ℝ)) : ℂ)) (Icc 0 t) := h.continuousOn_gapC.mono hsub
  have hcont : ContinuousOn (fun s => 2 / (v s * ((v1 s - w s : ℝ) : ℂ))) (Icc 0 r) :=
    (continuousOn_const.div (hv.1.mul hgc) fun s hs =>
      mul_ne_zero (hv.2 s hs).1 (Complex.ofReal_ne_zero.2 (h.gap_pos s (hsub hs)).ne')).mono hrr
  have hint : IntervalIntegrable (fun s => 2 / (v s * ((v1 s - w s : ℝ) : ℂ))) volume 0 r :=
    hcont.intervalIntegrable_of_Icc hr.1
  have hre : (∫ s in (0 : ℝ)..r, 2 / (v s * ((v1 s - w s : ℝ) : ℂ))).re =
      ∫ s in (0 : ℝ)..r, (2 / (v s * ((v1 s - w s : ℝ) : ℂ))).re :=
    ((Complex.reCLM).intervalIntegral_comp_comm hint).symm
  have hspan : IntervalIntegrable (spanRate w v0 v1) volume 0 r :=
    h.intervalIntegrable_spanRate.mono_set (uIcc_subset_uIcc_left (by rw [uIcc_of_le h.nonneg]; exact hr'))
  have hreI : IntervalIntegrable (fun s => (2 / (v s * ((v1 s - w s : ℝ) : ℂ))).re) volume 0 r :=
    (Complex.continuous_re.comp_continuousOn hcont).intervalIntegrable_of_Icc hr.1
  rw [h.sub_gapC_eq ht hv r hr, norm_mul, Complex.norm_exp, Complex.neg_re, hre, h.span_eq_exp r hr',
    intervalIntegral.integral_sub hspan hreI, mul_assoc, ← Real.exp_add]
  congr 2
  ring

theorem intervalIntegrable_budget : IntervalIntegrable (budget w v0 v1) volume 0 T := by
  have hgap : ∀ t ∈ Icc 0 T, v1 t - w t ≠ 0 := fun t ht => (h.gap_pos t ht).ne'
  have hc1 : ContinuousOn (fun s => 4 * (v1 s - v0 s) / (v1 s - w s) ^ 2) (uIcc 0 T) := by
    rw [uIcc_of_le h.nonneg]
    exact (continuousOn_const.mul (h.cont_v1.sub h.cont_v0)).div (h.continuousOn_gap.pow 2)
      fun t ht => pow_ne_zero 2 (hgap t ht)
  have hc2 : ContinuousOn (fun s => 4 * (v1 s - v0 s) / (v1 s - w s) ^ 3) (Icc 0 T) :=
    (continuousOn_const.mul (h.cont_v1.sub h.cont_v0)).div (h.continuousOn_gap.pow 3)
      fun t ht => pow_ne_zero 3 (hgap t ht)
  have := (h.int_v0.continuousOn_mul hc1).add (hc2.intervalIntegrable_of_Icc h.nonneg)
  refine this.congr fun s _ => ?_
  simp only [budget]
  rw [← div_eq_mul_inv, div_div]

theorem budget_nonneg (s : ℝ) (hs : s ∈ Icc 0 T) : 0 ≤ budget w v0 v1 s := by
  have he : 0 ≤ v1 s - v0 s := (h.span_pos s hs).le
  have hu := h.gap_pos s hs
  have ho : 0 ≤ v0 s - w s := sub_nonneg.2 (h.w_le_v0 s hs)
  unfold budget
  positivity

/-- **The pointwise budget bound**: while `‖D‖ ≤ e/2` and `o > 0`, `2/(u₁ o) − Re 2/(f u₁) ≤ β/2`. -/
theorem integrand_le_budget {s : ℝ} (hs : s ∈ Icc 0 T) (hne : v0 s ≠ w s) {f : ℂ}
    (hD : ‖f - ((v1 s - w s : ℝ) : ℂ)‖ ≤ (v1 s - v0 s) / 2) :
    spanRate w v0 v1 s - (2 / (f * ((v1 s - w s : ℝ) : ℂ))).re ≤ budget w v0 v1 s / 2 := by
  set c := v1 s - w s with hc
  set o := v0 s - w s with ho
  set e := v1 s - v0 s with he
  set D := f - (c : ℂ) with hDdef
  have hcpos : 0 < c := h.gap_pos s hs
  have hopos : 0 < o := lt_of_le_of_ne (sub_nonneg.2 (h.w_le_v0 s hs)) (Ne.symm (sub_ne_zero.2 hne))
  have hec : e = c - o := by rw [he, hc, ho]; ring
  have hD2 : ‖D‖ ≤ c / 2 := hD.trans (by rw [hec]; linarith)
  have hf : f = (c : ℂ) + D := by rw [hDdef]; ring
  have hre : (2 / (f * (c : ℂ))).re = 2 / c * ((c : ℂ) + D)⁻¹.re := by
    have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hcpos.ne'
    have : (2 : ℂ) / (f * c) = ((2 / c : ℝ) : ℂ) * ((c : ℂ) + D)⁻¹ := by
      rw [hf]; push_cast; field_simp
    rw [this, Complex.re_ofReal_mul]
  have hlow := re_inv_add_ge hcpos hD2
  have hre' : 2 / c ^ 2 - 4 * ‖D‖ / c ^ 3 ≤ (2 / (f * (c : ℂ))).re := by
    rw [hre]
    have h2c : 0 ≤ 2 / c := by positivity
    have := mul_le_mul_of_nonneg_left hlow h2c
    have e1 : 2 / c * (1 / c - 2 * ‖D‖ / c ^ 2) = 2 / c ^ 2 - 4 * ‖D‖ / c ^ 3 := by
      field_simp
      ring
    linarith
  have hkey : 2 / (c * o) - 2 / c ^ 2 = 2 * e / (c ^ 2 * o) := by
    rw [hec]
    field_simp
  have hDe : 4 * ‖D‖ / c ^ 3 ≤ 2 * e / c ^ 3 := by
    apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  have hsr : spanRate w v0 v1 s = 2 / (c * o) := rfl
  have hb : budget w v0 v1 s / 2 = 2 * e / (c ^ 2 * o) + 2 * e / c ^ 3 := by
    simp only [budget, ← hc, ← ho, ← he]
    ring
  rw [hsr, hb]
  linarith

/-- **The bootstrap**: if `∫₀ᵀ β ≤ C` and `‖z − 1‖ e^{C/2} < 1/2`, every forward solution from `z` on `[0, t] ⊆ [0, T]`
stays in the disk `B(u₁, e/2)`. -/
theorem norm_sub_gapC_lt {C : ℝ} (hC : ∫ s in (0 : ℝ)..T, budget w v0 v1 s ≤ C) {z : ℂ}
    (hz : ‖z - 1‖ * Real.exp (C / 2) < 1 / 2) {t : ℝ} (ht : t ∈ Icc 0 T) {v : ℝ → ℂ}
    (hv : QuantumZipper.IsForwardSol w z t v) :
    ∀ r ∈ Icc 0 t, ‖v r - ((v1 r - w r : ℝ) : ℂ)‖ < (v1 r - v0 r) / 2 := by
  have hsub : Icc 0 t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
  intro r hr
  by_contra hbad
  rw [not_lt] at hbad
  set A : Set ℝ := Icc 0 t ∩ (fun s => ((v1 s - v0 s) / 2, ‖v s - ((v1 s - w s : ℝ) : ℂ)‖)) ⁻¹'
    {p : ℝ × ℝ | p.1 ≤ p.2} with hA
  have hgc : ContinuousOn (fun s => (((v1 s - w s : ℝ)) : ℂ)) (Icc 0 t) := h.continuousOn_gapC.mono hsub
  have hAcl : IsClosed A := by
    refine ContinuousOn.preimage_isClosed_of_isClosed ?_ isClosed_Icc
      (isClosed_le continuous_fst continuous_snd)
    exact ((((h.cont_v1.sub h.cont_v0).mono hsub).div_const 2)).prodMk (hv.1.sub hgc).norm
  have hAne : A.Nonempty := ⟨r, hr, hbad⟩
  have hAbdd : BddBelow A := ⟨0, fun s hs => hs.1.1⟩
  set r₀ := sInf A with hr₀
  have hr₀A : r₀ ∈ A := hAcl.csInf_mem hAne hAbdd
  have hr₀I : r₀ ∈ Icc 0 t := hr₀A.1
  have hr₀T : r₀ ∈ Icc 0 T := hsub hr₀I
  have hbefore : ∀ s ∈ Ico 0 r₀, ‖v s - ((v1 s - w s : ℝ) : ℂ)‖ < (v1 s - v0 s) / 2 := by
    intro s hs
    by_contra hns
    rw [not_lt] at hns
    have hsA : s ∈ A := ⟨⟨hs.1, hs.2.le.trans hr₀I.2⟩, hns⟩
    exact absurd (csInf_le hAbdd hsA) (not_le.2 hs.2)
  -- the integral of the exponent is at most `C/2`
  have hrr : Icc 0 r₀ ⊆ Icc 0 t := Icc_subset_Icc_right hr₀I.2
  have hcont : ContinuousOn (fun s => 2 / (v s * ((v1 s - w s : ℝ) : ℂ))) (Icc 0 r₀) :=
    (continuousOn_const.div (hv.1.mul hgc) fun s hs =>
      mul_ne_zero (hv.2 s hs).1 (Complex.ofReal_ne_zero.2 (h.gap_pos s (hsub hs)).ne')).mono hrr
  have hspan : IntervalIntegrable (spanRate w v0 v1) volume 0 r₀ :=
    h.intervalIntegrable_spanRate.mono_set
      (uIcc_subset_uIcc_left (by rw [uIcc_of_le h.nonneg]; exact hr₀T))
  have hreI : IntervalIntegrable (fun s => (2 / (v s * ((v1 s - w s : ℝ) : ℂ))).re) volume 0 r₀ :=
    (Complex.continuous_re.comp_continuousOn hcont).intervalIntegrable_of_Icc hr₀I.1
  have hbI : IntervalIntegrable (fun s => budget w v0 v1 s / 2) volume 0 r₀ :=
    (h.intervalIntegrable_budget.mono_set
      (uIcc_subset_uIcc_left (by rw [uIcc_of_le h.nonneg]; exact hr₀T))).div_const 2
  have hle1 : ∫ s in (0 : ℝ)..r₀, (spanRate w v0 v1 s - (2 / (v s * ((v1 s - w s : ℝ) : ℂ))).re) ≤
      ∫ s in (0 : ℝ)..r₀, budget w v0 v1 s / 2 := by
    refine intervalIntegral.integral_mono_ae_restrict hr₀I.1 (hspan.sub hreI) hbI ?_
    have hr0 : ∀ᵐ x : ℝ, x ≠ r₀ := by simp [ae_iff, measure_singleton]
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
    filter_upwards [h.ae_ne, hr0] with s hne hsr hs
    have hsT : s ∈ Icc 0 T := ⟨hs.1, hs.2.trans hr₀T.2⟩
    exact h.integrand_le_budget hsT (hne hsT) (hbefore s ⟨hs.1, lt_of_le_of_ne hs.2 hsr⟩).le
  have hle2 : ∫ s in (0 : ℝ)..r₀, budget w v0 v1 s ≤ ∫ s in (0 : ℝ)..T, budget w v0 v1 s := by
    refine intervalIntegral.integral_mono_interval le_rfl hr₀I.1 hr₀T.2 ?_ h.intervalIntegrable_budget
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
    exact Filter.Eventually.of_forall fun s hs => h.budget_nonneg s ⟨hs.1.le, hs.2⟩
  have hhalf : ∫ s in (0 : ℝ)..r₀, budget w v0 v1 s / 2 = (∫ s in (0 : ℝ)..r₀, budget w v0 v1 s) / 2 :=
    intervalIntegral.integral_div _ _
  have hexp : Real.exp (∫ s in (0 : ℝ)..r₀,
      (spanRate w v0 v1 s - (2 / (v s * ((v1 s - w s : ℝ) : ℂ))).re)) ≤ Real.exp (C / 2) :=
    Real.exp_le_exp.2 (by rw [hhalf] at hle1; linarith)
  have hnorm := h.norm_sub_gapC_eq ht hv r₀ hr₀I
  have hepos := h.span_pos r₀ hr₀T
  have hlt : ‖v r₀ - ((v1 r₀ - w r₀ : ℝ) : ℂ)‖ < (v1 r₀ - v0 r₀) / 2 := by
    rw [hnorm]
    calc ‖z - 1‖ * Real.exp _ * (v1 r₀ - v0 r₀) ≤ ‖z - 1‖ * Real.exp (C / 2) * (v1 r₀ - v0 r₀) := by
          gcongr
      _ < 1 / 2 * (v1 r₀ - v0 r₀) := mul_lt_mul_of_pos_right hz hepos
      _ = (v1 r₀ - v0 r₀) / 2 := by ring
  exact absurd hr₀A.2 (not_le.2 hlt)

/-- **Points of `ℍ` near the mark are not swallowed**: if `∫₀ᵀ β ≤ C`, `z ∈ ℍ` and `‖z − 1‖ e^{C/2} < 1/2`, then
`z ∉ K_T`. -/
theorem not_mem_fwdHull {C : ℝ} (hC : ∫ s in (0 : ℝ)..T, budget w v0 v1 s ≤ C) {z : ℂ} (hzH : 0 < z.im)
    (hz : ‖z - 1‖ * Real.exp (C / 2) < 1 / 2) : z ∉ QuantumZipper.fwdHull w T := by
  intro hK
  obtain ⟨-, σ, hσT, hσ, hcl⟩ := (QuantumZipper.FwdClock.mem_fwdHull_iff_clock h.cont_w).1 hK
  obtain ⟨δ, hδ, hδle⟩ := h.exists_pos_le_gap
  obtain ⟨t, ht0, htσ, hM⟩ := hcl (4 * T / δ ^ 2)
  have htT : t ≤ T := htσ.le.trans hσT
  have hzt : z ∉ QuantumZipper.fwdHull w t := by
    rintro ⟨-, hle⟩
    rw [hσ, ENNReal.ofReal_le_ofReal_iff ht0] at hle
    linarith
  obtain ⟨v, hv⟩ := QuantumZipper.exists_isForwardSol_of_not_mem_fwdHull ht0 hzH hzt
  have htI : t ∈ Icc 0 T := ⟨ht0, htT⟩
  have hlow : ∀ r ∈ Icc (0 : ℝ) t, δ / 2 ≤ ‖QuantumZipper.fwdMap w r z‖ := by
    intro r hr
    have hrT : r ∈ Icc 0 T := ⟨hr.1, hr.2.trans htT⟩
    rw [QuantumZipper.fwdMap_eq h.cont_w hzH hv hr]
    have hb := h.norm_sub_gapC_lt hC hz htI hv r hr
    have he := h.span_le_gap r hrT
    have h1 : ‖(((v1 r - w r : ℝ)) : ℂ)‖ = v1 r - w r := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (h.gap_pos r hrT)]
    have h2 := norm_sub_norm_le (((v1 r - w r : ℝ)) : ℂ) (v r)
    rw [norm_sub_rev] at h2
    have := hδle r hrT
    linarith
  have hclock : QuantumZipper.FwdClock.fwdClock w t z ≤ 4 * T / δ ^ 2 := by
    have hI := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := t)
      (C := 4 / δ ^ 2) (f := fun r => 1 / ‖QuantumZipper.fwdMap w r z‖ ^ 2) (fun r hr => by
        rw [uIoc_of_le ht0] at hr
        have hl := hlow r ⟨hr.1.le, hr.2⟩
        rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        have hδ2 : 0 < δ / 2 := by positivity
        calc 1 / ‖QuantumZipper.fwdMap w r z‖ ^ 2 ≤ 1 / (δ / 2) ^ 2 :=
              one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hδ2.le hl 2)
          _ = 4 / δ ^ 2 := by field_simp; norm_num)
    calc QuantumZipper.FwdClock.fwdClock w t z
        ≤ ‖∫ r in (0 : ℝ)..t, 1 / ‖QuantumZipper.fwdMap w r z‖ ^ 2‖ := Real.le_norm_self _
      _ ≤ 4 / δ ^ 2 * |t - 0| := hI
      _ ≤ 4 * T / δ ^ 2 := by
        rw [sub_zero, abs_of_nonneg ht0, div_mul_eq_mul_div]
        gcongr
  linarith

end IsSeedMarkPath

end G11

end Supp7

end InteractingSLE
