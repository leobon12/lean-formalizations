/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import InteractingSLE.Frozen.Spec.IsIntegratedSLEPath

/-!
# Wang–Wu at `κ = 4`, Lemma 5.3: the force span, formula (P), the clock and the bound (T)

Packet PROVE-WW-C. Source: `source/external/WW17LP/wang_wu_lean_preprocessed.pdf`, §5.2, Lemma 5.3
(p. 35), and formula (P) in the proof of Lemma 7.1 (p. 45); the same span estimate opens the proofs of
Propositions 5.5 and 7.3 and Lemmas 5.8 and 7.4.

For two force points `L_t ≤ W_t ≤ R_t` solving the integrated force-point equations
`L_t = L_0 + ∫₀ᵗ 2/(L - W)`, `R_t = R_0 + ∫₀ᵗ 2/(R - W)` with Lebesgue-null collision sets
(`TwoForcePath`), put `D = R - L` and `X = (W - L)/D`. Then (deterministically, through collisions):

* `TwoForcePath.span_eq`: `D_t = D_0 + ∫₀ᵗ 2/(D X (1 - X))`, written `2 D/((W - L)(R - W))`;
* `TwoForcePath.span_mono`: the span is nondecreasing;
* `TwoForcePath.span_sq_ge` (formula (P) integrated): `D_t² ≥ D_s² + 16 (t - s)` for `s ≤ t`, from
  `d(D²)/dt = 4/(X(1 - X)) ≥ 16` almost everywhere;
* `TwoForcePath.clock_eq` (the clock of Lemma 5.3): if `D_s > 0`,
  `2 log(D_t/D_s) = 4 ∫ₛᵗ du/(D² X (1 - X))`, written `4 ∫ₛᵗ du/((W - L)(R - W))`;
* `TwoForcePath.clock_bound` (the inequality in (T)): with `v = 2 log(D_t/D_s)`,
  `t - s ≤ D_s² (e^v - 1)/16`.

The local absolute continuity of `D` and of `log D` used in the source ("`D` is absolutely continuous and
bounded below") is Mathlib's `AbsolutelyContinuousOnInterval`, and the fundamental theorem of calculus for
absolutely continuous functions (`AbsolutelyContinuousOnInterval.integral_deriv_eq_sub`) replaces the
chain rule across the collision null set.

`IsIntegratedSLEPath.twoForcePath` extracts a `TwoForcePath` from the frozen integrated evolution for any
left mark `i` and right mark `j`, up to any time before the lifetime. The stochastic part of Lemma 5.3 (the
Jacobi equation (S) in the clock `v`) is not in this file.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter Topology Real
open scoped NNReal ENNReal

namespace InteractingSLE

namespace WangWu

namespace Span

/-! ### Absolutely continuous functions with an almost-everywhere derivative -/

section AC

/-- A function equal on `[0, T]` to a constant plus the integral of an interval-integrable function is
absolutely continuous on `[0, T]`. -/
theorem absolutelyContinuousOnInterval_of_eq_add_integral {g f : ℝ → ℝ} {T c : ℝ} (hT : 0 ≤ T)
    (hf : IntervalIntegrable f volume 0 T) (hg : ∀ t ∈ Icc 0 T, g t = c + ∫ s in (0 : ℝ)..t, f s) :
    AbsolutelyContinuousOnInterval g 0 T := by
  have hF := hf.absolutelyContinuousOnInterval_intervalIntegral (c := 0) (by simp [hT])
  have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => c) 0 T :=
    (LipschitzWith.const c).lipschitzOnWith.absolutelyContinuousOnInterval
  refine (hc.add hF).congr fun t ht => ?_
  rw [uIcc_of_le hT] at ht
  simp only [Pi.add_apply, hg t ht]

/-- On the open interval, a function equal on `[0, T]` to a constant plus an integral has the integrand as
derivative almost everywhere. -/
theorem ae_hasDerivAt_of_eq_add_integral {g f : ℝ → ℝ} {T c : ℝ} (hT : 0 ≤ T)
    (hf : IntervalIntegrable f volume 0 T) (hg : ∀ t ∈ Icc 0 T, g t = c + ∫ s in (0 : ℝ)..t, f s) :
    ∀ᵐ x, x ∈ Ioo 0 T → HasDerivAt g (f x) x := by
  filter_upwards [hf.ae_hasDerivAt_integral] with x hx hxI
  have hxI' : x ∈ uIcc 0 T := by rw [uIcc_of_le hT]; exact Ioo_subset_Icc_self hxI
  have h0 : (0 : ℝ) ∈ uIcc 0 T := by simp [hT]
  have hd := (hx hxI' 0 h0).const_add c
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hxI.1 hxI.2] with y hy
  exact hg y (Ioo_subset_Icc_self hy)

/-- If `G` is absolutely continuous on `[a, b]` and has derivative `φ x` at almost every `x ∈ (a, b)`, then
`G b - G a = ∫_a^b φ`. -/
theorem sub_eq_integral_of_ae_hasDerivAt_of_ac {G φ : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hG : AbsolutelyContinuousOnInterval G a b)
    (h : ∀ᵐ x, x ∈ Ioo a b → HasDerivAt G (φ x) x) : G b - G a = ∫ x in a..b, φ x := by
  rw [← hG.integral_deriv_eq_sub]
  refine intervalIntegral.integral_congr_ae ?_
  have hb : ∀ᵐ x : ℝ, x ≠ b := by simp [ae_iff, measure_singleton]
  filter_upwards [h, hb] with x hx hxb hxI
  rw [uIoc_of_le hab] at hxI
  exact (hx ⟨hxI.1, lt_of_le_of_ne hxI.2 hxb⟩).deriv

/-- If `G` is absolutely continuous on `[a, b]` and has a derivative `≥ c` at almost every point of
`(a, b)`, then `G b - G a ≥ c (b - a)`. -/
theorem mul_sub_le_sub_of_ae_of_ac {G φ : ℝ → ℝ} {a b c : ℝ} (hab : a ≤ b)
    (hG : AbsolutelyContinuousOnInterval G a b)
    (h : ∀ᵐ x, x ∈ Ioo a b → HasDerivAt G (φ x) x ∧ c ≤ φ x) : c * (b - a) ≤ G b - G a := by
  rw [← hG.integral_deriv_eq_sub]
  have hc : ∫ _ in a..b, c = c * (b - a) := by simp [mul_comm]
  rw [← hc]
  refine intervalIntegral.integral_mono_ae_restrict hab intervalIntegrable_const
    hG.intervalIntegrable_deriv ?_
  have ha : ∀ᵐ x : ℝ, x ≠ a := by simp [ae_iff, measure_singleton]
  have hb : ∀ᵐ x : ℝ, x ≠ b := by simp [ae_iff, measure_singleton]
  rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Icc]
  filter_upwards [h, ha, hb] with x hx hxa hxb hxI
  have hx' := hx ⟨lt_of_le_of_ne hxI.1 (Ne.symm hxa), lt_of_le_of_ne hxI.2 hxb⟩
  rw [hx'.1.deriv]
  exact hx'.2


end AC

/-! ### Two force points and their span -/

/-- `log` is `c⁻¹`-Lipschitz on `[c, ∞)` for `c > 0`. -/
theorem lipschitzOnWith_log_Ici {c : ℝ} (hc : 0 < c) :
    LipschitzOnWith (Real.toNNReal c⁻¹) Real.log (Ici c) := by
  refine (convex_Ici c).lipschitzOnWith_of_nnnorm_hasDerivWithin_le (f' := fun x => x⁻¹)
    (fun x hx => (Real.hasDerivAt_log (ne_of_gt (lt_of_lt_of_le hc hx))).hasDerivWithinAt)
    fun x hx => ?_
  have hx0 : 0 < x := lt_of_lt_of_le hc hx
  rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ (inv_nonneg.mpr hc.le), Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hx0)]
  exact inv_anti₀ hc hx

/-- Two force points `l ≤ w ≤ r` on `[0, T]` (one left mark `l`, one right mark `r`, driver `w`) solving the
integrated force-point equations (1.2) at `κ = 4`, `l_t = l_0 + ∫₀ᵗ 2/(l - w)`, `r_t = r_0 + ∫₀ᵗ 2/(r - w)`, with
integrable reciprocal gaps and Lebesgue-null collision sets (Definition 1.3). This is the pathwise content of
Definition 1.3 that the span, the clock and (P) use; any left and any right mark of an integrated evolution
give one (`IsIntegratedSLEPath.twoForcePath`). -/
structure TwoForcePath (w l r : ℝ → ℝ) (T : ℝ) : Prop where
  nonneg : 0 ≤ T
  l_le_w : ∀ t ∈ Icc 0 T, l t ≤ w t
  w_le_r : ∀ t ∈ Icc 0 T, w t ≤ r t
  integrable_l : IntervalIntegrable (fun s => 2 / (l s - w s)) volume 0 T
  integrable_r : IntervalIntegrable (fun s => 2 / (r s - w s)) volume 0 T
  l_eq : ∀ t ∈ Icc 0 T, l t = l 0 + ∫ s in (0 : ℝ)..t, 2 / (l s - w s)
  r_eq : ∀ t ∈ Icc 0 T, r t = r 0 + ∫ s in (0 : ℝ)..t, 2 / (r s - w s)
  ae_lt : ∀ᵐ s, s ∈ Icc 0 T → l s < w s ∧ w s < r s

namespace TwoForcePath

variable {w l r : ℝ → ℝ} {T : ℝ}

/-- The span drift `2/(r - w) - 2/(l - w)` (the derivative of `D = r - l`). -/
def spanDrift (w l r : ℝ → ℝ) (s : ℝ) : ℝ := 2 / (r s - w s) - 2 / (l s - w s)

/-- Away from collisions the span drift is `2 D/((w - l)(r - w)) = 2/(D X (1 - X))`. -/
theorem spanDrift_eq {s : ℝ} (hl : l s < w s) (hr : w s < r s) :
    spanDrift w l r s = 2 * (r s - l s) / ((w s - l s) * (r s - w s)) := by
  have h1 : w s - l s ≠ 0 := by linarith
  have h2 : r s - w s ≠ 0 := by linarith
  have h3 : l s - w s ≠ 0 := by linarith
  unfold spanDrift
  field_simp
  ring

/-- The span drift is nonnegative wherever `l ≤ w ≤ r`. -/
theorem spanDrift_nonneg {s : ℝ} (hl : l s ≤ w s) (hr : w s ≤ r s) : 0 ≤ spanDrift w l r s := by
  unfold spanDrift
  have h1 : 0 ≤ 2 / (r s - w s) := div_nonneg (by norm_num) (by linarith)
  have h2 : 2 / (l s - w s) ≤ 0 := div_nonpos_of_nonneg_of_nonpos (by norm_num) (by linarith)
  linarith

/-- The identity `D² X (1 - X) = (w - l)(r - w)` for `D = r - l > 0`, `X = (w - l)/D`. -/
theorem span_sq_mul_ratio {s : ℝ} (hD : 0 < r s - l s) :
    (r s - l s) ^ 2 * ((w s - l s) / (r s - l s) * (1 - (w s - l s) / (r s - l s))) =
      (w s - l s) * (r s - w s) := by
  field_simp
  ring

theorem intervalIntegrable_spanDrift (h : TwoForcePath w l r T) :
    IntervalIntegrable (spanDrift w l r) volume 0 T :=
  h.integrable_r.sub h.integrable_l

/-- **The span equation** `D_t = D_0 + ∫₀ᵗ (2/(r - w) - 2/(l - w))` on `[0, T]`. -/
theorem span_eq_add_integral (h : TwoForcePath w l r T) :
    ∀ t ∈ Icc 0 T, r t - l t = (r 0 - l 0) + ∫ s in (0 : ℝ)..t, spanDrift w l r s := by
  intro t ht
  have hsub : uIcc 0 t ⊆ uIcc 0 T := by
    rw [uIcc_of_le ht.1, uIcc_of_le h.nonneg]; exact Icc_subset_Icc le_rfl ht.2
  have hl := h.integrable_l.mono_set hsub
  have hr := h.integrable_r.mono_set hsub
  unfold spanDrift
  rw [h.l_eq t ht, h.r_eq t ht, intervalIntegral.integral_sub hr hl]
  ring

/-- **Lemma 5.3, the span equation**: `D_t = D_0 + ∫₀ᵗ 2D/((w - l)(r - w))` (that is, `Ḋ = 2/(D X(1 - X))`),
the integrand being changed on the null collision set only. -/
theorem span_eq (h : TwoForcePath w l r T) :
    ∀ t ∈ Icc 0 T, r t - l t =
      (r 0 - l 0) + ∫ s in (0 : ℝ)..t, 2 * (r s - l s) / ((w s - l s) * (r s - w s)) := by
  intro t ht
  rw [h.span_eq_add_integral t ht]
  congr 1
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [h.ae_lt] with s hs hsI
  rw [uIoc_of_le ht.1] at hsI
  obtain ⟨h1, h2⟩ := hs ⟨hsI.1.le, hsI.2.trans ht.2⟩
  exact spanDrift_eq h1 h2

theorem absolutelyContinuousOnInterval_span (h : TwoForcePath w l r T) :
    AbsolutelyContinuousOnInterval (fun t => r t - l t) 0 T :=
  absolutelyContinuousOnInterval_of_eq_add_integral h.nonneg h.intervalIntegrable_spanDrift
    h.span_eq_add_integral

theorem ae_hasDerivAt_span (h : TwoForcePath w l r T) :
    ∀ᵐ x, x ∈ Ioo 0 T → HasDerivAt (fun t => r t - l t) (spanDrift w l r x) x :=
  ae_hasDerivAt_of_eq_add_integral h.nonneg h.intervalIntegrable_spanDrift h.span_eq_add_integral

theorem uIcc_subset {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T) : uIcc s t ⊆ uIcc 0 T := by
  rw [uIcc_of_le hst, uIcc_of_le (hs.trans (hst.trans ht))]
  exact Icc_subset_Icc hs ht

/-- **The span is nondecreasing** on `[0, T]` ("left points move left and right points move right"). -/
theorem span_mono (h : TwoForcePath w l r T) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T) :
    r s - l s ≤ r t - l t := by
  have hac := h.absolutelyContinuousOnInterval_span.mono (uIcc_subset hs hst ht)
  have := mul_sub_le_sub_of_ae_of_ac (c := 0) (φ := spanDrift w l r) hst hac (by
    filter_upwards [h.ae_hasDerivAt_span] with x hx hxI
    have hxT : x ∈ Ioo 0 T := ⟨lt_of_le_of_lt hs hxI.1, lt_of_lt_of_le hxI.2 ht⟩
    exact ⟨hx hxT, spanDrift_nonneg (h.l_le_w x (Ioo_subset_Icc_self hxT))
      (h.w_le_r x (Ioo_subset_Icc_self hxT))⟩)
  simp only [zero_mul] at this
  linarith

/-- The algebra of (P): for gaps `p = w - l > 0`, `q = r - w > 0`, `2 D · 2D/(p q) ≥ 16`. -/
theorem sixteen_le_two_mul_spanDrift {s : ℝ} (hl : l s < w s) (hr : w s < r s) :
    16 ≤ 2 * (r s - l s) * spanDrift w l r s := by
  rw [spanDrift_eq hl hr]
  have hp : 0 < w s - l s := by linarith
  have hq : 0 < r s - w s := by linarith
  have hpq : 0 < (w s - l s) * (r s - w s) := mul_pos hp hq
  rw [mul_div_assoc', le_div_iff₀ hpq]
  nlinarith [sq_nonneg ((w s - l s) - (r s - w s))]

/-- **Formula (P), integrated**: `D_t² ≥ D_s² + 16 (t - s)` for `0 ≤ s ≤ t ≤ T` (from
`d(D²)/dt = 4/(X(1 - X)) ≥ 16` almost everywhere). -/
theorem span_sq_ge (h : TwoForcePath w l r T) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T) :
    (r s - l s) ^ 2 + 16 * (t - s) ≤ (r t - l t) ^ 2 := by
  have hac := h.absolutelyContinuousOnInterval_span.mono (uIcc_subset hs hst ht)
  have hac2 := hac.fun_mul hac
  have := mul_sub_le_sub_of_ae_of_ac (c := 16) hst hac2
    (φ := fun x => spanDrift w l r x * (r x - l x) + (r x - l x) * spanDrift w l r x) (by
    filter_upwards [h.ae_hasDerivAt_span, h.ae_lt] with x hx hlt hxI
    have hxT : x ∈ Ioo 0 T := ⟨lt_of_le_of_lt hs hxI.1, lt_of_lt_of_le hxI.2 ht⟩
    obtain ⟨h1, h2⟩ := hlt (Ioo_subset_Icc_self hxT)
    refine ⟨(hx hxT).mul (hx hxT), ?_⟩
    have := sixteen_le_two_mul_spanDrift h1 h2
    linarith)
  nlinarith

/-- Formula (P) from the start: `D_t² ≥ D_0² + 16 t`. In particular, for the adjacent seed (`D_0 = 0`) the
span is positive at every positive time. -/
theorem span_sq_ge_zero (h : TwoForcePath w l r T) {t : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ T) :
    (r 0 - l 0) ^ 2 + 16 * t ≤ (r t - l t) ^ 2 := by
  simpa using h.span_sq_ge le_rfl ht0 ht

/-- **The clock of Lemma 5.3**: if `D_s > 0`, then for `s ≤ t ≤ T`,
`2 log(D_t/D_s) = ∫ₛᵗ 4/((w - l)(r - w)) = 4 ∫ₛᵗ du/(D² X (1 - X))`. -/
theorem clock_eq (h : TwoForcePath w l r T) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T)
    (hDs : 0 < r s - l s) :
    2 * Real.log ((r t - l t) / (r s - l s)) =
      ∫ u in s..t, 4 / ((w u - l u) * (r u - w u)) := by
  have hac := h.absolutelyContinuousOnInterval_span.mono (uIcc_subset hs hst ht)
  have hge : ∀ u ∈ uIcc s t, r s - l s ≤ r u - l u := by
    intro u hu
    rw [uIcc_of_le hst] at hu
    exact h.span_mono hs hu.1 (hu.2.trans ht)
  have hlog := (lipschitzOnWith_log_Ici hDs).comp_absolutelyContinuousOnInterval
    (g := fun u => r u - l u) (fun u hu => mem_Ici.mpr (hge u hu)) hac
  have := sub_eq_integral_of_ae_hasDerivAt_of_ac (φ := fun u => spanDrift w l r u / (r u - l u)) hst hlog (by
    filter_upwards [h.ae_hasDerivAt_span] with x hx hxI
    have hxT : x ∈ Ioo 0 T := ⟨lt_of_le_of_lt hs hxI.1, lt_of_lt_of_le hxI.2 ht⟩
    have hpos : 0 < r x - l x := lt_of_lt_of_le hDs (hge x (by
      rw [uIcc_of_le hst]; exact Ioo_subset_Icc_self hxI))
    exact (hx hxT).log (ne_of_gt hpos))
  simp only [Function.comp] at this
  rw [Real.log_div (ne_of_gt (lt_of_lt_of_le hDs (hge t (by simp [hst])))) (ne_of_gt hDs),
    this, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [h.ae_lt] with x hlt hxI
  rw [uIoc_of_le hst] at hxI
  obtain ⟨h1, h2⟩ := hlt ⟨hs.trans hxI.1.le, hxI.2.trans ht⟩
  rw [spanDrift_eq h1 h2]
  have hp : w x - l x ≠ 0 := by linarith
  have hq : r x - w x ≠ 0 := by linarith
  have hD : r x - l x ≠ 0 := by linarith
  field_simp
  norm_num

/-- **The bound (T)**: with the clock value `v = 2 log(D_t/D_s)`, `t - s ≤ D_s² (e^v - 1)/16`. -/
theorem clock_bound (h : TwoForcePath w l r T) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T)
    (hDs : 0 < r s - l s) :
    t - s ≤ (r s - l s) ^ 2 * (Real.exp (2 * Real.log ((r t - l t) / (r s - l s))) - 1) / 16 := by
  have hDt : 0 < r t - l t := lt_of_lt_of_le hDs (h.span_mono hs hst ht)
  have hexp : Real.exp (2 * Real.log ((r t - l t) / (r s - l s))) = ((r t - l t) / (r s - l s)) ^ 2 := by
    rw [← Real.log_rpow (div_pos hDt hDs), Real.exp_log (Real.rpow_pos_of_pos (div_pos hDt hDs) _)]
    norm_cast
  rw [hexp, div_pow, mul_sub, mul_div_cancel₀ _ (pow_ne_zero 2 (ne_of_gt hDs)), mul_one]
  have := h.span_sq_ge hs hst ht
  linarith

end TwoForcePath

/-! ### From the frozen integrated evolution -/

/-- `2/(v - w) = -2 · (w - v)⁻¹`, the form of the reciprocal gaps in `IsIntegratedSLEPath`. -/
theorem two_div_sub_eq_neg_two_mul_inv (v w : ℝ) : 2 / (v - w) = -2 * (w - v)⁻¹ := by
  rw [div_eq_mul_inv, ← neg_sub w v, inv_neg]
  ring

/-- **Any left mark `i` and right mark `j` of an integrated evolution** (`IsIntegratedSLEPath` at `a = 4`,
or at any `a`: the force-point equations do not involve `a`) form a `TwoForcePath` with the driver on
`[0, T]` for every `T` before the lifetime. -/
theorem _root_.InteractingSLE.IsIntegratedSLEPath.twoForcePath {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ}
    {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {w : ℝ≥0 → ℝ} {vL : Fin nL → ℝ≥0 → ℝ}
    {vR : Fin nR → ℝ≥0 → ℝ} {b : ℝ≥0 → ℝ} {ζ : ℝ≥0∞}
    (hp : IsIntegratedSLEPath a xL xR ρL ρR w vL vR b ζ) (i : Fin nL) (j : Fin nR) {T : ℝ≥0}
    (hT : (T : ℝ≥0∞) < ζ) :
    TwoForcePath (fun s : ℝ => w s.toNNReal) (fun s => vL i s.toNNReal) (fun s => vR j s.toNNReal) T := by
  obtain ⟨_, hvL0, hvR0, _, _, _, _, hvLle, hwle, _, hintL, hintR, _, hvLeq, hvReq, hcolL, hcolR, _⟩ := hp
  have hlt : ∀ t ∈ Icc (0 : ℝ) T, ((t.toNNReal : ℝ≥0) : ℝ≥0∞) < ζ := fun t ht =>
    lt_of_le_of_lt (by exact_mod_cast Real.toNNReal_le_iff_le_coe.mpr ht.2) hT
  have hcoe : ∀ t ∈ Icc (0 : ℝ) T, ((t.toNNReal : ℝ≥0) : ℝ) = t := fun t ht => Real.coe_toNNReal t ht.1
  refine ⟨T.2, fun t ht => hvLle _ (hlt t ht) i, fun t ht => hwle _ (hlt t ht) j, ?_, ?_, ?_, ?_, ?_⟩
  · simp_rw [two_div_sub_eq_neg_two_mul_inv]
    exact (hintL T hT i).const_mul (-2)
  · simp_rw [two_div_sub_eq_neg_two_mul_inv]
    exact (hintR T hT j).const_mul (-2)
  · intro t ht
    have := hvLeq _ (hlt t ht) i
    rw [hcoe t ht] at this
    simpa [hvL0] using this
  · intro t ht
    have := hvReq _ (hlt t ht) j
    rw [hcoe t ht] at this
    simpa [hvR0] using this
  · have hL := measure_eq_zero_iff_ae_notMem.mp (hcolL i)
    have hR := measure_eq_zero_iff_ae_notMem.mp (hcolR j)
    filter_upwards [hL, hR] with s hsL hsR hs
    simp only [not_and] at hsL hsR
    exact ⟨lt_of_le_of_ne (hvLle _ (hlt s hs) i) (Ne.symm (hsL hs.1 (hlt s hs))),
      lt_of_le_of_ne (hwle _ (hlt s hs) j) (hsR hs.1 (hlt s hs))⟩

end Span

end WangWu

end InteractingSLE
