import GaussianLQG.Core.Defs
import LQGMetric.Field.ExistSFub2

/-!
# Regularity of the white-noise frame functions (blueprint Appendix B, `lem:frame-props`)

For a white-noise vector `g ∈ L²(ℝ × ℂ)` the (unnormalized) frame function is
`frameFun0 g u = ∫ kerPt u q g(q) dq`, where `kerPt u (t, y) = √π 1_{t>0}(p_{t/2}(u,y) −
1_{t>1} p_{t/2}(0,y))` is the heat-kernel integrand of `LQGMetric`'s white-noise representation of
the field. For a *nice* `g` (essentially bounded, vanishing outside a bounded set that stays at
distance `a > 0` from time `0`) the kernel is bounded by `√π (π a)⁻¹` on the support of `g`, so:

* `IsNiceWN.integrable`: `g` is integrable;
* `continuous_frameFun0`, `exists_bound_frameFun0`: `frameFun0 g` is continuous and bounded
  (dominated convergence);
* `continuous_frameFunN`, `exists_bound_frameFunN`, `measurable_frameFunN`: the same for the
  normalized direction `frameFunN g = frameFun0 g − avg_{∂𝔻} frameFun0 g`;
* `integral_mul_frameFun0`: `∫ f(u) frameFun0 g u du = ∫ kerFun f · g` for integrable `f`
  (Fubini), with the special cases
  `integral_rectInd_mul_frameFun0`: `∫ 1_{[0,x]}(u) frameFun0 g u du = ⟪rectL2 x, g⟫` (the frame
  function integrated over the signed rectangle `[0, x]` is the white-noise pairing of the
  antiderivative kernel `LQGMetric.GFFExist.rectL2 x` with `g`), and
  `integral_test_mul_frameFun0`: `∫ φ frameFun0 g = ⟪testL2 φ, g⟫` for test functions `φ`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped RealInnerProductSpace

namespace GaussianLQG

open LQGMetric

/-! ## The kernel `kerPt` -/

/-- `kerPt` as a difference of two indicators. -/
lemma kerPt_eq (u : ℂ) (q : ℝ × ℂ) :
    kerPt u q = Real.sqrt Real.pi *
      ({q : ℝ × ℂ | 0 < q.1}.indicator (fun q => heatKernel (q.1 / 2) u q.2) q -
        {q : ℝ × ℂ | 1 < q.1}.indicator (fun q => heatKernel (q.1 / 2) 0 q.2) q) := by
  unfold kerPt
  by_cases h0 : 0 < q.1
  · by_cases h1 : 1 < q.1
    · simp [indicator, h0, h1]
    · simp [indicator, h0, h1]
  · have h1 : ¬ 1 < q.1 := fun h => h0 (lt_trans one_pos h)
    simp [indicator, h0, h1]

/-- Joint measurability of `(u, q) ↦ kerPt u q`. -/
lemma measurable_kerPt₂ : Measurable fun p : ℂ × (ℝ × ℂ) => kerPt p.1 p.2 := by
  have e : (fun p : ℂ × (ℝ × ℂ) => kerPt p.1 p.2) = fun p => Real.sqrt Real.pi *
      ((if 0 < p.2.1 then heatKernel (p.2.1 / 2) p.1 p.2.2 else 0) -
        (if 1 < p.2.1 then heatKernel (p.2.1 / 2) 0 p.2.2 else 0)) := by
    funext p
    rw [kerPt_eq]
    simp only [Set.indicator_apply, Set.mem_ofPred_eq]
  rw [e]
  refine measurable_const.mul (Measurable.sub ?_ ?_)
  · exact Measurable.ite (measurableSet_lt measurable_const (by fun_prop))
      (by unfold heatKernel; fun_prop) measurable_const
  · exact Measurable.ite (measurableSet_lt measurable_const (by fun_prop))
      (by unfold heatKernel; fun_prop) measurable_const

lemma measurable_kerPt (u : ℂ) : Measurable (kerPt u) := by
  have h : Measurable ((fun p : ℂ × (ℝ × ℂ) => kerPt p.1 p.2) ∘ Prod.mk u) :=
    measurable_kerPt₂.comp measurable_prodMk_left
  exact h

lemma kerPt_of_nonpos (u : ℂ) {q : ℝ × ℂ} (hq : q.1 ≤ 0) : kerPt u q = 0 := by
  unfold kerPt
  rw [indicator_of_notMem (show q.1 ∉ Ioi (0 : ℝ) from not_lt.mpr hq), mul_zero]

/-- On positive times, `|kerPt u (t, y)| ≤ √π (π t)⁻¹`. -/
lemma abs_kerPt_le (u : ℂ) {q : ℝ × ℂ} (hq : 0 < q.1) :
    |kerPt u q| ≤ Real.sqrt Real.pi * (Real.pi * q.1)⁻¹ := by
  have hs : 0 < q.1 / 2 := by linarith
  have hb : ∀ z w : ℂ, heatKernel (q.1 / 2) z w ≤ (Real.pi * q.1)⁻¹ := fun z w => by
    have := LQGMetric.GFFExist.heatKernel_le (q.1 / 2) hs z w
    rwa [show 2 * Real.pi * (q.1 / 2) = Real.pi * q.1 by ring] at this
  have h1 := hb u q.2
  have h2 := hb 0 q.2
  have h3 := LQGMetric.heatKernel_nonneg (q.1 / 2) hs.le u q.2
  have h4 := LQGMetric.heatKernel_nonneg (q.1 / 2) hs.le 0 q.2
  have hc : 0 ≤ (Ioi (1 : ℝ)).indicator (fun _ => heatKernel (q.1 / 2) 0 q.2) q.1 :=
    indicator_nonneg (fun _ _ => h4) _
  have hc' : (Ioi (1 : ℝ)).indicator (fun _ => heatKernel (q.1 / 2) 0 q.2) q.1 ≤
      (Real.pi * q.1)⁻¹ := by
    by_cases h : q.1 ∈ Ioi (1 : ℝ)
    · rw [indicator_of_mem h]; exact h2
    · rw [indicator_of_notMem h]; positivity
  unfold kerPt
  rw [indicator_of_mem (show q.1 ∈ Ioi (0 : ℝ) from hq), abs_mul,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  rw [abs_le]
  constructor <;> linarith

/-- On `|t| ≥ a > 0`, `|kerPt u (t, y)| ≤ √π (π a)⁻¹`. -/
lemma abs_kerPt_le_of_le {a : ℝ} (ha : 0 < a) (u : ℂ) {q : ℝ × ℂ} (hq : a ≤ |q.1|) :
    |kerPt u q| ≤ Real.sqrt Real.pi * (Real.pi * a)⁻¹ := by
  rcases le_or_gt q.1 0 with h | h
  · rw [kerPt_of_nonpos u h, abs_zero]; positivity
  · rw [abs_of_pos h] at hq
    refine (abs_kerPt_le u h).trans (mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _))
    exact inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left hq Real.pi_pos.le)

lemma continuous_kerPt (q : ℝ × ℂ) : Continuous fun u => kerPt u q := by
  unfold kerPt
  by_cases h : q.1 ∈ Ioi (0 : ℝ)
  · simp only [indicator_of_mem h]
    unfold heatKernel
    fun_prop
  · simp only [indicator_of_notMem h, mul_zero]
    exact continuous_const

/-! ## Nice white-noise vectors -/

namespace IsNiceWN

variable {g : WNSpace}

/-- A nice vector is dominated by a constant on a compact box. -/
lemma exists_dom (hg : IsNiceWN g) : ∃ a M : ℝ, 0 < a ∧ ∃ T : Set (ℝ × ℂ), IsCompact T ∧
    MeasurableSet T ∧ (∀ᵐ q ∂(volume : Measure (ℝ × ℂ)),
      |(g : ℝ × ℂ → ℝ) q| ≤ T.indicator (fun _ => M) q) ∧
    ∀ᵐ q ∂(volume : Measure (ℝ × ℂ)), (g : ℝ × ℂ → ℝ) q ≠ 0 → a ≤ |q.1| := by
  obtain ⟨a, b, M, R, ha, hM, hS⟩ := hg
  refine ⟨a, M, ha, Icc (-b) b ×ˢ Metric.closedBall (0 : ℂ) R,
    isCompact_Icc.prod (isCompact_closedBall _ _), measurableSet_Icc.prod measurableSet_closedBall,
    ?_, ?_⟩
  · filter_upwards [hM, hS] with q h1 h2
    by_cases h0 : (g : ℝ × ℂ → ℝ) q = 0
    · rw [h0, abs_zero]
      by_cases hT : q ∈ Icc (-b) b ×ˢ Metric.closedBall (0 : ℂ) R
      · rw [indicator_of_mem hT]; exact (abs_nonneg _).trans (h0 ▸ h1)
      · rw [indicator_of_notMem hT]
    · obtain ⟨_, hb, hR⟩ := h2 h0
      rw [indicator_of_mem (mem_prod.mpr ⟨abs_le.mp hb, by simpa using hR⟩)]
      exact h1
  · filter_upwards [hS] with q h hq
    exact (h hq).1

/-- A nice vector is integrable. -/
lemma integrable (hg : IsNiceWN g) : Integrable (g : ℝ × ℂ → ℝ) := by
  obtain ⟨a, M, ha, T, hTc, hTm, hdom, -⟩ := hg.exists_dom
  refine Integrable.mono' ((integrable_indicator_iff hTm).2
    (integrableOn_const (C := M) hTc.measure_lt_top.ne)) (Lp.aestronglyMeasurable g) ?_
  filter_upwards [hdom] with q hq
  rwa [Real.norm_eq_abs]

/-- The kernel is uniformly bounded on the support of a nice vector. -/
lemma exists_bound_kerPt_mul (hg : IsNiceWN g) : ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℂ,
    ∀ᵐ q ∂(volume : Measure (ℝ × ℂ)), |kerPt u q * (g : ℝ × ℂ → ℝ) q| ≤
      C * |(g : ℝ × ℂ → ℝ) q| := by
  obtain ⟨a, M, ha, T, -, -, -, hsupp⟩ := hg.exists_dom
  refine ⟨Real.sqrt Real.pi * (Real.pi * a)⁻¹, by positivity, fun u => ?_⟩
  filter_upwards [hsupp] with q hq
  rw [abs_mul]
  by_cases h0 : (g : ℝ × ℂ → ℝ) q = 0
  · rw [h0, abs_zero, mul_zero, mul_zero]
  · exact mul_le_mul_of_nonneg_right (abs_kerPt_le_of_le ha u (hq h0)) (abs_nonneg _)

lemma integrable_kerPt_mul (hg : IsNiceWN g) (u : ℂ) :
    Integrable fun q => kerPt u q * (g : ℝ × ℂ → ℝ) q := by
  obtain ⟨C, -, hC⟩ := hg.exists_bound_kerPt_mul
  refine Integrable.mono' (hg.integrable.abs.const_mul C)
    ((measurable_kerPt u).aestronglyMeasurable.mul (Lp.aestronglyMeasurable g)) ?_
  filter_upwards [hC u] with q hq
  rwa [Real.norm_eq_abs]

end IsNiceWN

/-! ## Regularity of the frame functions -/

variable {g : WNSpace}

theorem continuous_frameFun0 (hg : IsNiceWN g) : Continuous (frameFun0 g) := by
  obtain ⟨C, -, hC⟩ := hg.exists_bound_kerPt_mul
  unfold frameFun0
  refine continuous_of_dominated (bound := fun q => C * |(g : ℝ × ℂ → ℝ) q|)
    (fun u => (measurable_kerPt u).aestronglyMeasurable.mul (Lp.aestronglyMeasurable g))
    (fun u => ?_) (hg.integrable.abs.const_mul C) (Eventually.of_forall fun q => ?_)
  · filter_upwards [hC u] with q hq
    rwa [Real.norm_eq_abs]
  · exact (continuous_kerPt q).mul continuous_const

/-- `|frameFun0 g u| ≤ C` for all `u`. -/
theorem exists_bound_frameFun0 (hg : IsNiceWN g) : ∃ C : ℝ, ∀ u, |frameFun0 g u| ≤ C := by
  obtain ⟨C, -, hC⟩ := hg.exists_bound_kerPt_mul
  refine ⟨C * ∫ q, |(g : ℝ × ℂ → ℝ) q|, fun u => ?_⟩
  unfold frameFun0
  calc |∫ q, kerPt u q * (g : ℝ × ℂ → ℝ) q| ≤ ∫ q, |kerPt u q * (g : ℝ × ℂ → ℝ) q| :=
        abs_integral_le_integral_abs
    _ ≤ ∫ q, C * |(g : ℝ × ℂ → ℝ) q| :=
        integral_mono_ae (hg.integrable_kerPt_mul u).abs (hg.integrable.abs.const_mul C) (hC u)
    _ = C * ∫ q, |(g : ℝ × ℂ → ℝ) q| := integral_const_mul _ _

/-- A circle average of a function bounded by `C` is bounded by `C`. -/
lemma abs_circleAverage_le_of_abs_le {f : ℂ → ℝ} (hf : Continuous f) {C : ℝ}
    (hC : ∀ u, |f u| ≤ C) (c : ℂ) (r : ℝ) : |Real.circleAverage f c r| ≤ C := by
  refine Real.abs_circleAverage_le_circleAverage_abs.trans ?_
  exact Real.circleAverage_mono_on_of_le_circle
    ((continuous_abs.comp hf).continuousOn.circleIntegrable') fun u _ => hC u

theorem continuous_frameFunN (hg : IsNiceWN g) : Continuous (frameFunN g) :=
  (continuous_frameFun0 hg).sub continuous_const

theorem measurable_frameFunN (hg : IsNiceWN g) : Measurable (frameFunN g) :=
  (continuous_frameFunN hg).measurable

/-- `|frameFunN g u| ≤ C` for all `u`. -/
theorem exists_bound_frameFunN (hg : IsNiceWN g) : ∃ C : ℝ, ∀ u, |frameFunN g u| ≤ C := by
  obtain ⟨C, hC⟩ := exists_bound_frameFun0 hg
  refine ⟨C + C, fun u => ?_⟩
  unfold frameFunN
  exact (abs_sub _ _).trans (add_le_add (hC u)
    (abs_circleAverage_le_of_abs_le (continuous_frameFun0 hg) hC 0 1))

/-! ## Integrals over rectangles: the link with `LQGMetric`'s antiderivative field -/

/-- `LQGMetric`'s white-noise kernel of a function is the `kerPt`-transform of that function. -/
lemma kerFun_eq_integral_mul_kerPt (f : ℂ → ℝ) (q : ℝ × ℂ) :
    LQGMetric.GFFExist.kerFun f q = ∫ u, f u * kerPt u q := by
  unfold LQGMetric.GFFExist.kerFun LQGMetric.GFFExist.kerInner kerPt
  by_cases h : q.1 ∈ Ioi (0 : ℝ)
  · simp only [indicator_of_mem h]
    rw [← integral_const_mul]
    congr 1; funext u; ring
  · simp only [indicator_of_notMem h, mul_zero, integral_zero]

/-- **Weighted integrals of the frame functions (Fubini).** For a nice `g` and an integrable
weight `f`, `∫ f(u) frameFun0 g u du = ∫ kerFun f · g`. -/
theorem integral_mul_frameFun0 (hg : IsNiceWN g) {f : ℂ → ℝ} (hf : Integrable f) :
    ∫ u, f u * frameFun0 g u = ∫ q, LQGMetric.GFFExist.kerFun f q * (g : ℝ × ℂ → ℝ) q := by
  obtain ⟨C, hC0, hC⟩ := hg.exists_bound_kerPt_mul
  set F : ℂ × (ℝ × ℂ) → ℝ := fun p => f p.1 * kerPt p.1 p.2 * (g : ℝ × ℂ → ℝ) p.2 with hF
  have hFm : AEStronglyMeasurable F (volume.prod volume) :=
    (hf.aestronglyMeasurable.comp_fst.mul measurable_kerPt₂.aestronglyMeasurable).mul
      (Lp.aestronglyMeasurable g).comp_snd
  have hFi : Integrable F (volume.prod volume) := by
    rw [integrable_prod_iff hFm]
    refine ⟨Eventually.of_forall fun u => ?_, ?_⟩
    · simp only [hF, mul_assoc]
      exact (hg.integrable_kerPt_mul u).const_mul _
    · refine Integrable.mono' ((hf.abs.mul_const (C * ∫ q, |(g : ℝ × ℂ → ℝ) q|)))
        hFm.norm.integral_prod_right' (Eventually.of_forall fun u => ?_)
      have e : ∫ q, ‖F (u, q)‖ = |f u| * ∫ q, |kerPt u q * (g : ℝ × ℂ → ℝ) q| := by
        rw [← integral_const_mul]
        congr 1; funext q
        simp only [hF, Real.norm_eq_abs, abs_mul]; ring
      rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _), e]
      refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
      rw [← integral_const_mul]
      exact integral_mono_ae (hg.integrable_kerPt_mul u).abs (hg.integrable.abs.const_mul C) (hC u)
  have e1 : ∀ u, f u * frameFun0 g u = ∫ q, F (u, q) := fun u => by
    unfold frameFun0
    rw [← integral_const_mul]
    congr 1; funext q; simp only [hF]; ring
  have e2 : ∀ q, LQGMetric.GFFExist.kerFun f q * (g : ℝ × ℂ → ℝ) q = ∫ u, F (u, q) := fun q => by
    rw [kerFun_eq_integral_mul_kerPt, ← integral_mul_const]
  simp_rw [e1, e2]
  exact integral_integral_swap hFi

/-- **Rectangle integrals of the frame functions.** For a nice `g`, the integral of `frameFun0 g`
over the signed rectangle `[0, x]` is the white-noise pairing `⟪rectL2 x, g⟫`. -/
theorem integral_rectInd_mul_frameFun0 (hg : IsNiceWN g) (x : ℂ) :
    ∫ u, LQGMetric.GFFExist.rectInd x u * frameFun0 g u = ⟪LQGMetric.GFFExist.rectL2 x, g⟫ := by
  rw [integral_mul_frameFun0 hg (LQGMetric.GFFExist.rectInd_bddSupp x).integrable,
    LQGMetric.GFFExist.inner_rectL2_eq]

/-- **Test-function pairings of the frame functions.** For a nice `g` and a test function `φ`,
`∫ φ frameFun0 g = ⟪testL2 φ, g⟫`, the white-noise pairing of `LQGMetric`'s kernel of `φ`. -/
theorem integral_test_mul_frameFun0 (hg : IsNiceWN g) (φ : LQGMetric.TestC) :
    ∫ u, φ u * frameFun0 g u = ⟪LQGMetric.GFFExist.testL2 φ, g⟫ := by
  rw [integral_mul_frameFun0 hg (LQGMetric.GFFInv.integrable_test φ),
    LQGMetric.GFFExist.inner_testL2_eq]

end GaussianLQG
