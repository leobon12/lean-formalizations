import GaussianLQG.Field.Frame.Energy
import GaussianLQG.Field.FrameFun

/-!
# The white-noise transform of a regular measure (blueprint `lem:kappa`, `lem:frame-props`)

For a regular measure `μ` let `μ° = μ − μ(ℂ) σ` (`σ` the uniform measure on `∂𝔻`) and

`kappaFun μ (t, y) = ∫ kerPt u (t, y) μ°(du) = √π 1_{t>0} ∫ p_{t/2}(u, y) μ°(du)`

(the large-time renormalization of `kerPt` integrates to `0` against `μ°`).

* `kappaFun_of_pos`, `kappaFun_of_nonpos`: the explicit formula.
* `integral_kappaFun_mul_slice`: `∫ κ_μ(t, y) κ_ν(t, y) dy = framePsi μ ν t` for `t > 0`.
* `memLp_kappaFun`: `κ_μ ∈ L²(ℝ × ℂ)`; `kappaL2 μ hμ` is its class.
* `inner_kappaL2`: `⟪κ_μ, κ_ν⟫ = energy μ ν` (blueprint `lem:kappa`).
* `integral_frameFunN_eq_inner`: `∫ frameFunN g dμ = ⟪κ_μ, g⟫` for nice `g`
  (blueprint `lem:frame-props`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal RealInnerProductSpace

namespace GaussianLQG
namespace WNFrame

open LQGMetric

/-- The white-noise transform of `μ° = μ − μ(ℂ) σ`. -/
def kappaFun (μ : Measure ℂ) (q : ℝ × ℂ) : ℝ :=
  ∫ u, kerPt u q ∂μ - μ.real univ * ∫ u, kerPt u q ∂(circleMeasure 0 1)

lemma measurable_integral_kerPt (α : Measure ℂ) [SFinite α] :
    Measurable fun q : ℝ × ℂ => ∫ u, kerPt u q ∂α :=
  (StronglyMeasurable.integral_prod_left' (f := fun p : ℂ × (ℝ × ℂ) => kerPt p.1 p.2)
    measurable_kerPt₂.stronglyMeasurable).measurable

lemma measurable_kappaFun (μ : Measure ℂ) [SFinite μ] : Measurable (kappaFun μ) :=
  (measurable_integral_kerPt μ).sub (measurable_const.mul (measurable_integral_kerPt _))

lemma integral_kerPt_of_pos (α : Measure ℂ) [IsFiniteMeasure α] {q : ℝ × ℂ} (hq : 0 < q.1) :
    ∫ u, kerPt u q ∂α = Real.sqrt Real.pi * (heatAvg α q.1 q.2 -
      α.real univ * (Ioi (1 : ℝ)).indicator (fun _ => heatKernel (q.1 / 2) 0 q.2) q.1) := by
  have hs : 0 < q.1 / 2 := by linarith
  unfold kerPt heatAvg
  simp only [indicator_of_mem (show q.1 ∈ Ioi (0 : ℝ) from hq)]
  rw [integral_const_mul, integral_sub (integrable_heatKernel_left α hs q.2) (integrable_const _),
    integral_const, smul_eq_mul]

lemma kappaFun_of_pos (μ : Measure ℂ) [IsFiniteMeasure μ] {q : ℝ × ℂ} (hq : 0 < q.1) :
    kappaFun μ q = Real.sqrt Real.pi *
      (heatAvg μ q.1 q.2 - μ.real univ * heatAvg (circleMeasure 0 1) q.1 q.2) := by
  unfold kappaFun
  rw [integral_kerPt_of_pos μ hq, integral_kerPt_of_pos _ hq, circleMeasure_real_univ]
  ring

lemma kappaFun_of_nonpos (μ : Measure ℂ) {q : ℝ × ℂ} (hq : q.1 ≤ 0) : kappaFun μ q = 0 := by
  unfold kappaFun
  simp only [kerPt_of_nonpos _ hq, integral_zero, mul_zero, sub_zero]

/-- **The slice identity.** For `t > 0`, `∫ κ_μ(t, y) κ_ν(t, y) dy = framePsi μ ν t`. -/
theorem integral_kappaFun_mul_slice (μ ν : Measure ℂ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    {t : ℝ} (ht : 0 < t) :
    Integrable (fun y => kappaFun μ (t, y) * kappaFun ν (t, y)) ∧
      ∫ y, kappaFun μ (t, y) * kappaFun ν (t, y) = framePsi μ ν t := by
  obtain ⟨i1, e1⟩ := integral_heatAvg_mul μ ν ht
  obtain ⟨i2, e2⟩ := integral_heatAvg_mul μ (circleMeasure 0 1) ht
  obtain ⟨i3, e3⟩ := integral_heatAvg_mul (circleMeasure 0 1) ν ht
  obtain ⟨i4, e4⟩ := integral_heatAvg_mul (circleMeasure 0 1) (circleMeasure 0 1) ht
  have hpi : Real.sqrt Real.pi * Real.sqrt Real.pi = Real.pi := Real.mul_self_sqrt Real.pi_pos.le
  have e : ∀ y, kappaFun μ (t, y) * kappaFun ν (t, y) = Real.pi *
      (heatAvg μ t y * heatAvg ν t y -
        ν.real univ * (heatAvg μ t y * heatAvg (circleMeasure 0 1) t y) -
        μ.real univ * (heatAvg (circleMeasure 0 1) t y * heatAvg ν t y) +
        μ.real univ * ν.real univ *
          (heatAvg (circleMeasure 0 1) t y * heatAvg (circleMeasure 0 1) t y)) := by
    intro y
    rw [kappaFun_of_pos μ (q := (t, y)) ht, kappaFun_of_pos ν (q := (t, y)) ht]
    simp only
    linear_combination ((heatAvg μ t y - μ.real univ * heatAvg (circleMeasure 0 1) t y) *
      (heatAvg ν t y - ν.real univ * heatAvg (circleMeasure 0 1) t y)) * hpi
  have j1 : Integrable (fun y => heatAvg μ t y * heatAvg ν t y -
      ν.real univ * (heatAvg μ t y * heatAvg (circleMeasure 0 1) t y)) :=
    i1.sub (i2.const_mul _)
  have j2 : Integrable (fun y => heatAvg μ t y * heatAvg ν t y -
      ν.real univ * (heatAvg μ t y * heatAvg (circleMeasure 0 1) t y) -
      μ.real univ * (heatAvg (circleMeasure 0 1) t y * heatAvg ν t y)) :=
    j1.sub (i3.const_mul _)
  have j3 : Integrable (fun y => μ.real univ * ν.real univ *
      (heatAvg (circleMeasure 0 1) t y * heatAvg (circleMeasure 0 1) t y)) := i4.const_mul _
  simp_rw [e]
  refine ⟨(j2.add j3).const_mul _, ?_⟩
  rw [integral_const_mul, integral_add j2 j3, integral_sub j1 (i3.const_mul _),
    integral_sub i1 (i2.const_mul _), integral_const_mul, integral_const_mul, integral_const_mul,
    e1, e2, e3, e4]
  rfl

/-- `κ_μ ∈ L²(ℝ × ℂ)` for regular `μ`. -/
theorem memLp_kappaFun {μ : Measure ℂ} (hμ : IsRegular μ) :
    MemLp (kappaFun μ) 2 (volume : Measure (ℝ × ℂ)) := by
  have := hμ.1
  have hm := measurable_kappaFun μ
  rw [memLp_two_iff_integrable_sq hm.aestronglyMeasurable]
  rw [show (volume : Measure (ℝ × ℂ)) = volume.prod volume from rfl,
    integrable_prod_iff (hm.pow_const 2).aestronglyMeasurable]
  refine ⟨Eventually.of_forall fun t => ?_, ?_⟩
  · rcases le_or_gt t 0 with ht | ht
    · simp only [kappaFun_of_nonpos μ (q := (t, _)) ht]
      simp
    · simpa only [sq] using (integral_kappaFun_mul_slice μ μ ht).1
  · have e : (fun t => ∫ y, ‖kappaFun μ (t, y) ^ 2‖) = (Ioi (0 : ℝ)).indicator (framePsi μ μ) := by
      funext t
      rcases le_or_gt t 0 with ht | ht
      · rw [indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from not_lt.mpr ht)]
        simp only [kappaFun_of_nonpos μ (q := (t, _)) ht]
        simp
      · rw [indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht),
          ← (integral_kappaFun_mul_slice μ μ ht).2]
        congr 1; funext y
        rw [Real.norm_of_nonneg (sq_nonneg _), sq]
    rw [e, integrable_indicator_iff measurableSet_Ioi]
    exact integrableOn_framePsi hμ hμ

/-- The `L²` class of `κ_μ`. -/
def kappaL2 (μ : Measure ℂ) (hμ : IsRegular μ) : WNSpace := (memLp_kappaFun hμ).toLp _

lemma coeFn_kappaL2 {μ : Measure ℂ} (hμ : IsRegular μ) :
    (kappaL2 μ hμ : ℝ × ℂ → ℝ) =ᵐ[volume] kappaFun μ :=
  MemLp.coeFn_toLp _

lemma inner_kappaL2_eq {μ : Measure ℂ} (hμ : IsRegular μ) (g : WNSpace) :
    ⟪kappaL2 μ hμ, g⟫ = ∫ q, kappaFun μ q * (g : ℝ × ℂ → ℝ) q := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [coeFn_kappaL2 hμ] with q h1
  rw [h1, real_inner_eq_re_inner, RCLike.inner_apply]
  simp [mul_comm]

/-- **The covariance of the white-noise transforms** (blueprint `lem:kappa`):
`⟪κ_μ, κ_ν⟫ = energy μ ν`. -/
theorem inner_kappaL2 {μ ν : Measure ℂ} (hμ : IsRegular μ) (hν : IsRegular ν) :
    ⟪kappaL2 μ hμ, kappaL2 ν hν⟫ = energy μ ν := by
  have := hμ.1
  have := hν.1
  rw [inner_kappaL2_eq]
  have e : ∫ q, kappaFun μ q * (kappaL2 ν hν : ℝ × ℂ → ℝ) q = ∫ q, kappaFun μ q * kappaFun ν q := by
    refine integral_congr_ae ?_
    filter_upwards [coeFn_kappaL2 hν] with q h
    rw [h]
  rw [e]
  have hint : Integrable (fun q => kappaFun μ q * kappaFun ν q) (volume.prod volume) :=
    (memLp_kappaFun hμ).integrable_mul (memLp_kappaFun hν)
  rw [show (volume : Measure (ℝ × ℂ)) = volume.prod volume from rfl, integral_prod _ hint]
  have e2 : (fun t => ∫ y, kappaFun μ (t, y) * kappaFun ν (t, y)) =
      (Ioi (0 : ℝ)).indicator (framePsi μ ν) := by
    funext t
    rcases le_or_gt t 0 with ht | ht
    · rw [indicator_of_notMem (show t ∉ Ioi (0 : ℝ) from not_lt.mpr ht)]
      simp only [kappaFun_of_nonpos μ (q := (t, _)) ht, zero_mul, integral_zero]
    · rw [indicator_of_mem (show t ∈ Ioi (0 : ℝ) from ht), (integral_kappaFun_mul_slice μ ν ht).2]
  rw [e2, integral_indicator measurableSet_Ioi, integral_framePsi hμ hν]

/-! ## The frame functions against regular measures -/

/-- Fubini for `frameFun0` against a finite measure. -/
theorem integral_frameFun0 {g : WNSpace} (hg : IsNiceWN g) (α : Measure ℂ) [IsFiniteMeasure α] :
    Integrable (fun q => (∫ u, kerPt u q ∂α) * (g : ℝ × ℂ → ℝ) q) ∧
      ∫ u, frameFun0 g u ∂α = ∫ q, (∫ u, kerPt u q ∂α) * (g : ℝ × ℂ → ℝ) q := by
  obtain ⟨C, hC0, hC⟩ := hg.exists_bound_kerPt_mul
  set F : ℂ × (ℝ × ℂ) → ℝ := fun p => kerPt p.1 p.2 * (g : ℝ × ℂ → ℝ) p.2 with hF
  have hFm : AEStronglyMeasurable F (α.prod volume) :=
    measurable_kerPt₂.aestronglyMeasurable.mul (Lp.aestronglyMeasurable g).comp_snd
  have hFi : Integrable F (α.prod volume) := by
    rw [integrable_prod_iff hFm]
    refine ⟨Eventually.of_forall fun u => hg.integrable_kerPt_mul u, ?_⟩
    refine Integrable.mono' (integrable_const (C * ∫ q, |(g : ℝ × ℂ → ℝ) q|))
      hFm.norm.integral_prod_right' (Eventually.of_forall fun u => ?_)
    rw [Real.norm_of_nonneg (integral_nonneg fun _ => norm_nonneg _), ← integral_const_mul]
    exact integral_mono_ae (hg.integrable_kerPt_mul u).norm (hg.integrable.abs.const_mul C)
      ((hC u).mono fun q hq => by
        show ‖kerPt u q * (g : ℝ × ℂ → ℝ) q‖ ≤ C * |(g : ℝ × ℂ → ℝ) q|
        rwa [Real.norm_eq_abs])
  have e : ∀ q, (∫ u, kerPt u q ∂α) * (g : ℝ × ℂ → ℝ) q = ∫ u, F (u, q) ∂α := fun q => by
    rw [← integral_mul_const]
  refine ⟨?_, ?_⟩
  · simp_rw [e]
    exact hFi.integral_prod_right
  · simp_rw [e]
    exact integral_integral_swap (f := fun u q => F (u, q)) hFi

/-- **The frame functions against regular measures** (blueprint `lem:frame-props`):
`∫ frameFunN g dμ = ⟪κ_μ, g⟫`. -/
theorem integral_frameFunN_eq_inner {g : WNSpace} (hg : IsNiceWN g) {μ : Measure ℂ}
    (hμ : IsRegular μ) : ∫ u, frameFunN g u ∂μ = ⟪kappaL2 μ hμ, g⟫ := by
  have := hμ.1
  obtain ⟨C, hC⟩ := exists_bound_frameFun0 hg
  have hc := continuous_frameFun0 hg
  have hi : Integrable (frameFun0 g) μ :=
    Integrable.of_bound hc.aestronglyMeasurable C (Eventually.of_forall fun u => by
      rw [Real.norm_eq_abs]; exact hC u)
  obtain ⟨iμ, eμ⟩ := integral_frameFun0 hg μ
  obtain ⟨iσ, eσ⟩ := integral_frameFun0 hg (circleMeasure 0 1)
  have havg : Real.circleAverage (frameFun0 g) 0 1 =
      ∫ u, frameFun0 g u ∂(circleMeasure 0 1) :=
    (integral_circleMeasure 0 1 hc.aestronglyMeasurable).symm
  unfold frameFunN
  rw [integral_sub hi (integrable_const _), integral_const, smul_eq_mul, havg, eμ, eσ,
    inner_kappaL2_eq, ← integral_const_mul, ← integral_sub iμ (iσ.const_mul _)]
  congr 1; funext q
  unfold kappaFun
  ring

end WNFrame
end GaussianLQG
