import QuantumZipper.Statements.Prop16Literal
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Analysis.Normed.Module.Convex

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Non-vacuity of the chart hypotheses of the literal Proposition 1.6

For the model domain `D = halfDiscLit` (the open upper half-disc) we construct an explicit
measurable family of charts `ψ x : ℍ → D − x`, `x ∈ (-1, 1)`, satisfying `IsLitChart`.

**Source.** Own elementary construction, via the standard Cayley-type map
`z ↦ (1 + z)/(1 - z)` (unit disc → right half-plane; upper half-disc → open first quadrant),
followed by squaring (first quadrant → ℍ); see e.g. Ahlfors, *Complex Analysis*, Ch. 3 §3.4
(elementary conformal mappings). Riemann mapping is not in mathlib, so the charts are written
down explicitly: with `c = (1+x)/(1-x)`, `q = c²`,
`ψ x w = g((w + q)^{1/2}) - x`, `g s = (s - 1)/(s + 1)`, `r₀ x = q`.
-/

namespace QuantumZipper
namespace Prop16LitCert

open Complex Set

/-- The open upper half-disc. -/
def halfDiscLit : Set ℂ := {z | ‖z‖ < 1 ∧ 0 < z.im}

/-- The Cayley parameter `c(x) = (1 + x)/(1 - x)`. -/
noncomputable def cayC (x : ℝ) : ℝ := (1 + x) / (1 - x)

/-- The Möbius map `g s = (s - 1)/(s + 1)`. -/
noncomputable def gMob (s : ℂ) : ℂ := (s - 1) / (s + 1)

/-- The chart radius `q(x) = c(x)²`. -/
noncomputable def chartQ (x : ℝ) : ℝ := cayC x ^ 2

/-- The chart `ψ x w = g((w + q)^{1/2}) - x`. -/
noncomputable def chart (x : ℝ) (w : ℂ) : ℂ :=
  gMob ((w + (chartQ x : ℂ)) ^ (2⁻¹ : ℂ)) - x

lemma sqrt_sq_eq (v : ℂ) : (v ^ (2⁻¹ : ℂ)) ^ 2 = v := by
  simp

lemma sqrt_add_one_ne (v : ℂ) : v ^ (2⁻¹ : ℂ) + 1 ≠ 0 := by
  intro h
  have hs : v ^ (2⁻¹ : ℂ) = -1 := eq_neg_of_add_eq_zero_left h
  have hv : v = 1 := by
    have := sqrt_sq_eq v
    rw [hs] at this
    rw [← this]; norm_num
  rw [hv, one_cpow] at hs
  norm_num at hs

lemma gMob_inj {s t : ℂ} (hs : s + 1 ≠ 0) (ht : t + 1 ≠ 0) (h : gMob s = gMob t) : s = t := by
  unfold gMob at h
  rw [div_eq_div_iff hs ht] at h
  linear_combination h / 2

lemma chart_injective (x : ℝ) : Function.Injective (chart x) := by
  intro w₁ w₂ h
  unfold chart at h
  have h1 := gMob_inj (sqrt_add_one_ne _) (sqrt_add_one_ne _) (sub_left_inj.mp h)
  have h2 : w₁ + (chartQ x : ℂ) = w₂ + (chartQ x : ℂ) := by
    rw [← sqrt_sq_eq (w₁ + _), ← sqrt_sq_eq (w₂ + _), h1]
  exact add_right_cancel h2

lemma re_sqrt_pos {v : ℂ} (hv : v ∈ slitPlane) : 0 < (v ^ (2⁻¹ : ℂ)).re := by
  have hv0 : v ≠ 0 := slitPlane_ne_zero hv
  rw [cpow_def_of_ne_zero hv0, exp_re]
  apply mul_pos (Real.exp_pos _)
  apply Real.cos_pos_of_mem_Ioo
  have h1 := neg_pi_lt_arg v
  have h2 : arg v < Real.pi := lt_of_le_of_ne (arg_le_pi v) (mem_slitPlane_iff_arg.1 hv).1
  have him : (log v * 2⁻¹).im = arg v / 2 := by
    simp [Complex.mul_im, log_im]
    ring
  rw [him]
  constructor <;> linarith

lemma sqrt_mem_Q1 {v : ℂ} (hv : 0 < v.im) :
    0 < (v ^ (2⁻¹ : ℂ)).re ∧ 0 < (v ^ (2⁻¹ : ℂ)).im := by
  have hre := re_sqrt_pos (mem_slitPlane_iff.2 (Or.inr hv.ne'))
  refine ⟨hre, ?_⟩
  have hv' := hv
  rw [← sqrt_sq_eq v] at hv'
  simp only [sq, mul_im] at hv'
  by_contra hneg
  push Not at hneg
  nlinarith [mul_nonpos_of_nonneg_of_nonpos hre.le hneg]

lemma gMob_mem_halfDisc {s : ℂ} (h1 : 0 < s.re) (h2 : 0 < s.im) : gMob s ∈ halfDiscLit := by
  have hs1 : s + 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hn : 0 < normSq (s + 1) := normSq_pos.2 hs1
  refine ⟨?_, ?_⟩
  · unfold gMob
    rw [norm_div, div_lt_one (norm_pos_iff.2 hs1)]
    apply lt_of_pow_lt_pow_left₀ 2 (norm_nonneg _)
    rw [Complex.sq_norm, Complex.sq_norm, normSq_apply, normSq_apply]
    simp
    nlinarith
  · unfold gMob
    rw [Complex.div_im, ← sub_div]
    apply div_pos _ hn
    simp
    nlinarith

lemma cayC_pos {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) : 0 < cayC x := by
  unfold cayC
  exact div_pos (by linarith [hx.1]) (by linarith [hx.2])

lemma sqrt_chartQ {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    ((chartQ x : ℂ)) ^ (2⁻¹ : ℂ) = (cayC x : ℂ) := by
  unfold chartQ
  push_cast
  exact sq_cpow_two_inv (by simpa using cayC_pos hx)

lemma gMob_cayC {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) : gMob (cayC x : ℂ) = (x : ℂ) := by
  have h : (1 : ℝ) - x ≠ 0 := by linarith [hx.2]
  have hr : (cayC x - 1) / (cayC x + 1) = x := by
    unfold cayC
    rw [div_sub_one h, div_add_one h, div_div_div_cancel_right₀ h]
    have : 1 + x + (1 - x) = 2 := by ring
    rw [this]
    ring
  have : gMob (cayC x : ℂ) = (((cayC x - 1) / (cayC x + 1) : ℝ) : ℂ) := by
    unfold gMob
    push_cast
    ring
  rw [this, hr]

lemma chart_zero {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) : chart x 0 = 0 := by
  unfold chart
  rw [zero_add, sqrt_chartQ hx, gMob_cayC hx, sub_self]

lemma chart_differentiableAt {x : ℝ} {w : ℂ} (hw : w + (chartQ x : ℂ) ∈ slitPlane) :
    DifferentiableAt ℂ (chart x) w := by
  have hs : DifferentiableAt ℂ (fun w : ℂ => (w + (chartQ x : ℂ)) ^ (2⁻¹ : ℂ)) w :=
    (differentiableAt_id.add_const _).cpow_const hw
  have : DifferentiableAt ℂ
      (fun w : ℂ => ((w + (chartQ x : ℂ)) ^ (2⁻¹ : ℂ) - 1) /
        ((w + (chartQ x : ℂ)) ^ (2⁻¹ : ℂ) + 1) - (x : ℂ)) w :=
    ((hs.sub_const 1).div (hs.add_const 1) (sqrt_add_one_ne _)).sub_const _
  exact this

lemma chart_real {x : ℝ} {t : ℝ} (ht : |t| < chartQ x) :
    (chart x t).im = 0 := by
  have hnn : 0 ≤ t + chartQ x := by linarith [neg_abs_le t]
  set r : ℝ := (t + chartQ x) ^ (2⁻¹ : ℝ)
  have hr : ((t : ℂ) + (chartQ x : ℂ)) ^ (2⁻¹ : ℂ) = (r : ℂ) := by
    simp only [r]
    rw [ofReal_cpow hnn]
    push_cast
    ring_nf
  have : chart x t = (((r - 1) / (r + 1) - x : ℝ) : ℂ) := by
    unfold chart gMob
    rw [hr]
    push_cast
    ring
  rw [this, ofReal_im]

lemma chart_hasDerivAt {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    HasDerivAt (chart x) (((1 / ((cayC x + 1) ^ 2 * cayC x)) : ℝ) : ℂ) 0 := by
  have hc := cayC_pos hx
  set c := cayC x with hcdef
  have hq : ((chartQ x : ℝ) : ℂ) = (c : ℂ) ^ 2 := by
    unfold chartQ; push_cast; rfl
  have hslit : (0 : ℂ) + (chartQ x : ℂ) ∈ slitPlane := by
    rw [zero_add, hq, mem_slitPlane_iff]
    left
    simp [sq]
    nlinarith
  have hv : HasDerivAt (fun w : ℂ => w + (chartQ x : ℂ)) 1 0 := (hasDerivAt_id 0).add_const _
  have hs := hv.cpow_const (c := (2⁻¹ : ℂ)) hslit
  have hsv : ((0 : ℂ) + (chartQ x : ℂ)) ^ (2⁻¹ : ℂ) = (c : ℂ) := by
    rw [zero_add]; exact sqrt_chartQ hx
  have hc1 : (c : ℂ) + 1 ≠ 0 := by
    have : ((c + 1 : ℝ) : ℂ) ≠ 0 := ofReal_ne_zero.2 (by linarith)
    simpa using this
  have hg : HasDerivAt gMob ((1 * ((c : ℂ) + 1) - ((c : ℂ) - 1) * 1) / ((c : ℂ) + 1) ^ 2)
      (c : ℂ) := by
    have := ((hasDerivAt_id (c : ℂ)).sub_const 1).div ((hasDerivAt_id (c : ℂ)).add_const 1) hc1
    exact this
  rw [← hsv] at hg
  have hcomp := (hg.comp (0 : ℂ) hs).sub_const (x : ℂ)
  have hfun : (fun w => (gMob ∘ fun w : ℂ => (w + (chartQ x : ℂ)) ^ (2⁻¹ : ℂ)) w - (x : ℂ)) =
      chart x := rfl
  rw [hfun] at hcomp
  refine hcomp.congr_deriv ?_
  have hc0 : (c : ℂ) ≠ 0 := ofReal_ne_zero.2 hc.ne'
  have hq0 : ((chartQ x : ℝ) : ℂ) ≠ 0 := by rw [hq]; exact pow_ne_zero 2 hc0
  rw [hsv, zero_add, cpow_sub _ _ hq0, cpow_one, sqrt_chartQ hx, hq]
  push_cast
  field_simp
  ring

lemma chart_image (x : ℝ) :
    chart x '' H = zoomDomain halfDiscLit x := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    show chart x w + (x : ℂ) ∈ halfDiscLit
    unfold chart
    rw [sub_add_cancel]
    have hw' : 0 < (w + (chartQ x : ℂ)).im := by
      simpa [H] using hw
    exact gMob_mem_halfDisc (sqrt_mem_Q1 hw').1 (sqrt_mem_Q1 hw').2
  · intro hz
    have hy : z + (x : ℂ) ∈ halfDiscLit := hz
    set y := z + (x : ℂ) with hydef
    obtain ⟨hy1, hy2⟩ := hy
    have h1y : (1 : ℂ) - y ≠ 0 := by
      intro h
      have := congrArg Complex.im h
      simp at this
      linarith
    have hN : 0 < normSq (1 - y) := normSq_pos.2 h1y
    have hyn : y.re * y.re + y.im * y.im < 1 := by
      have : ‖y‖ ^ 2 < 1 := by nlinarith [norm_nonneg y]
      rwa [Complex.sq_norm, normSq_apply] at this
    set s := (1 + y) / (1 - y) with hsdef
    have hsre : 0 < s.re := by
      rw [hsdef, Complex.div_re, ← add_div]
      apply div_pos _ hN
      simp
      nlinarith
    have hsim : 0 < s.im := by
      rw [hsdef, Complex.div_im, ← sub_div]
      apply div_pos _ hN
      simp
      nlinarith
    refine ⟨s ^ 2 - (chartQ x : ℂ), ?_, ?_⟩
    · show 0 < (s ^ 2 - (chartQ x : ℂ)).im
      simp [sq]
      nlinarith
    · unfold chart
      rw [sub_add_cancel, sq_cpow_two_inv hsre]
      have e1 : s - 1 = 2 * y / (1 - y) := by rw [hsdef]; field_simp; ring
      have e2 : s + 1 = 2 / (1 - y) := by rw [hsdef]; field_simp; ring
      unfold gMob
      rw [e1, e2, div_div_div_cancel_right₀ h1y, mul_div_cancel_left₀ y two_ne_zero, hydef,
        add_sub_cancel_right]

theorem chart_isLitChart {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) :
    IsLitChart (zoomDomain halfDiscLit x) (chartQ x) (chart x) := by
  have hc := cayC_pos hx
  have hq : 0 < chartQ x := by unfold chartQ; positivity
  have hd := (chart_hasDerivAt hx).deriv
  refine ⟨?_, (chart_injective x).injOn, chart_image x, hq, ?_, (chart_injective x).injOn,
    fun t ht => chart_real ht, chart_zero hx, ?_, ?_⟩
  · intro w hw
    apply DifferentiableAt.differentiableWithinAt
    apply chart_differentiableAt
    rw [mem_slitPlane_iff]
    right
    have : 0 < w.im := hw
    simpa using this.ne'
  · intro w hw
    apply DifferentiableAt.differentiableWithinAt
    apply chart_differentiableAt
    rw [mem_slitPlane_iff]
    left
    have h1 : ‖w‖ < chartQ x := by simpa using hw
    have h2 := abs_re_le_norm w
    simp
    linarith [neg_abs_le w.re]
  · rw [hd, ofReal_im]
  · rw [hd, ofReal_re]
    positivity

lemma measurable_chart : Measurable (fun p : ℝ × ℂ => chart p.1 p.2) := by
  unfold chart gMob chartQ cayC
  fun_prop

lemma measurable_chartQ : Measurable chartQ := by
  unfold chartQ cayC
  fun_prop

theorem exists_litChart_family_halfDisc {a b : ℝ} (ha : -1 ≤ a) (hb : b ≤ 1) :
    ∃ (ψ : ℝ → ℂ → ℂ) (r₀ : ℝ → ℝ), Measurable (fun q : ℝ × ℂ => ψ q.1 q.2) ∧ Measurable r₀ ∧
      ∀ x ∈ Set.Ioo a b, IsLitChart (zoomDomain halfDiscLit x) (r₀ x) (ψ x) :=
  ⟨chart, chartQ, measurable_chart, measurable_chartQ, fun _ hx =>
    chart_isLitChart ⟨lt_of_le_of_lt ha hx.1, lt_of_lt_of_le hx.2 hb⟩⟩

/-- The geometric hypotheses of `theorem1_6_literal` hold for `D = halfDiscLit`, `c = -1`,
`d = 1`. -/
theorem halfDiscLit_geometry :
    IsOpen halfDiscLit ∧ IsConnected halfDiscLit ∧ Bornology.IsBounded halfDiscLit ∧
      halfDiscLit ⊆ H ∧
      frontier halfDiscLit ∩ {z : ℂ | z.im = 0} = realSet (Set.Icc (-1) 1) ∧
      (∀ t ∈ Set.Ioo (-1 : ℝ) 1, ∃ r > 0, Metric.ball (t : ℂ) r ∩ H ⊆ halfDiscLit) := by
  have hopen : IsOpen halfDiscLit :=
    (isOpen_lt continuous_norm continuous_const).inter (isOpen_lt continuous_const continuous_im)
  have heq : halfDiscLit = Metric.ball (0 : ℂ) 1 ∩ {w : ℂ | 0 < w.im} := by
    ext z; simp [halfDiscLit]
  refine ⟨hopen, ?_, ?_, fun z hz => hz.2, ?_, ?_⟩
  · rw [heq]
    refine Convex.isConnected ((convex_ball _ _).inter
      (convex_halfSpace_gt Complex.imLm.isLinear 0)) ⟨I / 2, ?_, ?_⟩
    · norm_num
    · norm_num
  · rw [heq]
    exact Metric.isBounded_ball.subset inter_subset_left
  · have hcl : closure halfDiscLit ⊆ {z : ℂ | ‖z‖ ≤ 1 ∧ 0 ≤ z.im} :=
      closure_minimal (fun z hz => ⟨hz.1.le, hz.2.le⟩)
        ((isClosed_le continuous_norm continuous_const).inter
          (isClosed_le continuous_const continuous_im))
    rw [hopen.frontier_eq]
    ext z
    constructor
    · rintro ⟨⟨hz, -⟩, him⟩
      have him' : z.im = 0 := him
      have h1 := (hcl hz).1
      refine ⟨z.re, ?_, ?_⟩
      · have := abs_re_le_norm z
        exact abs_le.1 (this.trans h1)
      · apply Complex.ext <;> simp [him']
    · rintro ⟨t, ht, rfl⟩
      refine ⟨⟨?_, fun h => by simpa using h.2⟩, by simp⟩
      have ht2 : t * t ≤ 1 := by nlinarith [ht.1, ht.2]
      let f : ℝ → ℂ := fun δ => ((1 - δ) * t : ℝ) + (δ : ℂ) * I
      have hf : Filter.Tendsto f (nhdsWithin 0 (Ioi 0)) (nhds (t : ℂ)) := by
        have hc : Continuous f := by fun_prop
        have := hc.tendsto 0
        simp only [f] at this
        simp only [sub_zero, one_mul, ofReal_zero, zero_mul, add_zero] at this
        exact this.mono_left nhdsWithin_le_nhds
      apply mem_closure_of_tendsto hf
      filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1)] with δ hδ
      obtain ⟨hδ0, hδ1⟩ := hδ
      refine ⟨?_, by simp [f]; exact hδ0⟩
      have hsq : ‖f δ‖ ^ 2 < 1 := by
        rw [Complex.sq_norm, normSq_apply]
        simp [f]
        nlinarith [mul_pos hδ0 hδ0, mul_nonneg (mul_nonneg hδ0.le hδ0.le) (mul_self_nonneg t)]
      nlinarith [norm_nonneg (f δ)]
  · intro t ht
    refine ⟨1 - |t|, by have := abs_lt.2 ⟨ht.1, ht.2⟩; linarith, ?_⟩
    rintro z ⟨hz, hzH⟩
    refine ⟨?_, hzH⟩
    have h1 : ‖z - (t : ℂ)‖ < 1 - |t| := by simpa [dist_eq_norm] using hz
    have h2 : ‖z‖ ≤ ‖z - (t : ℂ)‖ + ‖(t : ℂ)‖ := norm_le_norm_sub_add z _
    have h3 : ‖(t : ℂ)‖ = |t| := by simp
    linarith

end Prop16LitCert
end QuantumZipper
