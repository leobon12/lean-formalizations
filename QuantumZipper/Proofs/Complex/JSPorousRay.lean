import QuantumZipper.Proofs.Complex.JSCharts
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Complex.Convex

/-!
# JSPOROUSRAY: vertical rays, the open image `F '' ℍ`, and the qh integrand

Four analytic preliminaries behind the quasihyperbolic length of the vertical rays
`x + i[y,1]` of EXT-JS (`blueprint/EXT_JS_BLUEPRINT.md`, node D3) and the D6 boundary step:

* `JS.norm_image_sub_le_integral_norm_deriv_ray`: the fundamental theorem of calculus along a
  vertical segment, in the form needed to estimate `‖F z - F w‖` by an integral of `‖F'‖`;
* `JS.isOpen_image_H`: `F '' ℍ` is **open** for `F` holomorphic and injective on `ℍ` (the open
  mapping theorem);
* `JS.infDist_compl_image_pos`: the quasihyperbolic denominator `dist (F z, (F '' ℍ)ᶜ)` is
  positive at every `z ∈ ℍ` whenever `(F '' ℍ)ᶜ` is nonempty;
* `JS.continuousOn_qhIntegrand`: the quasihyperbolic integrand
  `t ↦ ‖F'(x + t i)‖ / dist (F(x + t i), (F '' ℍ)ᶜ)` is continuous on `[y,1]`, `y > 0`.

## Sources

* FTC along a vertical segment (Lemma 1) is elementary and standard: the derivative of the
  complex-analytic function `t ↦ F(x + t i)` is `F'(x + t i) · i` (chain rule) and
  `‖∫_a^b g‖ ≤ ∫_a^b ‖g‖`; see e.g. Ahlfors, *Complex Analysis*, 3rd ed., Ch. 4. **Own elementary
  proof, standard** (mathlib: `intervalIntegral.integral_eq_sub_of_hasDerivAt`,
  `intervalIntegral.norm_integral_le_integral_norm`).
* Lemma 2 is the open mapping theorem on the connected open set `ℍ`
  (`AnalyticOnNhd.is_constant_or_isOpen`, `Mathlib.Analysis.Complex.OpenMapping`; Ahlfors,
  *Complex Analysis*, Ch. 5, Thm 8), with the constant case excluded by injectivity.
* Lemma 3 is `IsClosed.notMem_iff_infDist_pos` applied to the closed set `(F '' ℍ)ᶜ`.
* Lemma 4 assembles Lemma 3 with the continuity of `deriv F` on the open set `ℍ`
  (`AnalyticOnNhd.deriv`, an analytic function has analytic — hence continuous — derivative).
-/

noncomputable section

open Set Metric MeasureTheory

namespace QuantumZipper
namespace JS

/-- **FTC along a vertical ray.** For `F` holomorphic on `ℍ` and `0 < a ≤ b`, the increment of
`F` along the vertical segment from `x + a i` to `x + b i` is bounded by the integral of `‖F'‖`
along that segment:

`‖F (x + b i) - F (x + a i)‖ ≤ ∫_a^b ‖F' (x + t i)‖ dt`.

Own elementary proof, standard (chain rule + FTC + `‖∫ g‖ ≤ ∫ ‖g‖`); Ahlfors, *Complex Analysis*,
3rd ed., Ch. 4. -/
lemma norm_image_sub_le_integral_norm_deriv_ray {F : ℂ → ℂ} (hd : DifferentiableOn ℂ F H)
    {x a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ‖F ((x : ℂ) + (b : ℂ) * Complex.I) - F ((x : ℂ) + (a : ℂ) * Complex.I)‖
      ≤ ∫ t in a..b, ‖deriv F ((x : ℂ) + (t : ℂ) * Complex.I)‖ := by
  set ray : ℝ → ℂ := fun t => (x : ℂ) + (t : ℂ) * Complex.I with hraydef
  -- the vertical ray `t ↦ x + t i` is differentiable with derivative `i`
  have hray : ∀ t : ℝ, HasDerivAt ray Complex.I t := by
    intro t
    have h := ((hasDerivAt_id t).ofReal_comp.mul_const Complex.I).const_add (x : ℂ)
    simpa [hraydef] using h
  -- the composite is differentiable with derivative `F'·i` on `[a,b]`
  have hstep : ∀ t ∈ uIcc a b, HasDerivAt (fun s : ℝ => F (ray s))
      (deriv F (ray t) * Complex.I) t := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    have ht0 : 0 < t := lt_of_lt_of_le ha ht.1
    have him : (ray t).im = t := by simp [hraydef]
    have hzH : ray t ∈ H := by
      show 0 < (ray t).im
      rw [him]
      exact ht0
    have hFd : HasDerivAt F (deriv F (ray t)) (ray t) :=
      (hd.differentiableAt (isOpen_H.mem_nhds hzH)).hasDerivAt
    exact hFd.comp t (hray t)
  -- continuity of the derivative on the closed segment gives integrability
  have hint : IntervalIntegrable (fun t : ℝ => deriv F (ray t) * Complex.I) volume a b := by
    refine ContinuousOn.intervalIntegrable_of_Icc hab ?_
    have hderivc : ContinuousOn (deriv F) H := (hd.analyticOnNhd isOpen_H).deriv.continuousOn
    have hraycont : ContinuousOn ray (Icc a b) := by
      have hcont : Continuous ray := by
        rw [hraydef]
        exact continuous_const.add
          ((Complex.continuous_ofReal.comp continuous_id).mul_const Complex.I)
      exact hcont.continuousOn
    have hmap : MapsTo ray (Icc a b) H := by
      intro t ht
      have him : (ray t).im = t := by simp [hraydef]
      show 0 < (ray t).im
      rw [him]
      exact lt_of_lt_of_le ha ht.1
    exact (hderivc.comp hraycont hmap).mul continuousOn_const
  have hftc : ∫ t in a..b, deriv F (ray t) * Complex.I = F (ray b) - F (ray a) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hstep hint
  have hmain : ‖F (ray b) - F (ray a)‖ ≤ ∫ t in a..b, ‖deriv F (ray t)‖ := by
    calc ‖F (ray b) - F (ray a)‖
        = ‖∫ t in a..b, deriv F (ray t) * Complex.I‖ := by rw [hftc]
      _ ≤ ∫ t in a..b, ‖deriv F (ray t) * Complex.I‖ :=
          intervalIntegral.norm_integral_le_integral_norm hab
      _ = ∫ t in a..b, ‖deriv F (ray t)‖ := by
          refine intervalIntegral.integral_congr fun t _ => ?_
          rw [norm_mul, Complex.norm_I, mul_one]
  simpa only [hraydef] using hmain

/-- **`F '' ℍ` is open.** If `F` is holomorphic on `ℍ` and injective there, its image of `ℍ` is
open.

This is the open mapping theorem (`AnalyticOnNhd.is_constant_or_isOpen` applied to the connected
open set `ℍ`, `Mathlib.Analysis.Complex.OpenMapping`; Ahlfors, *Complex Analysis*, Ch. 5 Thm 8):
the constant case is excluded because `F` is injective on `ℍ`, which contains the two distinct
points `i` and `1 + i`. -/
lemma isOpen_image_H {F : ℂ → ℂ} (hd : DifferentiableOn ℂ F H) (hinj : InjOn F H) :
    IsOpen (F '' H) := by
  have hnotconst : ¬ ∃ w, ∀ z ∈ H, F z = w := by
    rintro ⟨w, hw⟩
    have hI : Complex.I ∈ H := by simp [H]
    have h1I : (1 + Complex.I) ∈ H := by
      show 0 < (1 + Complex.I).im
      rw [Complex.add_im]
      simp
    have heq : Complex.I = 1 + Complex.I :=
      hinj hI h1I (by rw [hw Complex.I hI, hw (1 + Complex.I) h1I])
    have h01 : (0 : ℂ) = 1 := by
      have h := congrArg (fun u : ℂ => u - Complex.I) heq
      simp only [sub_self, add_sub_cancel_right] at h
      exact h
    norm_num at h01
  exact ((hd.analyticOnNhd isOpen_H).is_constant_or_isOpen
    (convex_halfSpace_im_gt 0).isPreconnected).resolve_left hnotconst H (subset_refl H) isOpen_H

/-- **The quasihyperbolic denominator is positive.** If `F` is holomorphic and injective on `ℍ`
and `(F '' ℍ)ᶜ` is nonempty, then `dist (F z, (F '' ℍ)ᶜ) > 0` for every `z ∈ ℍ`: the complement,
being the complement of the open set `F '' ℍ`, is closed and does not contain `F z`. -/
lemma infDist_compl_image_pos {F : ℂ → ℂ} (hd : DifferentiableOn ℂ F H) (hinj : InjOn F H)
    (hne : ((F '' H)ᶜ).Nonempty) {z : ℂ} (hz : z ∈ H) :
    0 < Metric.infDist (F z) (F '' H)ᶜ := by
  have hclosed : IsClosed ((F '' H)ᶜ) := (isOpen_image_H hd hinj).isClosed_compl
  rw [← hclosed.notMem_iff_infDist_pos hne]
  exact fun hc => hc ⟨z, hz, rfl⟩

/-- **Continuity of the quasihyperbolic integrand.** For `F` holomorphic and injective on `ℍ`
with `(F '' ℍ)ᶜ` nonempty, the integrand

`t ↦ ‖F'(x + t i)‖ / dist (F(x + t i), (F '' ℍ)ᶜ)`

is continuous on the compact segment `[y,1]`, `y > 0` (the denominator never vanishes there by
`infDist_compl_image_pos`, and `deriv F` is continuous on the open set `ℍ`). -/
lemma continuousOn_qhIntegrand {F : ℂ → ℂ} (hd : DifferentiableOn ℂ F H) (hinj : InjOn F H)
    (hne : ((F '' H)ᶜ).Nonempty) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    ContinuousOn (fun t : ℝ => ‖deriv F ((x : ℂ) + (t : ℂ) * Complex.I)‖
      / Metric.infDist (F ((x : ℂ) + (t : ℂ) * Complex.I)) (F '' H)ᶜ) (Icc y 1) := by
  set ray : ℝ → ℂ := fun t => (x : ℂ) + (t : ℂ) * Complex.I with hraydef
  have hraycont : ContinuousOn ray (Icc y 1) := by
    have hcont : Continuous ray := by
      rw [hraydef]
      exact continuous_const.add
        ((Complex.continuous_ofReal.comp continuous_id).mul_const Complex.I)
    exact hcont.continuousOn
  have hmap : MapsTo ray (Icc y 1) H := by
    intro t ht
    have him : (ray t).im = t := by simp [hraydef]
    show 0 < (ray t).im
    rw [him]
    exact lt_of_lt_of_le hy ht.1
  have hderivc : ContinuousOn (deriv F) H := (hd.analyticOnNhd isOpen_H).deriv.continuousOn
  have hnum : ContinuousOn (fun t : ℝ => ‖deriv F (ray t)‖) (Icc y 1) :=
    continuous_norm.comp_continuousOn (hderivc.comp hraycont hmap)
  have hden : ContinuousOn (fun t : ℝ => Metric.infDist (F (ray t)) (F '' H)ᶜ) (Icc y 1) :=
    (Metric.continuous_infDist_pt (F '' H)ᶜ).comp_continuousOn
      (hd.continuousOn.comp hraycont hmap)
  have hne0 : ∀ t ∈ Icc y 1, Metric.infDist (F (ray t)) (F '' H)ᶜ ≠ 0 := fun t ht =>
    ne_of_gt (infDist_compl_image_pos hd hinj hne (hmap ht))
  have hfin : ContinuousOn (fun t : ℝ => ‖deriv F (ray t)‖
      / Metric.infDist (F (ray t)) (F '' H)ᶜ) (Icc y 1) := hnum.div hden hne0
  simpa only [hraydef] using hfin

end JS
end QuantumZipper
