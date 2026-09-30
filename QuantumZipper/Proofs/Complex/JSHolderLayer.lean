import QuantumZipper.Proofs.Complex.KoebeHalfPlane
import QuantumZipper.Proofs.Complex.JSCharts
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Analysis.Complex.Convex
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# EXT-JS: the quasihyperbolic length of vertical rays (D3) and the chart boundary (D6, part)

Blueprint `blueprint/EXT_JS_BLUEPRINT.md` §2(D) steps 1–2 and §5.

* `JS.qhLength_vertical_le` (node D3): for `F` holomorphic and injective on `ℍ`, the
  quasihyperbolic length of the vertical ray `x + i[y,1]` is at most
  `koebeCovConst⁻¹ · log (1/y)`: the weak Koebe inequality `K5a`
  (`CA.Koebe.infDist_compl_image_ge`) bounds the integrand by `c⁻¹/t` pointwise.

* `JS.chart_real_notMem_image` (node D6, the chart-boundary step): a chart `F` for `K` on the
  box `[-2R,2R] × [0,4R]` does not take real points of that box into the image of `ℍ`. This is
  the boundary-correspondence fact behind "a point of the hull cannot be hit from `ℍ`".

## Sources

* The weak Koebe estimate is `CA.Koebe.infDist_compl_image_ge`
  (`Proofs/Complex/KoebeHalfPlane.lean`), itself proved from the square-root trick
  (Burckel, *Classical Analysis in the Complex Plane*, Thm 7.27; Garnett–Marshall,
  *Harmonic Measure*, Cor. I.4.4) — cite, do not reprove.
* The integration of `1/t` on `[y,1]` is `integral_inv_of_pos`
  (`Mathlib.Analysis.SpecialFunctions.Integrals.Basic`).
* `chart_real_notMem_image` is the local form of the boundary correspondence for the image of an
  injective holomorphic map at a boundary point (Pommerenke, *Boundary Behaviour of Conformal
  Maps*, §2.1): the proof here is an **own elementary proof**, using only the open mapping
  theorem (`AnalyticOnNhd.is_constant_or_isOpen`) and continuity on the box; no Carathéodory
  extension theory is needed for this node.
-/

noncomputable section

open Set Metric Filter MeasureTheory
open scoped Topology Real

namespace QuantumZipper
namespace JS

/-- **D3, pointwise form.** Weak Koebe along a vertical ray: for `t > 0`,

`‖F'(x + t i)‖ / dist (F(x + t i), F '' ℍᶜ) ≤ koebeCovConst⁻¹ * t⁻¹`.

Since `ball (x + t i) t ⊆ ℍ` (`t > 0`), `CA.Koebe.infDist_compl_image_ge` (K5a, weak Koebe)
gives `koebeCovConst * t * ‖F'(x + t i)‖ ≤ dist (F(x + t i), (F '' ℍ)ᶜ)`; if the distance
vanishes the quotient is `0` (`div_zero`), otherwise divide. -/
theorem norm_deriv_div_infDist_le {F : ℂ → ℂ} (hd : DifferentiableOn ℂ F H)
    (hinj : InjOn F H) {x t : ℝ} (ht : 0 < t) :
    ‖deriv F (x + t * Complex.I)‖ / Metric.infDist (F (x + t * Complex.I)) (F '' H)ᶜ
      ≤ (CA.Koebe.koebeCovConst)⁻¹ * t⁻¹ := by
  set z : ℂ := x + t * Complex.I with hz
  have hzim : z.im = t := by simp [hz]
  have hzH : z ∈ H := show 0 < z.im from hzim.symm ▸ ht
  have hk := CA.Koebe.infDist_compl_image_ge hd hinj hzH
  rw [hzim] at hk
  rcases eq_or_lt_of_le (Metric.infDist_nonneg : (0 : ℝ) ≤ Metric.infDist (F z) (F '' H)ᶜ)
    with h0 | hpos
  · rw [← h0, div_zero]
    exact mul_nonneg (inv_nonneg.2 CA.Koebe.koebeCovConst_pos.le) (inv_nonneg.2 ht.le)
  · rw [div_le_iff₀ hpos]
    have hct : 0 < CA.Koebe.koebeCovConst * t := mul_pos CA.Koebe.koebeCovConst_pos ht
    have h1 : (CA.Koebe.koebeCovConst * t)⁻¹ * (CA.Koebe.koebeCovConst * t * ‖deriv F z‖)
        ≤ (CA.Koebe.koebeCovConst * t)⁻¹ * Metric.infDist (F z) (F '' H)ᶜ :=
      mul_le_mul_of_nonneg_left hk (inv_nonneg.2 hct.le)
    rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hct), one_mul] at h1
    have h2 : (CA.Koebe.koebeCovConst * t)⁻¹ = (CA.Koebe.koebeCovConst)⁻¹ * t⁻¹ := by
      rw [mul_inv_rev, mul_comm]
    rwa [h2] at h1

/-- **D3 (EXT-JS §2(D) step 1, §5 table).** The quasihyperbolic length of the vertical ray
`x + i[y,1]` (measured in the image domain `F '' ℍ`) is at most `koebeCovConst⁻¹ * log (1/y)`:

`∫_y^1 ‖F'(x + t i)‖ / dist (F(x + t i), (F '' ℍ)ᶜ) dt ≤ koebeCovConst⁻¹ * log (1/y)`.

The pointwise bound `norm_deriv_div_infDist_le` gives `c⁻¹ * t⁻¹` on `[y,1]`; `∫_y^1 t⁻¹ dt =
log (1/y)`. If the integrand is not interval integrable the integral is `0 ≤` the right-hand
side, so both cases are covered. -/
theorem qhLength_vertical_le {F : ℂ → ℂ} (hd : DifferentiableOn ℂ F H) (hinj : Set.InjOn F H)
    (x : ℝ) {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) :
    ∫ t in y..1, ‖deriv F (x + t * Complex.I)‖ / Metric.infDist (F (x + t * Complex.I)) (F '' H)ᶜ
      ≤ (CA.Koebe.koebeCovConst)⁻¹ * Real.log (1 / y) := by
  have hpt : ∀ t ∈ Icc y 1,
      ‖deriv F (x + t * Complex.I)‖ / Metric.infDist (F (x + t * Complex.I)) (F '' H)ᶜ
        ≤ (CA.Koebe.koebeCovConst)⁻¹ * t⁻¹ :=
    fun t ht => norm_deriv_div_infDist_le hd hinj (lt_of_lt_of_le hy ht.1)
  have hintg : IntervalIntegrable (fun t : ℝ => (CA.Koebe.koebeCovConst)⁻¹ * t⁻¹) volume y 1 := by
    refine ContinuousOn.intervalIntegrable_of_Icc hy1 fun t ht => ?_
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le hy ht.1)
    exact (continuous_const.continuousAt.mul (continuousAt_id.inv₀ ht0)).continuousWithinAt
  by_cases hint : IntervalIntegrable
      (fun t : ℝ => ‖deriv F (x + t * Complex.I)‖
        / Metric.infDist (F (x + t * Complex.I)) (F '' H)ᶜ) volume y 1
  · calc ∫ t in y..1, ‖deriv F (x + t * Complex.I)‖
          / Metric.infDist (F (x + t * Complex.I)) (F '' H)ᶜ
        ≤ ∫ t in y..1, (CA.Koebe.koebeCovConst)⁻¹ * t⁻¹ :=
          intervalIntegral.integral_mono_on hy1 hint hintg hpt
      _ = (CA.Koebe.koebeCovConst)⁻¹ * ∫ t in y..1, t⁻¹ := by
          rw [intervalIntegral.integral_const_mul]
      _ = (CA.Koebe.koebeCovConst)⁻¹ * Real.log (1 / y) := by
          rw [integral_inv_of_pos hy (by norm_num)]
  · rw [intervalIntegral.integral_undef hint]
    refine mul_nonneg (inv_nonneg.2 CA.Koebe.koebeCovConst_pos.le) ?_
    apply Real.log_nonneg
    rw [le_div_iff₀ hy]
    linarith

/-- **D6 (chart boundary), the real-segment step.** A chart `F` for `K` on the box
`[-2R,2R] ×ℂ [0,4R]` maps no real point of that box into the image of the upper half-plane:
`F x ∉ F '' ℍ` for `x ∈ [-2R,2R]`.

Own elementary proof. If `F x = F z` with `z ∈ ℍ`, choose `ε = Im z / 2`, so that
`closedBall z ε ⊆ ℍ`. `F` is injective on `ℍ`, hence nonconstant there, so the open mapping
theorem makes `F '' ball z ε` a neighbourhood of `F z = F x`; by continuity of `F` at the box
point `x`, for every small `t > 0` the value `F (x + t i)` lies in `F '' ball z ε`, so by
injectivity `x + t i ∈ ball z ε`; letting `t → 0` gives `x ∈ closedBall z ε ⊆ ℍ`, i.e.
`0 < Im x = 0`, a contradiction. -/
theorem chart_real_notMem_image {K : Set ℂ} {R : ℝ} {F : ℂ → ℂ} (hF : IsChart K R F) {x : ℝ}
    (hx : x ∈ Set.Icc (-2 * R) (2 * R)) : F x ∉ F '' H := by
  rintro ⟨z, hzH, hzx⟩
  have hzx' : F z = F (x : ℂ) := hzx
  have hzim : 0 < z.im := hzH
  set ε : ℝ := z.im / 2 with hε
  have hεpos : 0 < ε := by rw [hε]; linarith
  -- disks of radius `ε` around `z` stay in `ℍ`
  have hsmall : ∀ {w : ℂ}, dist w z ≤ ε → w ∈ H := by
    intro w hw
    rw [Complex.dist_eq] at hw
    have h1 : |w.im - z.im| ≤ ‖w - z‖ := by
      simpa using Complex.abs_im_le_norm (w - z)
    have h2 : |w.im - z.im| ≤ ε := h1.trans hw
    show 0 < w.im
    have h3 := (abs_le.1 h2).1
    rw [hε] at h3
    linarith
  -- `F` is not constant on `ℍ`
  have hnotconst : ¬ ∃ w, ∀ u ∈ H, F u = w := by
    rintro ⟨w, hw⟩
    have hI : Complex.I ∈ H := by simp [H]
    have h1I : (1 + Complex.I) ∈ H := by
      show 0 < (1 + Complex.I).im
      rw [Complex.add_im]
      simp
    have heq : Complex.I = 1 + Complex.I :=
      hF.inj hI h1I (by rw [hw Complex.I hI, hw (1 + Complex.I) h1I])
    have h01 : (0 : ℂ) = 1 := by
      have h := congrArg (fun u : ℂ => u - Complex.I) heq
      simp only [sub_self, add_sub_cancel_right] at h
      exact h
    norm_num at h01
  have hanal : AnalyticOnNhd ℂ F H := hF.holo.analyticOnNhd isOpen_H
  have hopen : ∀ s ⊆ H, IsOpen s → IsOpen (F '' s) :=
    (hanal.is_constant_or_isOpen (convex_halfSpace_im_gt 0).isPreconnected).resolve_left hnotconst
  have hballH : ball z ε ⊆ H := fun w hw => hsmall (le_of_lt (mem_ball.1 hw))
  have himg_open : IsOpen (F '' ball z ε) := hopen _ hballH isOpen_ball
  have hmem : F (x : ℂ) ∈ F '' ball z ε := ⟨z, mem_ball_self hεpos, hzx'⟩
  obtain ⟨δ₁, hδ₁pos, hδ₁sub⟩ := Metric.mem_nhds_iff.1 (himg_open.mem_nhds hmem)
  -- continuity of `F` at the box point `x`
  have hxbox : (x : ℂ) ∈ Icc (-2 * R) (2 * R) ×ℂ Icc 0 (4 * R) := by
    rw [Complex.mem_reProdIm]
    refine ⟨?_, ?_⟩
    · simpa using hx
    · rw [Complex.ofReal_im]
      exact ⟨le_refl 0, by linarith [hF.pos]⟩
  have hcwa := hF.cont.continuousWithinAt hxbox
  have hev : ∀ᶠ w in 𝓝 (x : ℂ),
      w ∈ Icc (-2 * R) (2 * R) ×ℂ Icc 0 (4 * R) → F w ∈ ball (F (x : ℂ)) δ₁ := by
    have h := hcwa.eventually (ball_mem_nhds (F (x : ℂ)) hδ₁pos)
    rwa [eventually_nhdsWithin_iff] at h
  obtain ⟨η, hηpos, hη⟩ := Metric.eventually_nhds_iff.1 hev
  set δ₀ : ℝ := min (η / 2) R with hδ₀
  have hδ₀pos : 0 < δ₀ := lt_min (by linarith) hF.pos
  have hδ₀η : δ₀ < η := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδ₀R : δ₀ ≤ R := min_le_right _ _
  -- distance from the real point `x` to a nearby vertical point
  have hdist_aux : ∀ t : ℝ, 0 < t →
      dist (x : ℂ) ((x : ℂ) + (t : ℂ) * Complex.I) = t := by
    intro t ht
    rw [Complex.dist_eq]
    have hsub : (x : ℂ) - ((x : ℂ) + (t : ℂ) * Complex.I) = -((t : ℂ) * Complex.I) := by
      ring
    rw [hsub, norm_neg, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos ht]
  -- every small positive `t` gives a point of the ball around `z`
  have hstep : ∀ t : ℝ, 0 < t → t ≤ δ₀ → (x : ℂ) + (t : ℂ) * Complex.I ∈ ball z ε := by
    intro t ht0 htδ
    have htη : t < η := lt_of_le_of_lt htδ hδ₀η
    have ht4R : t ≤ 4 * R := by linarith [hδ₀R, hF.pos]
    set w : ℂ := (x : ℂ) + (t : ℂ) * Complex.I with hw
    have hwre : w.re = x := by simp [hw]
    have hwim : w.im = t := by simp [hw]
    have hwbox : w ∈ Icc (-2 * R) (2 * R) ×ℂ Icc 0 (4 * R) := by
      rw [Complex.mem_reProdIm]
      exact ⟨by simpa [hwre] using hx, by rw [hwim]; exact ⟨le_of_lt ht0, ht4R⟩⟩
    have hdist : dist w (x : ℂ) < η := by
      rw [hw, dist_comm, hdist_aux t ht0]
      exact htη
    have hwH : w ∈ H := show 0 < w.im from hwim.symm ▸ ht0
    obtain ⟨u, hu, hFu⟩ := hδ₁sub (hη hdist hwbox)
    have huw : u = w := hF.inj (hballH hu) hwH hFu
    rwa [huw] at hu
  -- letting `t → 0` puts the real point `x` in `closedBall z ε ⊆ ℍ`
  have hxcl : (x : ℂ) ∈ closedBall z ε := by
    rw [← closure_ball z hεpos.ne']
    refine Metric.mem_closure_iff.2 fun δ hδ => ?_
    have ht0 : 0 < min δ₀ δ / 2 := half_pos (lt_min hδ₀pos hδ)
    have htδ₀ : min δ₀ δ / 2 ≤ δ₀ :=
      (half_le_self (le_min hδ₀pos.le hδ.le)).trans (min_le_left δ₀ δ)
    refine ⟨(x : ℂ) + (((min δ₀ δ / 2 : ℝ)) : ℂ) * Complex.I, hstep _ ht0 htδ₀, ?_⟩
    rw [hdist_aux _ ht0]
    calc min δ₀ δ / 2 ≤ δ / 2 := div_le_div_of_nonneg_right (min_le_right δ₀ δ) (by norm_num)
      _ < δ := div_lt_self hδ (by norm_num)
  have hxH : 0 < (x : ℂ).im := hsmall (mem_closedBall.1 hxcl)
  exact absurd hxH (by simp)

end JS
end QuantumZipper
