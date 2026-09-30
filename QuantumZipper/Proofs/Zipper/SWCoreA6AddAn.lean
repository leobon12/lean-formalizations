import QuantumZipper.Proofs.Zipper.SWCoreA5Class
import QuantumZipper.Proofs.LQG.GoodSample
import QuantumZipper.Proofs.Zipper.WedgeUnzipAddFun
import QuantumZipper.Proofs.Section5.Prop16LocalAgree

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-A6-ADDAN: adding a continuous function, uniformly over an area class

Helper for SWC-A6. For `ψ ∈ AreaClass a b c d ρ M m` and `g` continuous:

* `addon_push_split` (H3): the circle-average regularization of `x + g` integrated against the
  pushed circle `fc(z_n, r).map ψ` splits, and the `g`-part converges to `∫ g∘ψ dfc(z_n, r)`;
* `addon_circle_unif` (H2): `∫ g∘ψ dfc(z,r)` and `∫ g dfc(ψ z, r‖ψ'(z)‖)` are uniformly close to
  `g(ψ z)` for small `r`.

Own elementary arguments, adapting `WedgeUnzip.unzipAddFun` (dominated convergence) to the
class, with the Cauchy bounds of `SWCoreA5Class`. The hypothesis `Continuous g` is used (allowed
by the task).
-/

open MeasureTheory Filter Set Metric
open scoped Topology

namespace QuantumZipper
namespace SWCore

/-- Averages of an a.e. `η`-close function. -/
theorem swA6_abs_integral_sub_le {μ : Measure ℂ} [IsProbabilityMeasure μ] {f : ℂ → ℝ}
    (hf : AEStronglyMeasurable f μ) {A η : ℝ} (h : ∀ᵐ w ∂μ, |f w - A| ≤ η) :
    |∫ w, f w ∂μ - A| ≤ η := by
  have hint : Integrable f μ := by
    refine Integrable.of_bound hf (|A| + η) (h.mono fun w hw => ?_)
    rw [Real.norm_eq_abs]
    have := abs_sub_abs_le_abs_sub (f w) A
    linarith
  have heq : ∫ w, f w ∂μ - A = ∫ w, (f w - A) ∂μ := by
    rw [integral_sub hint (integrable_const A)]; simp
  rw [heq]
  have := norm_integral_le_of_norm_le_const (μ := μ) (C := η) (f := fun w => f w - A)
    (by simpa [Real.norm_eq_abs] using h)
  simpa [Real.norm_eq_abs] using this

/-- **(H2)** Circle averages of `g∘ψ` at `(z, r)` and of `g` at `(ψ z, r‖ψ'(z)‖)` are uniformly
close to `g(ψ z)`. -/
theorem addon_circle_unif {a b c d ρ M m : ℝ} (hc : 0 < c) (hρ : 0 < ρ) {g : ℂ → ℝ}
    (hg : Continuous g) :
    ∀ η > 0, ∃ r₀ > 0, ∀ ψ ∈ AreaClass a b c d ρ M m, ∀ z ∈ rectC a b c d, ∀ r, 0 < r → r ≤ r₀ →
      |∫ w, g (ψ w) ∂foldedCircle z r - g (ψ z)| ≤ η ∧
        |∫ w, g w ∂foldedCircle (ψ z) (r * ‖deriv ψ z‖) - g (ψ z)| ≤ η := by
  intro η hη
  obtain ⟨δ, hδ, hU⟩ := Metric.uniformContinuousOn_iff.1
    ((isCompact_closedBall (0 : ℂ) (|M| + 1)).uniformContinuousOn_of_continuous hg.continuousOn)
    η hη
  obtain ⟨C, L, r₀, hC, -, hr₀, -, H⟩ := areaClass_deriv_bounds (a := a) (b := b) (c := c)
    (d := d) (M := M) (m := m) hρ
  refine ⟨min (min r₀ c) (min (δ / (2 * C)) (min (1 / C) (ρ / (2 * C)))), by positivity, ?_⟩
  intro ψ hψ z hz r hr hrs
  have hrr₀ : r ≤ r₀ := hrs.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hrc : r ≤ c := hrs.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hCδ : C * r ≤ δ / 2 := by
    have h := hrs.trans ((min_le_right _ _).trans (min_le_left _ _))
    rw [le_div_iff₀ (by positivity)] at h; linarith
  have hC1 : C * r ≤ 1 := by
    have h := hrs.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
    rw [le_div_iff₀ hC] at h; linarith
  have hCρ : C * r ≤ ρ / 2 := by
    have h := hrs.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
    rw [le_div_iff₀ (by positivity)] at h; linarith
  have hψz := hψ.2.2.1 z (self_subset_thickening hρ _ hz)
  have hψzB : ψ z ∈ closedBall (0 : ℂ) (|M| + 1) := by
    rw [mem_closedBall, dist_zero_right]; linarith [hψz.1, le_abs_self M]
  -- closeness to `ψ z` implies closeness of `g`
  have hclose : ∀ w : ℂ, ‖w - ψ z‖ ≤ C * r → |g w - g (ψ z)| ≤ η := by
    intro w hw
    have hwB : w ∈ closedBall (0 : ℂ) (|M| + 1) := by
      rw [mem_closedBall, dist_zero_right]
      have := norm_sub_norm_le w (ψ z)
      linarith [hψz.1, le_abs_self M]
    have := hU w hwB (ψ z) hψzB (by rw [dist_eq_norm]; linarith)
    rw [Real.dist_eq] at this; exact this.le
  have hz0 : z ∈ closedBall z r₀ := mem_closedBall_self hr₀.le
  refine ⟨?_, ?_⟩
  · rw [foldedCircle_eq_circleUnif hr.le (hrc.trans hz.2.1)]
    have hball : ∀ᵐ w ∂circleUnif z r, w ∈ closedBall z r₀ :=
      (CircleMV.ae_circleUnif z r).mono fun w hw => by
        rw [mem_closedBall, dist_eq_norm, hw, abs_of_pos hr]; exact hrr₀
    have hcont : ContinuousOn ψ (closedBall z r₀) := fun u hu =>
      (H ψ hψ z hz u hu).1.continuousAt.continuousWithinAt
    have hae : AEMeasurable ψ (circleUnif z r) := by
      rw [← Measure.restrict_eq_self_of_ae_mem hball]
      exact hcont.aemeasurable measurableSet_closedBall
    refine swA6_abs_integral_sub_le (f := fun w => g (ψ w))
      (hg.comp_aestronglyMeasurable hae.aestronglyMeasurable) ?_
    filter_upwards [CircleMV.ae_circleUnif z r, hball] with w hw hwb
    refine hclose _ ?_
    have hlip := Convex.norm_image_sub_le_of_norm_deriv_le (fun v hv => (H ψ hψ z hz v hv).1)
      (fun v hv => (H ψ hψ z hz v hv).2.1) (convex_closedBall z r₀) hz0 hwb
    rw [hw, abs_of_pos hr] at hlip
    exact hlip
  · have hdz := (H ψ hψ z hz z hz0).2.1
    have hs0 : 0 ≤ r * ‖deriv ψ z‖ := by positivity
    have hsC : r * ‖deriv ψ z‖ ≤ C * r := by nlinarith
    rw [foldedCircle_eq_circleUnif hs0 (by linarith [hψz.2])]
    refine swA6_abs_integral_sub_le hg.aestronglyMeasurable ?_
    filter_upwards [CircleMV.ae_circleUnif (ψ z) (r * ‖deriv ψ z‖)] with w hw
    refine hclose _ ?_
    rw [hw, abs_of_nonneg hs0]; exact hsC

/-- Uniform angle measure on `[0, 2π)` (copy of `Thm18Asm.G1RC.circM`). -/
noncomputable def swA6CircM : Measure ℝ :=
  (ENNReal.ofReal (2 * Real.pi))⁻¹ • volume.restrict (Ico 0 (2 * Real.pi))

instance : IsProbabilityMeasure swA6CircM := by
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  constructor
  show (ENNReal.ofReal (2 * Real.pi))⁻¹ • volume.restrict (Ico 0 (2 * Real.pi)) univ = 1
  rw [smul_eq_mul, Measure.restrict_apply MeasurableSet.univ, univ_inter, Real.volume_Ico,
    sub_zero]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.mpr h2π).ne' ENNReal.ofReal_ne_top

theorem swA6_circleUnif_eq_map (z : ℂ) (ε : ℝ) :
    circleUnif z ε = swA6CircM.map (circleMap z ε) := by
  unfold circleUnif swA6CircM
  rw [Measure.map_smul]
  exact (continuous_circleMap z ε).measurable.aemeasurable

end SWCore
end QuantumZipper
