import HigherDimLQGMetric.Sphere.Cont
import HigherDimLQGMetric.Core.Defs

/-! Recentring the metric normalizer under a continuous coarse field. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Filter Topology
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- Adding a continuous field multiplies the scale normalizer by the
exponential of its spherical mean. -/
theorem amplify_sNorm_addFun {X : DistRd d} {s : ℝ} {w : Rd d} {a : ℝ}
    (hlim : Tendsto (sphereAvgSeq X s w) atTop (𝓝 a))
    (g : C(Rd d, ℝ)) (ξ Q : ℝ) :
    sNorm ξ Q (addFun X g) s w =
      Real.exp (ξ * sphereAvg (ofCont g) s w) * sNorm ξ Q X s w := by
  rw [sNorm, sphereAvg_addFun_of_tendsto hlim, ← sphereAvg_ofCont,
    sNorm, mul_add, Real.exp_add]
  ring

/-- A small oscillation on the trial ball also controls the deviation from
the coarse field's spherical mean. -/
theorem amplify_abs_coarse_sub_sphereMean_le (hd : 1 ≤ d)
    {s δ : ℝ} (hs : 0 < s) (w : Rd d) (g : C(Rd d, ℝ))
    (hosc : ∀ x ∈ Metric.ball w (5 * s), ∀ y ∈ Metric.ball w (5 * s),
      |g x - g y| ≤ δ)
    {x : Rd d} (hx : x ∈ Metric.ball w (5 * s)) :
    |g x - sphereAvg (ofCont g) s w| ≤ δ := by
  have := isProbabilityMeasure_unitSphereProb hd
  have hi : Integrable (fun u : Rd d => g (w + s • u)) (unitSphereProb d) :=
    integrable_unitSphereProb_of_continuous (by fun_prop)
  have hball : ∀ᵐ u ∂(unitSphereProb d), w + s • u ∈ Metric.ball w (5 * s) := by
    filter_upwards [ae_unitSphereProb_norm_eq_one d] with u hu
    change ‖w + s • u - w‖ < 5 * s
    simpa only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
      abs_of_pos hs, hu, mul_one] using (show s < 5 * s by linarith)
  have hbound : ∀ᵐ u ∂(unitSphereProb d), |g x - g (w + s • u)| ≤ δ := by
    filter_upwards [hball] with u hu
    exact hosc x hx _ hu
  have hint := integral_mono_ae ((integrable_const _).sub hi).abs
    (integrable_const δ) hbound
  rw [integral_const, probReal_univ, one_smul] at hint
  rw [sphereAvg_ofCont]
  have hsub : g x - ∫ u, g (w + s • u) ∂(unitSphereProb d) =
      ∫ u, g x - g (w + s • u) ∂(unitSphereProb d) := by
    rw [integral_sub (integrable_const _) hi, integral_const, probReal_univ, one_smul]
  rw [hsub]
  exact (abs_integral_le_integral_abs).trans hint

end HigherDimLQGMetric
