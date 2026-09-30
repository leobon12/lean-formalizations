import Mathlib.Analysis.Calculus.BumpFunction.SmoothApprox
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.Topology.MetricSpace.Thickening

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Mollification of a Lipschitz function on `ℂ`

`n2Lip_exists_mollify`: an `L`-Lipschitz function `f : ℂ → ℝ` vanishing off `K` has, for every
`r > 0`, a `C¹` approximation `f'` with `‖Df'‖ ≤ L`, vanishing off `cthickening r K`, and with
`|f' - f| ≤ L r`.

Source: standard mollification (e.g. Evans–Gariepy, *Measure Theory and Fine Properties of
Functions*, §4.2); own elementary Lean proof. We take `f' = φₙ ⋆ f` with `φₙ` the normalized
`ContDiffBump (0 : ℂ)` of outer radius `r`, following the pattern of mathlib's
`MeasureTheory.LocallyIntegrable.exists_contDiff_dist_le_of_forall_mem_ball_dist_le`.
-/

open MeasureTheory Metric Set Filter
open scoped Convolution

noncomputable section

namespace QuantumZipper.D3Plus

theorem n2Lip_exists_mollify {L : NNReal} {f : ℂ → ℝ} (hf : LipschitzWith L f) {K : Set ℂ}
    (hK : ∀ z ∉ K, f z = 0) {r : ℝ} (hr : 0 < r) :
    ∃ f' : ℂ → ℝ, ContDiff ℝ 1 f' ∧ (∀ u, ‖fderiv ℝ f' u‖ ≤ L) ∧
      (∀ z ∉ Metric.cthickening r K, f' z = 0) ∧ ∀ u, |f' u - f u| ≤ L * r := by
  let φ : ContDiffBump (0 : ℂ) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  let ψ : ℂ → ℝ := φ.normed volume
  let f' : ℂ → ℝ := ψ ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] f
  have hfc : Continuous f := hf.continuous
  have hform : ∀ x, f' x = ∫ t, ψ t * f (x - t) := fun x => by
    simp only [f', convolution_lsmul, smul_eq_mul]
  have hint : ∀ x, Integrable (fun t => ψ t * f (x - t)) := fun x =>
    (φ.continuous_normed.mul (hfc.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
      φ.hasCompactSupport_normed.mul_right
  have hlip : LipschitzWith L f' := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.dist_eq, ← Real.norm_eq_abs, hform, hform, ← integral_sub (hint x) (hint y)]
    have hb : ∀ t, ‖ψ t * f (x - t) - ψ t * f (y - t)‖ ≤ ψ t * (L * dist x y) := by
      intro t
      rw [← mul_sub, norm_mul, Real.norm_of_nonneg (φ.nonneg_normed t)]
      refine mul_le_mul_of_nonneg_left ?_ (φ.nonneg_normed t)
      have := hf.dist_le_mul (x - t) (y - t)
      rwa [dist_sub_right, dist_eq_norm] at this
    calc _ ≤ ∫ t, ψ t * (L * dist x y) :=
          norm_integral_le_of_norm_le (φ.integrable_normed.mul_const _) (Eventually.of_forall hb)
      _ = L * dist x y := by rw [integral_mul_const, φ.integral_normed, one_mul]
  refine ⟨f', ?_, fun u => norm_fderiv_le_of_lipschitz ℝ hlip, ?_, ?_⟩
  · exact φ.hasCompactSupport_normed.contDiff_convolution_left _ φ.contDiff_normed
      hfc.locallyIntegrable
  · intro z hz
    rw [hform]
    refine integral_eq_zero_of_ae (Eventually.of_forall fun t => ?_)
    by_cases ht : ψ t = 0
    · simp [ht]
    · have htb : t ∈ ball (0 : ℂ) r := by
        have : t ∈ Function.support ψ := ht
        rwa [φ.support_normed_eq] at this
      have hzt : z - t ∉ K := fun hK' => hz (thickening_subset_cthickening _ _
        (mem_thickening_iff.2 ⟨z - t, hK', by simpa [dist_eq_norm] using htb⟩))
      simp [hK _ hzt]
  · intro u
    rw [← Real.dist_eq]
    refine φ.dist_normed_convolution_le hfc.aestronglyMeasurable fun y hy => ?_
    calc dist (f y) (f u) ≤ L * dist y u := hf.dist_le_mul y u
      _ ≤ L * r := mul_le_mul_of_nonneg_left (le_of_lt hy) L.2

end QuantumZipper.D3Plus

end
