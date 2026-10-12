import BouRabeeGwynne.PaperObjects
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-! The analytic limiting step in the mesh-only Sobolev argument.

The pinned library's endpoint Sobolev theorem requires C¹ functions. This file
passes that theorem through an actual almost-everywhere smooth approximation.
The tiling-specific construction and derivative estimate are separate obligations.
-/

open scoped ENNReal Topology
open MeasureTheory Filter

namespace BouRabeeGwynne.MeshOnlySobolev

/-- Endpoint Sobolev bounds pass to an almost-everywhere limit by Fatou.
No differentiability of the limiting function is required. -/
theorem sobolev_of_smooth_approximation {d : ℕ} {p : ℝ}
    (hp : Real.HolderConjugate (d : ℝ) p)
    (F : Euc d → ℝ) (g : ℕ → Euc d → ℝ)
    (hg : ∀ n, ContDiff ℝ 1 (g n))
    (hcompact : ∀ n, HasCompactSupport (g n))
    (hlim : ∀ᵐ x ∂volume, Tendsto (fun n => g n x) atTop (𝓝 (F x)))
    (J : ℝ≥0∞) (hderiv : ∀ n, ∫⁻ x, ‖fderiv ℝ (g n) x‖ₑ ∂volume ≤ J) :
    (∫⁻ x, ‖F x‖ₑ ^ p ∂volume) ≤
      lintegralPowLePowLIntegralFDerivConst (volume : Measure (Euc d)) p * J ^ p := by
  have hbound (n : ℕ) : (∫⁻ x, ‖g n x‖ₑ ^ p ∂volume) ≤
      lintegralPowLePowLIntegralFDerivConst (volume : Measure (Euc d)) p * J ^ p := by
    have hp' : Real.HolderConjugate (Module.finrank ℝ (Euc d) : ℝ) p := by
      simpa only [finrank_euclideanSpace_fin] using hp
    exact (lintegral_pow_le_pow_lintegral_fderiv volume (hg n) (hcompact n) hp').trans
      (mul_le_mul_right (ENNReal.rpow_le_rpow (hderiv n) hp.symm.nonneg) _)
  calc
    _ = ∫⁻ x, liminf (fun n => ‖g n x‖ₑ ^ p) atTop ∂volume := by
      apply lintegral_congr_ae
      filter_upwards [hlim] with x hx
      exact (hx.enorm.ennrpow_const p).liminf_eq.symm
    _ ≤ liminf (fun n => ∫⁻ x, ‖g n x‖ₑ ^ p ∂volume) atTop :=
      lintegral_liminf_le fun n =>
        (ENNReal.continuous_rpow_const.comp (hg n).continuous.enorm).measurable
    _ ≤ _ := liminf_le_of_frequently_le' (Eventually.of_forall hbound).frequently

end BouRabeeGwynne.MeshOnlySobolev
