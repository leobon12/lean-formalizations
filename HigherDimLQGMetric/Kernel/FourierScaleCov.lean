import HigherDimLQGMetric.Kernel.FourierMeasure

/-!
# Fourier representation of scale covariance

For pairable finite-measure pairs, integrate the fixed-scale spectral identity
over any measurable positive scale set.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory FourierTransform Complex Set
open scoped FourierTransform RealInnerProductSpace ComplexConjugate

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ} {κ : Rd d → ℝ}

theorem scaleCov_eq_fourier (hκ : HigherDimLFPP.IsLFPPKernel κ)
    {S : Set ℝ} (hS : MeasurableSet S) (hS0 : S ⊆ Ioi 0)
    (μ ν μ' ν' : Measure (Rd d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteMeasure μ'] [IsFiniteMeasure ν']
    (hp : HigherDimLFPP.IsPairable κ S μ ν)
    (hp' : HigherDimLFPP.IsPairable κ S μ' ν') :
    ((HigherDimLFPP.scaleCov κ S μ ν μ' ν' : ℝ) : ℂ) =
      ∫ t in S, ∫ ξ : Rd d,
        ((t ^ ((d : ℝ) - 1) *
          ‖𝓕 (fun y : Rd d => (κ y : ℂ)) (t • ξ)‖ ^ 2 : ℝ) : ℂ) *
          (conj (measureFourier μ ξ) - conj (measureFourier ν ξ)) *
          (measureFourier μ' ξ - measureFourier ν' ξ) := by
  rw [HigherDimLFPP.scaleCov_eq_integral hκ hS hS0 hp hp',
    ← integral_complex_ofReal]
  exact setIntegral_congr_fun hS fun t ht => scalePair_eq_fourier hκ (hS0 ht) μ ν μ' ν'

end HigherDimLQGMetric
