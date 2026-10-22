import HigherDimLQGMetric.Kernel.FourierScaleCov
import HigherDimLFPP.Field.LogCov

/-!
# Fourier representation of logarithmic covariance

This form retains the scale integral.  It follows from HigherDimLFPP's
all-scale covariance theorem, so no distributional Fourier transform of the
logarithm enters its proof.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory FourierTransform Complex Set
open scoped FourierTransform RealInnerProductSpace ComplexConjugate

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ} {κ : Rd d → ℝ}

theorem logCov_eq_fourier (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (μ ν μ' ν' : Measure (Rd d))
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    [IsFiniteMeasure μ'] [IsFiniteMeasure ν']
    (hmass : μ.real univ = ν.real univ)
    (hmass' : μ'.real univ = ν'.real univ)
    (hlog : HigherDimLFPP.LogPairable μ ν μ' ν') :
    ((HigherDimLFPP.logCov μ ν μ' ν' : ℝ) : ℂ) =
      ∫ t in Ioi (0 : ℝ), ∫ ξ : Rd d,
        ((t ^ ((d : ℝ) - 1) *
          ‖𝓕 (fun y : Rd d => (κ y : ℂ)) (t • ξ)‖ ^ 2 : ℝ) : ℂ) *
          (conj (measureFourier μ ξ) - conj (measureFourier ν ξ)) *
          (measureFourier μ' ξ - measureFourier ν' ξ) := by
  obtain ⟨hp, hp', hcov⟩ := HigherDimLFPP.scaleCov_eq_logCov hκ hmass hmass' hlog
  rw [← hcov]
  exact scaleCov_eq_fourier hκ measurableSet_Ioi (fun _ h => h) μ ν μ' ν' hp hp'

end HigherDimLQGMetric
