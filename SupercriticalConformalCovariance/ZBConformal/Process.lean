import SupercriticalConformalCovariance.ZBConformal.PositivePart
import LQGMetric.Field.ZeroBoundaryAffine

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory TopologicalSpace
open SupercriticalConformalCovariance
open LQGMetric

namespace SupercriticalConformalCovariance.ZBConformal

/-- Reindex a test-function process by the conformal transport. -/
def pullProcess {Ω : Type*} {φ : ℂ → ℂ} {U V : Opens ℂ}
    (hφ : IsConformalBijection φ U V) (X : TestOn V → Ω → ℝ) :
    TestOn U → Ω → ℝ := fun ψ ω => X (confPushTest hφ ψ) ω

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {φ : ℂ → ℂ} {U V : Opens ℂ} (hφ : IsConformalBijection φ U V)
  {X : TestOn V → Ω → ℝ} (hX : IsZBGFFProcess V X P)

include hX in
theorem pullProcess_measurable (ψ : TestOn U) :
    Measurable (pullProcess hφ X ψ) := hX.measurable _

include hX in
theorem pullProcess_gaussian :
    IsGaussianProcess (pullProcess hφ X) P :=
  hX.gaussian.comp_right (confPushTest hφ)

include hX in
theorem pullProcess_centered (ψ : TestOn U) :
    ∫ ω, pullProcess hφ X ψ ω ∂P = 0 := hX.centered _

end SupercriticalConformalCovariance.ZBConformal
