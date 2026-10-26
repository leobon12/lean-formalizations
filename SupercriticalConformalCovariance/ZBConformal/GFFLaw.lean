import SupercriticalConformalCovariance.ZBConformal.Process
import SupercriticalConformalCovariance.ZBConformal.Covariance

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory TopologicalSpace
open SupercriticalConformalCovariance
open LQGMetric
open QuantumZipper

namespace SupercriticalConformalCovariance.ZBConformal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {φ : ℂ → ℂ} {U V : Opens ℂ} (hφ : IsConformalBijection φ U V)

/-- Conformal invariance of the zero-boundary GFF process on the same probability space. -/
theorem isZBGFFProcess_pullProcess {X : TestOn V → Ω → ℝ}
    (hX : IsZBGFFProcess V X P) :
    IsZBGFFProcess U (pullProcess hφ X) P where
  measurable := fun ψ => pullProcess_measurable hφ hX ψ
  gaussian := pullProcess_gaussian hφ hX
  centered := fun ψ => pullProcess_centered hφ hX ψ
  covariance_eq := by
    intro ψ χ
    change cov[X (confPushTest hφ ψ), X (confPushTest hφ χ); P] =
      zeroGFFTestCov U ψ χ
    rw [hX.covariance_eq, zeroGFFTestCov_conformal hφ]

/-- A zero-boundary GFF on V pulls back to one on U, with no change of probability space. -/
theorem isZeroBoundaryGFF_distPullback {g : Ω → DistOn V}
    (hg : IsZeroBoundaryGFF V g P) :
    IsZeroBoundaryGFF U (fun ω => distPullback hφ (g ω)) P where
  measurable := (measurable_distPullback hφ).comp hg.measurable
  process := by
    change IsZBGFFProcess U (pullProcess hφ (fun ψ ω => g ω ψ)) P
    exact isZBGFFProcess_pullProcess hφ hg.process

end SupercriticalConformalCovariance.ZBConformal
