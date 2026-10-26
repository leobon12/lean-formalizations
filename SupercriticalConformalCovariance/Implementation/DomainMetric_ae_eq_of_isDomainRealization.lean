import SupercriticalLQGUniqueness.Frozen.IsStrongLQGMetric
import SupercriticalConformalCovariance.Frozen.IsDomainRealization
import SupercriticalConformalCovariance.Frozen.DomainMetric
import SupercriticalConformalCovariance.Domain.AeEq

/-!
Provider module of the frozen anchor `domainMetric_ae_eq_of_isDomainRealization_v1`
(`SupercriticalConformalCovariance.domainMetric_ae_eq_of_isDomainRealization`, frozen anchor
`SupercriticalConformalCovariance.Frozen.DomainMetric_ae_eq_of_isDomainRealization`; ruling A10.2, GMU Remark 1.5).
The statement and the `open` lines are copied verbatim from the frozen file. The proof is
`SupercriticalConformalCovariance.Domain.domainMetric_ae_eq_of_isDomainRealization` (`Domain/AeEq.lean`): GMU Remark 1.5's bump-function argument with coin-mixture universal locality.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory TopologicalSpace Set
open scoped ENNReal
open LQGMetric (DistC DistOn)

namespace SupercriticalConformalCovariance.Implementation

open SupercriticalLQGUniqueness (LSCMetric IsLFPPExponent IsStrongLQGMetric)

/-- Provider of `SupercriticalConformalCovariance.domainMetric_ae_eq_of_isDomainRealization` (realization independence of
the domain metric; ruling A10.2). -/
theorem domainMetric_ae_eq_of_isDomainRealization_impl :
    ∀ ξ : Set.Ioi (0 : ℝ), ∀ Q : ℝ, IsLFPPExponent ξ Q →
      ∀ D : DistC → LSCMetric, IsStrongLQGMetric ξ Q D →
      ∀ V : Opens ℂ,
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistOn V) (h₀ h₀' : Ω → DistC) (f f' : Ω → C(V, ℝ)),
        IsDomainRealization V P h h₀ f → IsDomainRealization V P h h₀' f' →
        ∀ᵐ ω ∂P, domainMetric (ξ : ℝ) D V (h₀ ω) (f ω) = domainMetric (ξ : ℝ) D V (h₀' ω) (f' ω) :=
  SupercriticalConformalCovariance.Domain.domainMetric_ae_eq_of_isDomainRealization

end SupercriticalConformalCovariance.Implementation
