-- FROZEN_ANCHOR_PREFIX_BEGIN
import SupercriticalLQGUniqueness.Frozen.IsStrongLQGMetric
import SupercriticalConformalCovariance.Frozen.IsDomainRealization
import SupercriticalConformalCovariance.Frozen.DomainMetric
import SupercriticalConformalCovariance.Implementation.DomainMetric_ae_eq_of_isDomainRealization

/-! Frozen anchor (ruling A15, author-delegated approval of 2026-10-25 of revision 2.2: planning/candidates/rev2.2/APPROVAL-REQUEST.md, sha256 cbc72606…, commit bb67bbe3c). One declaration: `domainMetric_ae_eq_of_isDomainRealization`. Statement unchanged from the candidate `CandDomainMetricAeEq.lean` (sha256 a967423a6555c965…); its proof body is the manifest-registered DRAFT_SORRY placeholder until the two-key seal (provider `SupercriticalConformalCovariance.Implementation.DomainMetric_ae_eq_of_isDomainRealization`). -/

set_option autoImplicit false

noncomputable section

open MeasureTheory TopologicalSpace Set
open scoped ENNReal
open LQGMetric (DistC DistOn)

namespace SupercriticalConformalCovariance

open SupercriticalLQGUniqueness (LSCMetric IsLFPPExponent IsStrongLQGMetric)

/-- **The domain metric does not depend on the realization** (ruling A10.2; GMU arXiv:1905.00383v3
Remark 1.5, `source/literature/gm-uniqueness/tex/uniqueness-final.tex` l. 360–374: "It is easily seen from
Axioms II (locality) and III (Weyl scaling) that `D_{h̊^U}` is a measurable function of `h̊^U`", by the
bump-function argument; Gwynne–Miller 1905.00384v2 l. 316–319; paper l. 23, "in the local sense in which
the canonical metric is defined", and Lemma 7.1, l. 519–538). For a (strong) LQG metric `D` with
parameter `ξ` (DG Definition 1.7, `Q = Q(ξ)`), an open set `V`, and two realizations `(h₀, f)`, `(h₀', f')`
of the same random distribution `h` on `V` on one probability space, almost surely the two domain metrics
`e^{ξ f} · D_{h₀}(·, ·; V)` and `e^{ξ f'} · D_{h₀'}(·, ·; V)` agree at every pair of points of `V` (values
`+∞` included). Thus `domainMetric` is, almost surely, a function of the field `h` alone. -/
theorem domainMetric_ae_eq_of_isDomainRealization :
    ∀ ξ : Set.Ioi (0 : ℝ), ∀ Q : ℝ, IsLFPPExponent ξ Q →
      ∀ D : DistC → LSCMetric, IsStrongLQGMetric ξ Q D →
      ∀ V : Opens ℂ,
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistOn V) (h₀ h₀' : Ω → DistC) (f f' : Ω → C(V, ℝ)),
        IsDomainRealization V P h h₀ f → IsDomainRealization V P h h₀' f' →
        ∀ᵐ ω ∂P, domainMetric (ξ : ℝ) D V (h₀ ω) (f ω) = domainMetric (ξ : ℝ) D V (h₀' ω) (f' ω) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact SupercriticalConformalCovariance.Implementation.domainMetric_ae_eq_of_isDomainRealization_impl
-- FROZEN_ANCHOR_PROOF_END

-- FROZEN_ANCHOR_SUFFIX_BEGIN
end SupercriticalConformalCovariance
-- FROZEN_ANCHOR_SUFFIX_END
