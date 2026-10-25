-- FROZEN_ANCHOR_PREFIX_BEGIN
import SupercriticalLQGUniqueness.Implementation.Lfpp_tendstoInProbability

/-! Batch-2 frozen anchor (author-approved 2026-10-24, ruling A24). One declaration: `lfpp_tendstoInProbability`. Its proof body is the registered DRAFT_SORRY placeholder until the two-key seal. -/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal Distributions
open LQGMetric (DistC DistOn TestC restrictTo ofCont addFun addConst IsWholePlaneGFF IsGFFPlusCont
  IsGFFPlusBddCont IsPiecewiseC1Path lfppLen)

namespace SupercriticalLQGUniqueness


/-- DG Theorem 1.3 (l. 325–328): let `h` be a whole-plane GFF plus a bounded continuous function
and `ξ > 0`. The re-scaled LFPP metrics `𝔞_ε⁻¹ D^ε_h` converge in probability, with respect to
the topology on lower semicontinuous functions on `ℂ × ℂ` (DG Definition 1.2), to a random
lower semicontinuous metric `D_h` on `ℂ` that may take the value `∞`. The limit is a random
variable on the probability space of `h` (one per field law); it precedes the choice of heat
version. `𝔞_ε` is characterized by `IsLFPPNormalizer` (pinned by
`existsUnique_isLFPPNormalizer`). -/
theorem lfpp_tendstoInProbability :
    ∀ ξ : Set.Ioi (0 : ℝ), ∀ m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ),
      (∀ ε, IsLFPPNormalizer ξ ε (m ε)) →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsGFFPlusBddCont h P →
        ∃ L : Ω → LSCMetric, Measurable L ∧
          ∀ X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ), (∀ ε, IsHeatSmoothing P h ε (X ε)) →
            LSCTendstoInProbability P (fun ε ω => rescaledLFPP (ξ : ℝ) (m ε) (X ε ω))
              (fun ω => (L ω).toLSCFun.1) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact SupercriticalLQGUniqueness.Implementation.lfpp_tendstoInProbability_impl
-- FROZEN_ANCHOR_PROOF_END

-- FROZEN_ANCHOR_SUFFIX_BEGIN
end SupercriticalLQGUniqueness
-- FROZEN_ANCHOR_SUFFIX_END
