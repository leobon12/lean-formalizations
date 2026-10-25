-- FROZEN_ANCHOR_PREFIX_BEGIN
import SupercriticalLQGUniqueness.Implementation.Exists_strongLQGMetric_lfppLimit

/-! Batch-2 frozen anchor (author-approved 2026-10-24, ruling A24). One declaration: `exists_strongLQGMetric_lfppLimit`. Its proof body is the registered DRAFT_SORRY placeholder until the two-key seal. -/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal Distributions
open LQGMetric (DistC DistOn TestC restrictTo ofCont addFun addConst IsWholePlaneGFF IsGFFPlusCont
  IsGFFPlusBddCont IsPiecewiseC1Path lfppLen)

namespace SupercriticalLQGUniqueness


/-- DG Theorem 1.8, first sentence (l. 476): for each `ξ > 0` there is one (strong) LQG metric
`D` with parameter `ξ` such that, whenever `h` is a whole-plane GFF plus a bounded continuous
function, the re-scaled LFPP metrics `𝔞_ε⁻¹ D^ε_h` of Theorem 1.3 converge in probability to
`D_h`, i.e. the limiting metric of Theorem 1.3 is a.s. `D_h`. The one map `D` precedes every
normalizer family, field law, sample and heat version. `Q` is characterized by DG (1.5) (A9);
`𝔞_ε` by `IsLFPPNormalizer` (pinned by `existsUnique_isLFPPNormalizer`). -/
theorem exists_strongLQGMetric_lfppLimit :
    ∀ ξ : Set.Ioi (0 : ℝ), ∀ Q : ℝ, IsLFPPExponent ξ Q →
      ∃ D : DistC → LSCMetric, IsStrongLQGMetric ξ Q D ∧
        ∀ m : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ), (∀ ε, IsLFPPNormalizer ξ ε (m ε)) →
        ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
          (h : Ω → DistC), IsGFFPlusBddCont h P →
          ∀ X : Set.Ioi (0 : ℝ) → Ω → C(ℂ, ℝ), (∀ ε, IsHeatSmoothing P h ε (X ε)) →
            LSCTendstoInProbability P (fun ε ω => rescaledLFPP (ξ : ℝ) (m ε) (X ε ω))
              (fun ω => (D (h ω)).toLSCFun.1) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact SupercriticalLQGUniqueness.Implementation.exists_strongLQGMetric_lfppLimit_impl
-- FROZEN_ANCHOR_PROOF_END

-- FROZEN_ANCHOR_SUFFIX_BEGIN
end SupercriticalLQGUniqueness
-- FROZEN_ANCHOR_SUFFIX_END
