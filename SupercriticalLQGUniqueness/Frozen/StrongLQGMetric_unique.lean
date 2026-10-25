-- FROZEN_ANCHOR_PREFIX_BEGIN
import SupercriticalLQGUniqueness.Implementation.StrongLQGMetric_unique

/-! Batch-2 frozen anchor (author-approved 2026-10-24, ruling A24). One declaration: `strongLQGMetric_unique`. Its proof body is the registered DRAFT_SORRY placeholder until the two-key seal. -/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal Distributions
open LQGMetric (DistC DistOn TestC restrictTo ofCont addFun addConst IsWholePlaneGFF IsGFFPlusCont
  IsGFFPlusBddCont IsPiecewiseC1Path lfppLen)

namespace SupercriticalLQGUniqueness


/-- DG Theorem 1.8, second sentence (l. 477): if `D` and `D̃` are two (strong) LQG metrics with
parameter `ξ`, there is a deterministic constant `C > 0` such that a.s. `D̃_h = C D_h` whenever
`h` is a whole-plane GFF plus a continuous function. `Q` is characterized by DG (1.5)
(l. 330–333); as for `weakLQGMetric_unique` (ruling A9), this certifies the literal statement
only together with sealed `existsUnique_isLFPPExponent`. -/
theorem strongLQGMetric_unique :
    ∀ ξ : Set.Ioi (0 : ℝ), ∀ Q : ℝ, IsLFPPExponent ξ Q →
      ∀ D D' : DistC → LSCMetric,
        IsStrongLQGMetric ξ Q D → IsStrongLQGMetric ξ Q D' →
        ∃ C : ℝ, 0 < C ∧
          ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
            (h : Ω → DistC), IsGFFPlusCont h P →
            ∀ᵐ ω ∂P, ∀ u v : ℂ,
              (D' (h ω)).1 (u, v) = ENNReal.ofReal C * (D (h ω)).1 (u, v) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact SupercriticalLQGUniqueness.Implementation.strongLQGMetric_unique_impl
-- FROZEN_ANCHOR_PROOF_END

-- FROZEN_ANCHOR_SUFFIX_BEGIN
end SupercriticalLQGUniqueness
-- FROZEN_ANCHOR_SUFFIX_END
