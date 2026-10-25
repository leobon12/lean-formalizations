-- FROZEN_ANCHOR_PREFIX_BEGIN
import SupercriticalLQGUniqueness.Implementation.WeakLQGMetric_unique

/-! Scratch freeze split of SLURoots.lean:35. -/
set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped ENNReal
open LQGMetric (DistC IsGFFPlusCont)

namespace SupercriticalLQGUniqueness

/-- DG Theorem 1.13 (l. 596–598), with `Q` characterized by the LFPP
asymptotic of DG l. 330–333. Under A9 this predicate-form root certifies the
literal theorem only together with sealed `existsUnique_isLFPPExponent`, which
identifies the unique `Q` with DG's `Q(ξ)`. -/
theorem weakLQGMetric_unique :
    ∀ ξ : Set.Ioi (0 : ℝ), ∀ Q : ℝ, IsLFPPExponent ξ Q →
      ∀ D D' : DistC → LSCMetric,
        IsWeakLQGMetric ξ Q D → IsWeakLQGMetric ξ Q D' →
        ∃ C : ℝ, 0 < C ∧
          ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
            (h : Ω → DistC), IsGFFPlusCont h P →
            ∀ᵐ ω ∂P, ∀ u v : ℂ,
              (D (h ω)).1 (u, v) = ENNReal.ofReal C * (D' (h ω)).1 (u, v) :=
-- FROZEN_ANCHOR_PROOF_BEGIN
by exact SupercriticalLQGUniqueness.Implementation.weakLQGMetric_unique_impl
-- FROZEN_ANCHOR_PROOF_END
-- FROZEN_ANCHOR_SUFFIX_BEGIN
end SupercriticalLQGUniqueness
-- FROZEN_ANCHOR_SUFFIX_END
