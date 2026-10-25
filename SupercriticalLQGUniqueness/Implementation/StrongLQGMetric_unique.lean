import SupercriticalLQGUniqueness.B2.Strong.WeakOfStrong
import SupercriticalLQGUniqueness.Frozen.WeakLQGMetric_unique

 












set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal Distributions
open LQGMetric (DistC DistOn TestC restrictTo ofCont addFun addConst IsWholePlaneGFF IsGFFPlusCont
  IsGFFPlusBddCont IsPiecewiseC1Path lfppLen)

namespace SupercriticalLQGUniqueness.Implementation

open SupercriticalLQGUniqueness.B2.Strong

 

theorem strongLQGMetric_unique_impl :
    ∀ ξ : Set.Ioi (0 : ℝ), ∀ Q : ℝ, IsLFPPExponent ξ Q →
      ∀ D D' : DistC → LSCMetric,
        IsStrongLQGMetric ξ Q D → IsStrongLQGMetric ξ Q D' →
        ∃ C : ℝ, 0 < C ∧
          ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
            (h : Ω → DistC), IsGFFPlusCont h P →
            ∀ᵐ ω ∂P, ∀ u v : ℂ,
              (D' (h ω)).1 (u, v) = ENNReal.ofReal C * (D (h ω)).1 (u, v) := by
  intro ξ Q hQ D D' hD hD'
  exact weakLQGMetric_unique ξ Q hQ D' D (isWeakLQGMetric_of_isStrongLQGMetric hD')
    (isWeakLQGMetric_of_isStrongLQGMetric hD)

end SupercriticalLQGUniqueness.Implementation
