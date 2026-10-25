import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal.T51Main
import SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal.Assembly2
import SupercriticalLQGUniqueness.Uniqueness.Objects.RadiusAssembly.Assembly




 












set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped ENNReal
open LQGMetric (DistC IsGFFPlusCont)

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal

 
theorem t58RadiusResidual_proved : Objects.Density.T58RadiusResidual :=
  Objects.Density.t58RadiusResidual_of_budget (t58BudgetResidual_of_t51 t51Statement_holds)

 

theorem weakLQGMetric_unique_proved :
    ∀ ξ : Set.Ioi (0 : ℝ), ∀ Q : ℝ, IsLFPPExponent ξ Q →
      ∀ D D' : DistC → LSCMetric,
        IsWeakLQGMetric ξ Q D → IsWeakLQGMetric ξ Q D' →
        ∃ C : ℝ, 0 < C ∧
          ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
            (h : Ω → DistC), IsGFFPlusCont h P →
            ∀ᵐ ω ∂P, ∀ u v : ℂ,
              (D (h ω)).1 (u, v) = ENNReal.ofReal C * (D' (h ω)).1 (u, v) :=
  Objects.RadiusAssembly.weakLQGMetric_unique_of_radius_residual t58RadiusResidual_proved

end SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal

 





namespace SupercriticalLQGUniqueness.Implementation

open MeasureTheory
open scoped ENNReal
open LQGMetric (DistC IsGFFPlusCont)

 
theorem weakLQGMetric_unique_impl :
    ∀ ξ : Set.Ioi (0 : ℝ), ∀ Q : ℝ, IsLFPPExponent ξ Q →
      ∀ D D' : DistC → LSCMetric,
        IsWeakLQGMetric ξ Q D → IsWeakLQGMetric ξ Q D' →
        ∃ C : ℝ, 0 < C ∧
          ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
            (h : Ω → DistC), IsGFFPlusCont h P →
            ∀ᵐ ω ∂P, ∀ u v : ℂ,
              (D (h ω)).1 (u, v) = ENNReal.ofReal C * (D' (h ω)).1 (u, v) :=
  SupercriticalLQGUniqueness.Uniqueness.Objects.BlockMarginal.weakLQGMetric_unique_proved

end SupercriticalLQGUniqueness.Implementation
