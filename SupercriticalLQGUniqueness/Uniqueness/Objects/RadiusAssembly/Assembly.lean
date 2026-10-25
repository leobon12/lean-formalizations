import SupercriticalLQGUniqueness.Uniqueness.Objects.Density.Final
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.ClosedBallCounting.C45Endgame
import SupercriticalLQGUniqueness.Uniqueness.Assembly.Inputs.S36Adapter




 








set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.RadiusAssembly

open LQGMetric (DistC IsGFFPlusCont)

 
theorem weakLQGMetric_unique_of_radius_residual (hR : Objects.Density.T58RadiusResidual) :
    ∀ ξ : Set.Ioi (0 : ℝ), ∀ Q : ℝ, IsLFPPExponent ξ Q →
      ∀ D D' : DistC → LSCMetric,
        IsWeakLQGMetric ξ Q D → IsWeakLQGMetric ξ Q D' →
        ∃ C : ℝ, 0 < C ∧
          ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
            (h : Ω → DistC), IsGFFPlusCont h P →
            ∀ᵐ ω ∂P, ∀ u v : ℂ,
              (D (h ω)).1 (u, v) = ENNReal.ofReal C * (D' (h ω)).1 (u, v) :=
  EndSaving.ClosedBallCounting.anchor2_of_s36_t58 Assembly.Inputs.s36Input_proved
    (Objects.Density.t58Input_of_radius_residual hR)

end SupercriticalLQGUniqueness.Uniqueness.Objects.RadiusAssembly
