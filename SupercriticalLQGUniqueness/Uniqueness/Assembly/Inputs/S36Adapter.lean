import SupercriticalLQGUniqueness.Uniqueness.Assembly.Inputs.Inputs
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.S36Final




 









set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Assembly.Inputs

open LQGMetric (DistC)

 

def S36E3Input : Prop :=
  ∀ (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ), 0 < Q → ∀ D : DistC → LSCMetric,
    IsWeakLQGMetric ξ Q D → ∀ p : ℝ, 0 < p → ∀ q : Set.Ioo (0 : ℝ) (1 / 100),
    ∃ a₀ : Set.Ioo (1 - (q : ℝ)) 1,
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P → ∀ (z : ℂ) (r : Set.Ioi (0 : ℝ)),
        P {ω | ¬ TwoScale.S36Events.EventClause3 (D (h ω)) z r q a₀} ≤ ENNReal.ofReal p

 
theorem s36Input_of_E3 (hE3 : S36E3Input) : S36Input :=
  ⟨TwoScale.S36.hS36upper_of_E3 hE3, TwoScale.S36.hS36lower_of_E3 hE3⟩

 
theorem s36Input_proved : S36Input :=
  ⟨TwoScale.S36.hS36upper_proved, TwoScale.S36.hS36lower_proved⟩

end SupercriticalLQGUniqueness.Uniqueness.Assembly.Inputs

