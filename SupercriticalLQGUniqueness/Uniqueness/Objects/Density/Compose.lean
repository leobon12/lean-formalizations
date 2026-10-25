import SupercriticalLQGUniqueness.Uniqueness.Objects.Density.Centre
import SupercriticalLQGUniqueness.Uniqueness.Assembly.Inputs.T58Adapter
import SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Determinism.HDet




 




















set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Density

open LQGMetric (DistC)

 

theorem optimal_pos_finite {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (D D' : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D')
    (hGFF : IsNormalizedWholePlaneGFF h P) (cMinus cPlus : ℝ≥0∞)
    (hMinus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus)
    (hPlus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus) :
    0 < cMinus ∧ cPlus < ⊤ := by
  have hQ : 0 < Q := EndSaving.InterfaceV2.q_pos_of_weak_metric ξ Q D hD
  obtain ⟨cm, cp, hcm0, -, -, hcpt, hm, hp⟩ := OptimalConstants.Determinism.hDET_proved ξ Q hQ D D' hD hD' P h hGFF
  obtain ⟨ω, ⟨h1, h2⟩, h3, h4⟩ := ((hMinus.and hm).and (hPlus.and hp)).exists
  refine ⟨?_, ?_⟩
  · rw [← h1, h2]; exact hcm0
  · rw [← h3, h4]; exact hcpt

 

theorem t58CentreInputsInput_of_residual (hP36 : P364DyadicInput) (hR : T58RadiusResidual) :
    Assembly.Inputs.T58CentreInputsInput := by
  intro Ω _ P _ h ξ Q D D' hD hD' hGFF cMinus cPlus hMinus hPlus hstrict
  have hQ : 0 < Q := EndSaving.InterfaceV2.q_pos_of_weak_metric ξ Q D hD
  obtain ⟨hcm, hcp⟩ := optimal_pos_finite P h ξ Q D D' hD hD' hGFF cMinus cPlus hMinus hPlus
  exact nonempty_centreT58Inputs_of_inputs P h ξ Q D D' hD hD' hGFF cMinus cPlus hMinus hPlus
    hstrict hQ hcm hcp hP36 hR

 


theorem t58Input_of_residual (hP36 : P364DyadicInput) (hR : T58RadiusResidual) :
    Assembly.Inputs.T58Input :=
  Assembly.Inputs.t58Input_of_centre0_inputs (t58CentreInputsInput_of_residual hP36 hR)

 
theorem t58Input_of_budget_residual (hP36 : P364DyadicInput) (hB : T58BudgetResidual) :
    Assembly.Inputs.T58Input :=
  t58Input_of_residual hP36 (t58RadiusResidual_of_budget hB)

end SupercriticalLQGUniqueness.Uniqueness.Objects.Density
