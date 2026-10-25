import SupercriticalLQGUniqueness.Uniqueness.Assembly.Inputs.Inputs
import SupercriticalLQGUniqueness.Uniqueness.Objects.Producer.T58c




 









set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Assembly.Inputs

open LQGMetric (DistC)

 

def T58InputsInput : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (D D' : DistC → LSCMetric),
    IsWeakLQGMetric ξ Q D → IsWeakLQGMetric ξ Q D' →
    IsNormalizedWholePlaneGFF h P → ∀ cMinus cPlus : ℝ≥0∞,
    (∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus) →
    (∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus) →
    cMinus < cPlus →
    ∀ pbar : Set.Ioo (0 : ℝ) 1, Nonempty (Objects.Producer.T58Inputs P h D D' ξ Q cMinus cPlus pbar)

 
theorem t58Input_of_inputs (hIn : T58InputsInput) : T58Input :=
  fun P _ h ξ Q D D' hD hD' hGFF cMinus cPlus hMinus hPlus hstrict =>
    Objects.Producer.t58_of_inputs P h ξ Q D D' hD hD' hGFF cMinus cPlus hMinus hPlus hstrict
      (hIn P h ξ Q D D' hD hD' hGFF cMinus cPlus hMinus hPlus hstrict)

 

def T58CentreInputsInput : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (D D' : DistC → LSCMetric),
    IsWeakLQGMetric ξ Q D → IsWeakLQGMetric ξ Q D' →
    IsNormalizedWholePlaneGFF h P → ∀ cMinus cPlus : ℝ≥0∞,
    (∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus) →
    (∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus) →
    cMinus < cPlus →
    ∀ pbar : Set.Ioo (0 : ℝ) 1, Nonempty (Objects.Producer.CentreT58Inputs P h D D' ξ Q cMinus cPlus pbar)

 

theorem t58Input_of_centre0_inputs (hIn : T58CentreInputsInput) : T58Input :=
  fun P _ h ξ Q D D' hD hD' hGFF cMinus cPlus hMinus hPlus hstrict =>
    Objects.Producer.t58_of_centre0_inputs P h ξ Q D D' hD hD' hGFF cMinus cPlus hMinus hPlus hstrict
      (hIn P h ξ Q D D' hD hD' hGFF cMinus cPlus hMinus hPlus hstrict)

end SupercriticalLQGUniqueness.Uniqueness.Assembly.Inputs

