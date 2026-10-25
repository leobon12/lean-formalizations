import SupercriticalLQGUniqueness.Uniqueness.EndSaving.ClosedBallCounting.ClosedBallEndpoints




 
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.ClosedBallCounting
open LQGMetric (DistC)
open SupercriticalLQGUniqueness.Uniqueness.EndSaving.InterfaceV2
open SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame
open SupercriticalLQGUniqueness.Uniqueness.Assembly.Inputs

 
theorem c45_balls_input : Assembly.Inputs.C45BallsInput := by
  intro Ω _ P _ h ξ Q D D' hD hD' hGFF cMinus cPlus hMinus hPlus
    hstrict pbar R params family
  exact c45_balls_at P h ξ Q D D' hD hD' hGFF cMinus cPlus
    hMinus hPlus hstrict pbar R params family

 
theorem selected_endgame_dyadic :
    ∃ pbar : Set.Ioo (0 : ℝ) 1,
      ∀ (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (D D' : DistC → LSCMetric),
        (hD : IsWeakLQGMetric ξ Q D) → (hD' : IsWeakLQGMetric ξ Q D') →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), (hGFF : IsNormalizedWholePlaneGFF h P) →
      ∀ cMinus cPlus : ℝ≥0∞,
        (hMinus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus) →
        (hPlus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus) →
        ∀ hstrict : cMinus < cPlus,
      ∀ objs : ObjectsExistV2 P h D D' ξ Q cMinus cPlus pbar,
        R52ClosedEndSavingDyadic P h ξ Q D D'
          hD hD'
          hGFF cMinus cPlus
          hMinus
          hPlus
          hstrict pbar objs ∧
        ∀ θ : Set.Ioi (0 : ℝ),
          R53OfObjectsDyadic P h ξ Q D D'
            hD hD'
            hGFF cMinus cPlus
            hMinus
            hPlus
            hstrict pbar objs θ := by
  obtain ⟨pbar, hEndgame⟩ := Assembly.Inputs.selected_endgame_dyadic_of_C45Balls
  refine ⟨pbar, ?_⟩
  intro ξ Q D D' hD hD' Ω _ P _ h hGFF cMinus cPlus hMinus hPlus hstrict objs
  exact hEndgame ξ Q D D' hD hD' P h hGFF cMinus cPlus
    hMinus hPlus hstrict objs
    (c45_balls_at P h ξ Q D D' hD hD' hGFF cMinus cPlus
      hMinus hPlus hstrict pbar objs.radii objs.params objs.family)

 
theorem anchor2_of_s36_t58 (hS36 : Assembly.Inputs.S36Input) (hT58 : Assembly.Inputs.T58Input) :
    ∀ ξ : Set.Ioi (0 : ℝ), ∀ Q : ℝ, IsLFPPExponent ξ Q →
      ∀ D D' : DistC → LSCMetric,
        IsWeakLQGMetric ξ Q D → IsWeakLQGMetric ξ Q D' →
        ∃ C : ℝ, 0 < C ∧
          ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
            (h : Ω → DistC), LQGMetric.IsGFFPlusCont h P →
            ∀ᵐ ω ∂P, ∀ u v : ℂ,
              (D (h ω)).1 (u, v) = ENNReal.ofReal C * (D' (h ω)).1 (u, v) := by
  exact Assembly.Inputs.weakLQGMetric_unique_of_inputs_balls hS36 hT58 c45_balls_input

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.ClosedBallCounting
