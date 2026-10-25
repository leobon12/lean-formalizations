import SupercriticalLQGUniqueness.Uniqueness.Assembly.Inputs.Inputs
import SupercriticalLQGUniqueness.Uniqueness.Assembly.Root.RootSkeleton
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame.GlobalEndgameAssembly
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.InterfaceV2.SourceAssemblyV2




 


















set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Assembly.Inputs

open LQGMetric (DistC IsGFFPlusCont)

 


theorem hMAIN_of_inputs (hS36 : S36Input) (hT58 : T58Input) (hC45 : C45Input) :
    ∀ (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ), 0 < Q →
      ∀ (D D' : DistC → LSCMetric), IsWeakLQGMetric ξ Q D → IsWeakLQGMetric ξ Q D' →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
      ∀ cMinus cPlus : ℝ≥0∞,
        (∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus) →
        (∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus) →
        cMinus = cPlus := by
  intro ξ Q _ D D' hD hD' Ω _ P _ h hGFF cMinus cPlus hMinus hPlus
  exact EndSaving.Endgame.hMAIN_common_pbar_of_sections hS36.1 hS36.2
    (fun ξ Q _ D D' hD hD' _ _ P _ h hGFF cMinus cPlus hMinus hPlus hstrict pbar =>
      EndSaving.InterfaceV2.T58DataV2.ofObjectsExistV2
        (Classical.choice
          (hT58 P h ξ Q D D' hD hD' hGFF cMinus cPlus hMinus hPlus hstrict pbar)))
    (fun ξ Q _ D D' hD hD' _ _ P _ h hGFF cMinus cPlus hMinus hPlus hstrict pbar objs =>
      hC45 P h ξ Q D D' hD hD' hGFF cMinus cPlus hMinus hPlus hstrict pbar
        objs.radii objs.params objs.family)
    ξ Q D D' hD hD' P h hGFF cMinus cPlus hMinus hPlus

 



theorem weakLQGMetric_unique_of_inputs (hS36 : S36Input) (hT58 : T58Input)
    (hC45 : C45Input) :
    ∀ ξ : Set.Ioi (0 : ℝ), ∀ Q : ℝ, IsLFPPExponent ξ Q →
      ∀ D D' : DistC → LSCMetric,
        IsWeakLQGMetric ξ Q D → IsWeakLQGMetric ξ Q D' →
        ∃ C : ℝ, 0 < C ∧
          ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
            (h : Ω → DistC), IsGFFPlusCont h P →
            ∀ᵐ ω ∂P, ∀ u v : ℂ,
              (D (h ω)).1 (u, v) = ENNReal.ofReal C * (D' (h ω)).1 (u, v) :=
  Assembly.Root.weakLQGMetric_unique_of_main OptimalConstants.Determinism.hDET_proved (hMAIN_of_inputs hS36 hT58 hC45)

end SupercriticalLQGUniqueness.Uniqueness.Assembly.Inputs
