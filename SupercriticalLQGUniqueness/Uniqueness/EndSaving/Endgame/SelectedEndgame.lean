import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame.R52Dyadic
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame.R53Dyadic
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame.R52ToCollision




 
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame
open LQGMetric (DistC)
open SupercriticalLQGUniqueness.Uniqueness.EndSaving.Interfaces
open SupercriticalLQGUniqueness.Uniqueness.EndSaving.InterfaceV2

 

theorem selected_endgame_dyadic_of_C45 :
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
        C45CorrectedNonemptyInternal P h ξ Q D D' hD
          hD' hGFF
          cMinus cPlus hMinus
          hPlus
          hstrict pbar objs.radii objs.params objs.family →
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
  obtain ⟨pbar, hExtra⟩ := EndSaving.MainExtraV2.lemMainExtraV2
  refine ⟨pbar, ?_⟩
  intro ξ Q D D' hD hD' Ω _ P _ h hGFF cMinus cPlus hMinus hPlus hstrict objs hC45
  have hExtraHere := hExtra ξ Q D D' hD hD' P h hGFF cMinus cPlus
    hMinus hPlus hstrict objs
  have hR52 := r52ClosedDyadic_of_extra_and_C45 P h ξ Q D D' hD hD' hGFF
    cMinus cPlus hMinus hPlus hstrict pbar objs hExtraHere hC45
  exact ⟨hR52, fun θ => r53OfClosedR52Dyadic P h ξ Q D D' hD hD' hGFF
    cMinus cPlus hMinus hPlus hstrict pbar objs θ hR52⟩

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame
