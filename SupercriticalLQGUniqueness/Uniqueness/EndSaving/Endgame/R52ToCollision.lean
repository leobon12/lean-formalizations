import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame.R53Dyadic
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame.R53Collision




 
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame
open LQGMetric (DistC)
open SupercriticalLQGUniqueness.Uniqueness.EndSaving.Interfaces
open SupercriticalLQGUniqueness.Uniqueness.EndSaving.InterfaceV2

theorem r52Dyadic_to_collision {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (D D' : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D')
    (hGFF : IsNormalizedWholePlaneGFF h P)
    (cMinus cPlus : ℝ≥0∞)
    (hMinus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus)
    (hPlus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus)
    (hstrict : cMinus < cPlus)
    (pbar : Set.Ioo (0 : ℝ) 1)
    (objs : ObjectsExistV2 P h D D' ξ Q cMinus cPlus pbar)
    (θ : Set.Ioi (0 : ℝ))
    (hR52 : R52ClosedEndSavingDyadic P h ξ Q D D' hD hD' hGFF
      cMinus cPlus hMinus hPlus hstrict pbar objs)
    (a : Set.Ioo (3 / 4 : ℝ) 1) (κ : Set.Ioi (0 : ℝ))
    (p : Set.Ioo (0 : ℝ) 1) :
    ∃ Ctop : Set.Ioo (0 : ℝ) cPlus.toReal,
      ∀ j : ℕ,
        ENNReal.ofReal (κ : ℝ) ≤
          P (h ⁻¹' OptimalConstants.Ratios.GtildeEvent D D'
            (dyadicRadius j) κ
              ⟨objs.cMid', lt_of_le_of_lt ENNReal.toReal_nonneg
                objs.cMid'_lower⟩) →
        P (h ⁻¹' {g | OptimalConstants.Ratios.HEvent D D' ξ Q (dyadicRadius j) a
          ⟨Ctop, Ctop.property.1⟩ θ g}) <
            ENNReal.ofReal ((p : ℝ) / 2) := by
  exact r53Dyadic_to_collision P h ξ Q D D' hD hD' hGFF
    cMinus cPlus hMinus hPlus hstrict pbar objs θ
    (r53OfClosedR52Dyadic P h ξ Q D D' hD hD' hGFF
      cMinus cPlus hMinus hPlus hstrict pbar objs θ hR52) a κ p

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame
