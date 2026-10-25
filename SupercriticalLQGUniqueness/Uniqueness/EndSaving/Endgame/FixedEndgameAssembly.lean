import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame.SelectedEndgame
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame.CommonTheta
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame.R53Collision




 
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame
open LQGMetric (DistC)
open SupercriticalLQGUniqueness.Uniqueness.EndSaving.Interfaces
open SupercriticalLQGUniqueness.Uniqueness.EndSaving.InterfaceV2

theorem hMAIN_fixed_from_selected_endgame_C45 {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (D D' : DistC → LSCMetric) (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D')
    (hGFF : IsNormalizedWholePlaneGFF h P)
    (cMinus cPlus : ℝ≥0∞) (hPlusPos : 0 < cPlus)
    (hMinus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus)
    (hPlus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus)
    (hS36upper : ∃ θ : Set.Ioi (0 : ℝ),
      ∃ a : Set.Ioo (3 / 4 : ℝ) 1,
      ∃ p : Set.Ioo (0 : ℝ) 1,
        ∀ Ctop : Set.Ioo (0 : ℝ) cPlus.toReal,
          ∃ n₁ : ℕ, ∀ n ≥ n₁,
            3 * n ≤ 4 * (upperGood P h D D' ξ Q a θ
              ⟨Ctop, Ctop.property.1⟩ p n).card)
    (hS36lower : ∀ Cmid : {x : ℝ // cMinus.toReal < x},
      ∃ κ : Set.Ioi (0 : ℝ), ∃ n₂ : ℕ, ∀ n ≥ n₂,
        3 * n ≤ 4 * (lowerGood P h D D' κ
          ⟨Cmid, lt_of_le_of_lt ENNReal.toReal_nonneg Cmid.property⟩ n).card)
    (hT58 : ∀ pbar : Set.Ioo (0 : ℝ) 1, cMinus < cPlus →
      ObjectsExistV2 P h D D' ξ Q cMinus cPlus pbar)
    (hC45 : ∀ (hstrict : cMinus < cPlus) (pbar : Set.Ioo (0 : ℝ) 1)
      (objs : ObjectsExistV2 P h D D' ξ Q cMinus cPlus pbar),
        C45CorrectedNonemptyInternal P h ξ Q D D' hD hD' hGFF
          cMinus cPlus hMinus hPlus hstrict pbar objs.radii objs.params objs.family) :
    cMinus = cPlus := by
  obtain ⟨pbar, hEndgame⟩ := selected_endgame_dyadic_of_C45
  apply hMAIN_fixed_common_exists_theta_v2 P h D D' ξ Q cMinus cPlus
    hPlusPos hMinus hPlus pbar hS36upper hS36lower
    (fun hstrict => hT58 pbar hstrict)
  intro hstrict θ objs a κ p
  have hC := hC45 hstrict pbar objs
  have hR53 := (hEndgame ξ Q D D' hD hD' P h hGFF cMinus cPlus
    hMinus hPlus hstrict objs hC).2 θ
  exact r53Dyadic_to_collision P h ξ Q D D' hD hD' hGFF
    cMinus cPlus hMinus hPlus hstrict pbar objs θ hR53 a κ p

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame
