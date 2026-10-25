import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame.CommonPbar




 
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame
open LQGMetric (DistC)
open SupercriticalLQGUniqueness.Uniqueness.EndSaving.Interfaces
open SupercriticalLQGUniqueness.Uniqueness.EndSaving.InterfaceV2

theorem hMAIN_fixed_common_exists_theta_v2 {Ω : Type} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistC)
    (D D' : DistC → LSCMetric) (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (cMinus cPlus : ℝ≥0∞) (hPlusPos : 0 < cPlus)
    (hMinus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus)
    (hPlus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus)
    (pbar : Set.Ioo (0 : ℝ) 1)
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
    (hT58 : cMinus < cPlus →
      ObjectsExistV2 P h D D' ξ Q cMinus cPlus pbar)
    (hR53 : cMinus < cPlus → ∀ θ : Set.Ioi (0 : ℝ), ∀ (objs : ObjectsExistV2 P h D D' ξ Q cMinus cPlus pbar)
      (a : Set.Ioo (3 / 4 : ℝ) 1) (κ : Set.Ioi (0 : ℝ))
      (p : Set.Ioo (0 : ℝ) 1),
        ∃ Ctop : Set.Ioo (0 : ℝ) cPlus.toReal,
          ∀ j : ℕ,
            ENNReal.ofReal (κ : ℝ) ≤
              P (h ⁻¹' OptimalConstants.Ratios.GtildeEvent D D'
                (dyadicRadius j) κ
                  ⟨objs.cMid', lt_of_le_of_lt ENNReal.toReal_nonneg objs.cMid'_lower⟩) →
            P (h ⁻¹' {g | OptimalConstants.Ratios.HEvent D D' ξ Q (dyadicRadius j) a
              ⟨Ctop, Ctop.property.1⟩ θ g}) <
                ENNReal.ofReal ((p : ℝ) / 2)) :
    cMinus = cPlus := by
  obtain ⟨θ, a, p, hUpper⟩ := hS36upper
  exact hMAIN_fixed_common_pbar_v2 P h D D' ξ Q cMinus cPlus hPlusPos
    hMinus hPlus θ pbar ⟨a, p, hUpper⟩ hS36lower hT58
    (fun hstrict objs a κ p => hR53 hstrict θ objs a κ p)

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame
