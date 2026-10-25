import SupercriticalLQGUniqueness.Uniqueness.EndSaving.InterfaceV2.SourceStatementsV2




 
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame
open LQGMetric (DistC)
open SupercriticalLQGUniqueness.Uniqueness.EndSaving.Interfaces
open SupercriticalLQGUniqueness.Uniqueness.EndSaving.InterfaceV2

 
def R52ClosedEndSavingDyadic {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (D D' : DistC → LSCMetric)
    (_hD : IsWeakLQGMetric ξ Q D) (_hD' : IsWeakLQGMetric ξ Q D')
    (_hGFF : IsNormalizedWholePlaneGFF h P)
    (cMinus cPlus : ℝ≥0∞)
    (_hMinus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus)
    (_hPlus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus)
    (_hstrict : cMinus < cPlus) (pbar : Set.Ioo (0 : ℝ) 1)
    (objs : ObjectsExistV2 P h D D' ξ Q cMinus cPlus pbar) : Prop :=
  ∀ (ν κG κEnd : Set.Ioi (0 : ℝ)) (η : Set.Ioo (0 : ℝ) 1),
    ∃ δ₀ : Set.Ioo (0 : ℝ) 1,
      ∀ δ : ℝ, (hδ : 0 < δ) → δ ≤ δ₀ → ∀ j : ℕ,
        let b := dyadicRadius j
        ENNReal.ofReal (κG : ℝ) ≤
          P (h ⁻¹' OptimalConstants.Ratios.GtildeEvent D D' b κG
            ⟨objs.cMid', lt_of_le_of_lt ENNReal.toReal_nonneg objs.cMid'_lower⟩) →
        ENNReal.ofReal (1 - (η : ℝ)) ≤
          P (ClosedEndSaving h D D' ξ Q cPlus b ν ⟨δ, hδ⟩ κEnd)

 
def R53OfObjectsDyadic {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (D D' : DistC → LSCMetric)
    (_hD : IsWeakLQGMetric ξ Q D) (_hD' : IsWeakLQGMetric ξ Q D')
    (_hGFF : IsNormalizedWholePlaneGFF h P)
    (cMinus cPlus : ℝ≥0∞)
    (_hMinus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus)
    (_hPlus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus)
    (_hstrict : cMinus < cPlus) (pbar : Set.Ioo (0 : ℝ) 1)
    (objs : ObjectsExistV2 P h D D' ξ Q cMinus cPlus pbar)
    (θ : Set.Ioi (0 : ℝ)) : Prop :=
  ∀ (a : Set.Ioo (3 / 4 : ℝ) 1) (κ : Set.Ioi (0 : ℝ))
    (p : Set.Ioo (0 : ℝ) 1),
    ∃ δ₀ : Set.Ioo (0 : ℝ) cPlus.toReal,
      ∀ δ : ℝ, (hδ : 0 < δ) → (hδsmall : δ ≤ δ₀) → ∀ j : ℕ,
        let b := dyadicRadius j
        ENNReal.ofReal (κ : ℝ) ≤
          P (h ⁻¹' OptimalConstants.Ratios.GtildeEvent D D' b κ
            ⟨objs.cMid', lt_of_le_of_lt ENNReal.toReal_nonneg objs.cMid'_lower⟩) →
        P (h ⁻¹' {g | OptimalConstants.Ratios.HEvent D D' ξ Q b a
          ⟨cPlus.toReal - δ,
            by exact sub_pos.mpr (lt_of_le_of_lt hδsmall δ₀.property.2)⟩ θ g}) <
            ENNReal.ofReal (p : ℝ)

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame
