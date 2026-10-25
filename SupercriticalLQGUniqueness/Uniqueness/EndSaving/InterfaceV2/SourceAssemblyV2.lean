import SupercriticalLQGUniqueness.Uniqueness.EndSaving.InterfaceV2.AssemblyV2
import SupercriticalLQGUniqueness.Uniqueness.EndSaving.InterfaceV2.R53AdapterV2




 



set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.InterfaceV2
open LQGMetric (DistC)
open SupercriticalLQGUniqueness.Uniqueness.EndSaving.Interfaces

 

def T58DataV2.ofObjectsExistV2 {Ω : Type} [MeasurableSpace Ω]
    {P : Measure Ω} {h : Ω → DistC} {D D' : DistC → LSCMetric}
    {ξ : Set.Ioi (0 : ℝ)} {Q : ℝ}
    {cMinus cPlus : ℝ≥0∞} {pbar : Set.Ioo (0 : ℝ) 1}
    (objs : ObjectsExistV2 P h D D' ξ Q cMinus cPlus pbar) :
    T58DataV2 P h D D' ξ Q cMinus cPlus pbar :=
  ⟨objs.cMid', objs.cMid'_lower, objs.cMid'_upper,
    objs.radii, objs.params, objs.family, objs.density⟩

 

theorem hMAIN_fixed_from_v2_statements
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ)
    (D D' : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D')
    (hGFF : IsNormalizedWholePlaneGFF h P)
    (cMinus cPlus : ℝ≥0∞) (hPlusPos : 0 < cPlus)
    (hMinus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus)
    (hPlus : ∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus)
    (θ : Set.Ioi (0 : ℝ))
    (hS36upper : ∃ a : Set.Ioo (3 / 4 : ℝ) 1,
      ∃ p : Set.Ioo (0 : ℝ) 1,
        ∀ Ctop : Set.Ioo (0 : ℝ) cPlus.toReal,
          ∃ n₁ : ℕ, ∀ n ≥ n₁,
            3 * n ≤ 4 * (upperGood P h D D' ξ Q a θ
              ⟨Ctop, Ctop.property.1⟩ p n).card)
    (hS36lower : ∀ Cmid : {x : ℝ // cMinus.toReal < x},
      ∃ κ : Set.Ioi (0 : ℝ), ∃ n₂ : ℕ, ∀ n ≥ n₂,
        3 * n ≤ 4 * (lowerGood P h D D' κ
          ⟨Cmid, lt_of_le_of_lt ENNReal.toReal_nonneg Cmid.property⟩ n).card)
    (hT58 : ∀ hstrict : cMinus < cPlus,
      T58Statement P h ξ Q D D' hD hD' hGFF
        cMinus cPlus hMinus hPlus hstrict)
    (hR53 : ∀ (hstrict : cMinus < cPlus)
      (pbar : Set.Ioo (0 : ℝ) 1)
      (objs : ObjectsExistV2 P h D D' ξ Q cMinus cPlus pbar),
      R53OfObjectsInternal P h ξ Q D D' hD hD' hGFF
        cMinus cPlus hMinus hPlus hstrict pbar objs θ) :
    cMinus = cPlus := by
  have hObjs : ∀ pbar : Set.Ioo (0 : ℝ) 1, cMinus < cPlus →
      T58DataV2 P h D D' ξ Q cMinus cPlus pbar := by
    intro pbar hstrict
    exact T58DataV2.ofObjectsExistV2
      (Classical.choice (hT58 hstrict pbar))
  have hCompare : cMinus < cPlus →
      (∀ᵐ ω ∂P, ∀ z w : ℂ,
        (D' (h ω)) (z, w) ≤ cPlus * (D (h ω)) (z, w)) →
      ∀ (pbar : Set.Ioo (0 : ℝ) 1)
        (objs : ObjectsExistV2 P h D D' ξ Q cMinus cPlus pbar)
        (a : Set.Ioo (3 / 4 : ℝ) 1) (κ : Set.Ioi (0 : ℝ))
        (p : Set.Ioo (0 : ℝ) 1),
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
    intro hstrict _ pbar objs a κ p
    exact r53_to_dyadic P h ξ Q D D' hD hD' hGFF
      cMinus cPlus hMinus hPlus hstrict pbar objs θ
      (hR53 hstrict pbar objs) a κ p
  exact hMAIN_fixed_of_repaired_sections P h ξ Q D D' hD hD'
    hGFF cMinus cPlus hPlusPos hMinus hPlus θ
    hS36upper hS36lower hObjs hCompare

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.InterfaceV2
