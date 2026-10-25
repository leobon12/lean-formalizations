import SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame.A16Scopes




 




set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame
open LQGMetric (DistC)
open SupercriticalLQGUniqueness.Uniqueness.EndSaving.Interfaces
open SupercriticalLQGUniqueness.Uniqueness.EndSaving.InterfaceV2

 

theorem r53Dyadic_to_collision {Ω : Type} [MeasurableSpace Ω]
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
    (hR53 : R53OfObjectsDyadic P h ξ Q D D' hD hD' hGFF
      cMinus cPlus hMinus hPlus hstrict pbar objs θ)
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
  let q : Set.Ioo (0 : ℝ) 1 :=
    ⟨(p : ℝ) / 2, by have := p.property.1; linarith,
      by have := p.property.2; linarith⟩
  obtain ⟨δ₀, hδ₀⟩ := hR53 a κ q
  let δ : ℝ := (δ₀ : ℝ) / 2
  have hδpos : 0 < δ := by dsimp [δ]; have := δ₀.property.1; linarith
  have hδsmall : δ ≤ δ₀ := by dsimp [δ]; have := δ₀.property.1; linarith
  let Ctop : Set.Ioo (0 : ℝ) cPlus.toReal :=
    ⟨cPlus.toReal - δ,
      by have := δ₀.property.2; dsimp [δ]; have := δ₀.property.1; linarith,
      by exact sub_lt_self _ hδpos⟩
  refine ⟨Ctop, ?_⟩
  intro j hgood
  exact hδ₀ δ hδpos hδsmall j hgood

end SupercriticalLQGUniqueness.Uniqueness.EndSaving.Endgame
