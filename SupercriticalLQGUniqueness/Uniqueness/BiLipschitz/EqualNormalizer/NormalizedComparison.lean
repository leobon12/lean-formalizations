import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.EqualNormalizer.AroundLocality
import SupercriticalLQGUniqueness.Uniqueness.Positivity.FromAxioms.AXPOSComplete




 
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.EqualNormalizer
open LQGMetric (DistC IsGFFPlusCont)

 

theorem normalized_ebl
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (D D' : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D') :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
        ∀ᵐ ω ∂P, ∀ z w : ℂ,
          (D' (h ω)) (z,w) ≤ ENNReal.ofReal C * (D (h ω)) (z,w) ∧
          (D (h ω)) (z,w) ≤ ENNReal.ofReal C * (D' (h ω)) (z,w) := by
  have hQ : 0 < Q := Positivity.FromAxioms.axpos ξ Q D hD
  have hAround : ∀ z : ℂ, ∀ r : Set.Ioi (0 : ℝ), ∀ d e : LSCMetric,
      d.internal (BiLipschitz.OneScale.collarOpen z r : Set ℂ) =
        e.internal (BiLipschitz.OneScale.collarOpen z r : Set ℂ) →
      aroundDist d (BiLipschitz.OneScale.separatorAt z r) = aroundDist e (BiLipschitz.OneScale.separatorAt z r) := by
    intro z r d e hint
    exact aroundDist_eq_of_collar_internal_eq z r d e hint
  obtain ⟨A, hA, hGrid⟩ := normalized_grid_cover_of_around ξ Q hQ D D' hD hD' hAround
  obtain ⟨A', hA', hGrid'⟩ := normalized_grid_cover_of_around ξ Q hQ D' D hD' hD hAround
  let C := max (2 * A ^ 2) (2 * A' ^ 2)
  have hC : 1 ≤ C := by
    have hA2 : 1 ≤ 2 * A ^ 2 := by nlinarith [sq_nonneg A]
    exact hA2.trans (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro Ω _ P _ h hh
  have hGFF : IsGFFPlusCont h P :=
    LQGMetric.GM.Tight.isGFFPlusCont_of_wp hh.1
  have hL := IsWeakLQGMetric.length hD P h hGFF
  have hL' := IsWeakLQGMetric.length hD' P h hGFF
  have hB := BiLipschitz.Barrier.ae_barrier hD hQ P h hh
  have hB' := BiLipschitz.Barrier.ae_barrier hD' hQ P h hh
  have hG := hGrid P h hh
  have hG' := hGrid' P h hh
  filter_upwards [hL, hL', hB, hB', hG, hG'] with ω hl hl' hb hb' hg hg'
  intro z w
  have hleft := BiLipschitz.PaidSeparators.paid_separator_all_pairs (D (h ω)) (D' (h ω)) hb hl hA hg z w
  have hright := BiLipschitz.PaidSeparators.paid_separator_all_pairs (D' (h ω)) (D (h ω)) hb' hl' hA' hg' z w
  constructor
  · exact hleft.trans (by
      gcongr
      exact le_max_left (2 * A ^ 2) (2 * A' ^ 2))
  · exact hright.trans (by
      gcongr
      exact le_max_right (2 * A ^ 2) (2 * A' ^ 2))

end SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.EqualNormalizer
