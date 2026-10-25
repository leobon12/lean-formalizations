import SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.FixedUnit.Infimum
import SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Determinism.HDet




 

set_option autoImplicit false
noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.FixedUnit

open SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Ratios
open LQGMetric (DistC)

 


theorem ae_HEvent_to_GEvent
    (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q)
    (D E : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (hE : IsWeakLQGMetric ξ Q E)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (a : Set.Ioo (3 / 4 : ℝ) 1) (θ : Set.Ioi (0 : ℝ))
    (ζ : ℝ) (hζ : 0 < ζ) :
    ∃ cPlus : ℝ≥0∞, 0 < cPlus ∧ cPlus < ⊤ ∧
      (∀ᵐ ω ∂P, upperOptimal (D (h ω)) (E (h ω)) = cPlus) ∧
      ∃ κ : Set.Ioi (0 : ℝ),
        ∀ᵐ ω ∂P, ∀ (r : Set.Ioi (0 : ℝ))
          (C : Set.Ioi (0 : ℝ)) (hζC : ζ < (C : ℝ)),
          HEvent D E ξ Q r a C θ (h ω) →
          h ω ∈ GEvent D E r κ
            ⟨(C : ℝ) - ζ, sub_pos.mpr hζC⟩ := by
  obtain ⟨cMinus, cPlus, hcMinus, _hcMinusTop, hcPlus, hcPlusTop,
    hMinus, hPlus⟩ := OptimalConstants.Determinism.hDET_proved ξ Q hQ D E hD hE P h hh
  let c : NNReal := cPlus.toNNReal
  have hc : 0 < c := by
    exact ENNReal.toNNReal_pos hcPlus.ne' hcPlusTop.ne
  have hcoe : (c : ℝ≥0∞) = cPlus :=
    ENNReal.coe_toNNReal hcPlusTop.ne
  obtain ⟨K, hK, hEBL⟩ := BiLipschitz.EqualNormalizer.ebl ξ Q D E hD hE
  have hGFFPlus : LQGMetric.IsGFFPlusCont h P :=
    LQGMetric.GM.detGFFPlusCont hh.1
  have hB : ∀ᵐ ω ∂P,
      BiLipBound (D (h ω)) (E (h ω))
        (ENNReal.ofReal K)⁻¹ (ENNReal.ofReal K) := by
    filter_upwards [hEBL P h hGFFPlus] with ω hb
    exact OptimalConstants.Determinism.biLipBound_of_symmetric_ebl K hK (D (h ω)) (E (h ω)) hb
  have hPair : ∀ᵐ ω ∂P,
      ∃ u v : ℂ, RatioPair (D (h ω)) u v :=
    OptimalConstants.Determinism.ae_finitePair_of_tightness ξ Q D hD P h hh
  have hLower : 0 < (ENNReal.ofReal K)⁻¹ :=
    ENNReal.inv_pos.mpr ENNReal.ofReal_ne_top
  have hAll : ∀ᵐ ω ∂P, ∀ z w : ℂ,
      E (h ω) (z, w) ≤ (c : ℝ≥0∞) * D (h ω) (z, w) := by
    filter_upwards [ae_allPairs_of_ae_optima P
      (fun ω => D (h ω)) (fun ω => E (h ω))
      hLower hB hPair hMinus hPlus] with ω hb z w
    simpa only [hcoe] using (hb z w).2
  have hDlen : ∀ᵐ ω ∂P, (D (h ω)).IsLengthSpace :=
    hD.length P h hGFFPlus
  have hElen : ∀ᵐ ω ∂P, (E (h ω)).IsLengthSpace :=
    hE.length P h hGFFPlus
  have hDreg : ∀ᵐ ω ∂P,
      ∀ (γ : ℝ → ℂ) (s t : ℝ),
        (D (h ω)).IsCurve γ s t → ContinuousOn γ (Icc s t) := by
    filter_upwards [BiLipschitz.Barrier.ae_curves_continuous hD hQ P h hh] with ω hreg
    exact hreg.2.1
  have hEreg : ∀ᵐ ω ∂P,
      ∀ (γ : ℝ → ℂ) (s t : ℝ),
        (E (h ω)).IsCurve γ s t → ContinuousOn γ (Icc s t) := by
    filter_upwards [BiLipschitz.Barrier.ae_curves_continuous hE hQ P h hh] with ω hreg
    exact hreg.2.1
  have hradius : 0 < (1 - (a : ℝ)) ^ 4 :=
    pow_pos (sub_pos.mpr a.property.2) _
  obtain ⟨δ, hδ, hδB, herr⟩ :=
    exists_endpoint_error_radius (c : ℝ) θ ζ
      ((1 - (a : ℝ)) ^ 4) θ.property hζ hradius
  refine ⟨cPlus, hcPlus, hcPlusTop, hPlus, ⟨δ, hδ⟩, ?_⟩
  filter_upwards [hDlen, hElen, hDreg, hEreg, hAll]
    with ω hDl hEl hDr hEr hComp
  intro r C hζC hHE
  obtain ⟨hCircle, _hCircle, hH⟩ := hHE
  exact H_to_G_on_regular_at_radius
    (D (h ω)) (E (h ω)) c hc hDl hEl hDr hEr hComp
    ξ Q a θ ζ hζ δ hδ hδB herr r C hCircle hζC hH


end SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.FixedUnit
