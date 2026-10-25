import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.EqualNormalizer.EBL
import SupercriticalLQGUniqueness.Uniqueness.OptimalConstants.Ratios.Section3




 




set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.Assembly.Root
open LQGMetric (DistC IsGFFPlusCont)

private theorem ratioPair_of_upperOptimal_pos (d e : LSCMetric)
    (h : 0 < OptimalConstants.Ratios.upperOptimal d e) :
    ∃ z w : ℂ, OptimalConstants.Ratios.RatioPair d z w := by
  by_contra hn
  have hzero : OptimalConstants.Ratios.upperOptimal d e = 0 := by
    apply le_antisymm
    · unfold OptimalConstants.Ratios.upperOptimal
      refine iSup_le fun z => iSup_le fun w => iSup_le fun hp => ?_
      exact False.elim (hn ⟨z, w, hp⟩)
    · exact bot_le
  exact h.ne' hzero

private theorem biLipBound_of_ebl (d e : LSCMetric) (C : ℝ) (hC : 0 < C)
    (h : ∀ z w : ℂ, e (z, w) ≤ ENNReal.ofReal C * d (z, w) ∧
      d (z, w) ≤ ENNReal.ofReal C * e (z, w)) :
    OptimalConstants.Ratios.BiLipBound d e (ENNReal.ofReal C⁻¹) (ENNReal.ofReal C) := by
  intro z w
  constructor
  · have hmul := mul_le_mul_left (h z w).2 (ENNReal.ofReal C⁻¹)
    calc ENNReal.ofReal C⁻¹ * d (z, w)
        ≤ ENNReal.ofReal C⁻¹ * (ENNReal.ofReal C * e (z, w)) := by
          simpa only [mul_comm] using hmul
      _ = e (z, w) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (inv_pos.mpr hC).le,
            inv_mul_cancel₀ hC.ne', ENNReal.ofReal_one, one_mul]
  · exact (h z w).1

 
theorem weakLQGMetric_unique_of_main
    (hDET : ∀ (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ), 0 < Q →
      ∀ (D D' : DistC → LSCMetric), IsWeakLQGMetric ξ Q D → IsWeakLQGMetric ξ Q D' →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
      ∃ cMinus cPlus : ℝ≥0∞,
        0 < cMinus ∧ cMinus < ⊤ ∧ 0 < cPlus ∧ cPlus < ⊤ ∧
        (∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus) ∧
        (∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus))
    (hMAIN : ∀ (ξ : Set.Ioi (0 : ℝ)) (Q : ℝ), 0 < Q →
      ∀ (D D' : DistC → LSCMetric), IsWeakLQGMetric ξ Q D → IsWeakLQGMetric ξ Q D' →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
      ∀ cMinus cPlus : ℝ≥0∞,
        (∀ᵐ ω ∂P, OptimalConstants.Ratios.lowerOptimal (D (h ω)) (D' (h ω)) = cMinus) →
        (∀ᵐ ω ∂P, OptimalConstants.Ratios.upperOptimal (D (h ω)) (D' (h ω)) = cPlus) →
        cMinus = cPlus) :
    ∀ ξ : Set.Ioi (0 : ℝ), ∀ Q : ℝ, IsLFPPExponent ξ Q →
      ∀ D D' : DistC → LSCMetric,
        IsWeakLQGMetric ξ Q D → IsWeakLQGMetric ξ Q D' →
        ∃ C : ℝ, 0 < C ∧
          ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
            (h : Ω → DistC), IsGFFPlusCont h P →
            ∀ᵐ ω ∂P, ∀ u v : ℂ,
              (D (h ω)).1 (u, v) = ENNReal.ofReal C * (D' (h ω)).1 (u, v) := by
  intro ξ Q _ D D' hD hD'
  have hQpos : 0 < Q := Positivity.FromAxioms.axpos ξ Q D hD
  obtain ⟨Ω₀, mΩ₀, P₀, hP₀, H₀, hH₀⟩ := exists_normalizedGFF
  letI : MeasurableSpace Ω₀ := mΩ₀
  letI : IsProbabilityMeasure P₀ := hP₀
  obtain ⟨cMinus, cPlus, hMinusPos, hMinusFin, hPlusPos, hPlusFin,
    hMinus, hPlus⟩ := hDET ξ Q hQpos D' D hD' hD P₀ H₀ hH₀
  have hEq : cMinus = cPlus :=
    hMAIN ξ Q hQpos D' D hD' hD P₀ H₀ hH₀ cMinus cPlus hMinus hPlus
  obtain ⟨K, hK, hEBL⟩ := BiLipschitz.EqualNormalizer.ebl ξ Q D' D hD' hD
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hK
  have hc : 0 < ENNReal.ofReal K⁻¹ := ENNReal.ofReal_pos.mpr (inv_pos.mpr hKpos)
  have hGFF : IsGFFPlusCont H₀ P₀ :=
    LQGMetric.GM.Tight.isGFFPlusCont_of_wp hH₀.1
  have hB : ∀ᵐ ω ∂P₀,
      OptimalConstants.Ratios.BiLipBound (D' (H₀ ω)) (D (H₀ ω))
        (ENNReal.ofReal K⁻¹) (ENNReal.ofReal K) := by
    filter_upwards [hEBL P₀ H₀ hGFF] with ω hω
    exact biLipBound_of_ebl (D' (H₀ ω)) (D (H₀ ω)) K hKpos hω
  have hPair : ∀ᵐ ω ∂P₀,
      ∃ z w : ℂ, OptimalConstants.Ratios.RatioPair (D' (H₀ ω)) z w := by
    filter_upwards [hPlus] with ω hw
    exact ratioPair_of_upperOptimal_pos _ _ (hw ▸ hPlusPos)
  have hAll := OptimalConstants.Ratios.ae_allPairs_of_ae_optima P₀
    (fun ω => D' (H₀ ω)) (fun ω => D (H₀ ω)) hc hB hPair hMinus hPlus
  have hNorm : ∀ᵐ ω ∂P₀, ∀ u v : ℂ,
      (D (H₀ ω)).1 (u,v) = cPlus * (D' (H₀ ω)).1 (u,v) := by
    rw [hEq] at hAll
    filter_upwards [hAll] with ω hω u v
    exact le_antisymm (hω u v).2 (hω u v).1
  have hCpos : 0 < cPlus.toReal := ENNReal.toReal_pos hPlusPos.ne' hPlusFin.ne
  have hCeq : ENNReal.ofReal cPlus.toReal = cPlus := ENNReal.ofReal_toReal hPlusFin.ne
  apply TwoScale.GapChecks.rootExtension_of_reference ξ Q D D' hD hD'
  exact ⟨Ω₀, mΩ₀, P₀, H₀, cPlus.toReal, hH₀, hCpos,
    by simpa only [hCeq] using hNorm⟩

end SupercriticalLQGUniqueness.Uniqueness.Assembly.Root
