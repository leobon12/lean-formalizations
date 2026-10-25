import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.EqualNormalizer.WeightedImage




 
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal
namespace SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.EqualNormalizer
open LQGMetric.MetricGeometry

 

theorem subordinate_length_clock_lipschitz
    (D E : LSCMetric) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ p : ℂ × ℂ, E p ≤ ENNReal.ofReal C * D p)
    (P : ℝ → ℂ) (L : ℝ) (hL : 0 ≤ L)
    (hu : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 L)) :
    LipschitzOnWith (⟨C, hC⟩ : ℝ≥0)
      (variationOnFromTo (E.pt ∘ P) (Icc 0 L) 0) (Icc 0 L) := by
  let F := E.pt ∘ P
  let σ := variationOnFromTo F (Icc 0 L) 0
  let K : ℝ≥0 := ⟨C, hC⟩
  have hDlen : D.len P 0 L = ENNReal.ofReal L := by
    exact hasUnitSpeedOn_Icc_iff.mp hu 0 L le_rfl hL le_rfl |>.trans (by simp)
  have hEfin : E.len P 0 L ≠ ∞ := by
    have hbound := len_le_mul_of_pointwise D E C hC h P 0 L
    rw [hDlen] at hbound
    exact ne_top_of_le_ne_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      ENNReal.ofReal_lt_top).ne hbound
  have hbv : BoundedVariationOn F (Icc 0 L) := hEfin
  have hloc : LocallyBoundedVariationOn F (Icc 0 L) := hbv.locallyBoundedVariationOn
  have hdiff : ∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L, s ≤ t →
      σ t - σ s = (E.len P s t).toReal := by
    intro s hs t ht hst
    calc
      σ t - σ s = variationOnFromTo F (Icc 0 L) s t :=
        variationOnFromTo.sub_right hloc ⟨le_rfl, hL⟩ ht hs
      _ = (E.len P s t).toReal := by
        rw [variationOnFromTo.eq_of_le F (Icc 0 L) hst,
          inter_eq_right.mpr (Icc_subset_Icc hs.1 ht.2)]
        rfl
  have hdiffBound : ∀ s ∈ Icc 0 L, ∀ t ∈ Icc 0 L, s ≤ t →
      σ t - σ s ≤ C * (t - s) := by
    intro s hs t ht hst
    rw [hdiff s hs t ht hst]
    have hlen := len_le_mul_of_pointwise D E C hC h P s t
    have hDlenst : D.len P s t = ENNReal.ofReal (t - s) :=
      hasUnitSpeedOn_Icc_iff.mp hu s t hs.1 hst ht.2
    rw [hDlenst, ← ENNReal.ofReal_mul hC] at hlen
    have hb := ENNReal.toReal_mono ENNReal.ofReal_ne_top hlen
    simpa only [ENNReal.toReal_ofReal (mul_nonneg hC (sub_nonneg.mpr hst))] using hb
  intro s hs t ht
  have hK : (K : ℝ≥0∞) = ENNReal.ofReal C := by
    rw [ENNReal.ofReal_eq_coe_nnreal hC]
    congr 1
  change edist (σ s) (σ t) ≤ (K : ℝ≥0∞) * edist s t
  rw [hK]
  simp only [edist_dist, Real.dist_eq]
  rw [← ENNReal.ofReal_mul hC]
  rcases le_total s t with hst | hst
  · rw [abs_sub_comm]
    have hσnonneg : 0 ≤ σ t - σ s := by
      rw [hdiff s hs t ht hst]
      exact ENNReal.toReal_nonneg
    rw [abs_of_nonneg hσnonneg, abs_of_nonpos (sub_nonpos.mpr hst)]
    simpa only [neg_sub] using ENNReal.ofReal_le_ofReal (hdiffBound s hs t ht hst)
  · have hσnonneg : 0 ≤ σ s - σ t := by
      rw [hdiff t ht s hs hst]
      exact ENNReal.toReal_nonneg
    rw [abs_of_nonneg hσnonneg, abs_of_nonneg (sub_nonneg.mpr hst)]
    exact ENNReal.ofReal_le_ofReal (hdiffBound t ht s hs hst)

end SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.EqualNormalizer
