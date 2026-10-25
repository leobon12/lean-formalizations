import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.EqualNormalizer.NormalizedComparison
import LQGMetric.Metric.WeylScaling




 
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal NNReal
namespace SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.EqualNormalizer

 

theorem len_le_mul_of_pointwise (D E : LSCMetric) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ p : ℂ × ℂ, E p ≤ ENNReal.ofReal C * D p)
    (P : ℝ → ℂ) (a b : ℝ) :
    E.len P a b ≤ ENNReal.ofReal C * D.len P a b := by
  unfold LSCMetric.len eVariationOn
  change (⨆ p : ℕ × {u : ℕ → ℝ // Monotone u ∧ ∀ i, u i ∈ Icc a b},
      ∑ i ∈ Finset.range p.1,
        edist (E.pt (P (p.2.1 (i + 1)))) (E.pt (P (p.2.1 i)))) ≤ _
  rw [ENNReal.mul_iSup]
  refine iSup_le fun p => le_iSup_of_le p ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  change E (P (p.2.1 (i + 1)), P (p.2.1 i)) ≤
    ENNReal.ofReal C * D (P (p.2.1 (i + 1)), P (p.2.1 i))
  exact h _

 
theorem isCurve_of_pointwise_le (D E : LSCMetric) (C : ℝ) (hC : 0 ≤ C)
    (h : ∀ p : ℂ × ℂ, E p ≤ ENNReal.ofReal C * D p)
    (P : ℝ → ℂ) (a b : ℝ) (hP : D.IsCurve P a b) : E.IsCurve P a b := by
  let K : ℝ≥0 := ⟨C, hC⟩
  have hK : K = NNReal.mk C hC := by
    apply Subtype.ext
    rfl
  have hlip : @LipschitzWith D.Space E.Space
      (@EMetricSpace.toPseudoEMetricSpace D.Space D.instEMetricSpace)
      (@EMetricSpace.toPseudoEMetricSpace E.Space E.instEMetricSpace)
      K (fun x : D.Space => (x : E.Space)) := by
    intro x y
    change E (x, y) ≤ (K : ℝ≥0∞) * D (x, y)
    rw [hK, ← ENNReal.ofReal_eq_coe_nnreal hC]
    exact h (x, y)
  refine ⟨hP.1, ?_⟩
  have hc := hlip.continuous.comp_continuousOn hP.2
  dsimp [LSCMetric.pt, Function.comp, id] at hc ⊢
  exact hc

end SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.EqualNormalizer
