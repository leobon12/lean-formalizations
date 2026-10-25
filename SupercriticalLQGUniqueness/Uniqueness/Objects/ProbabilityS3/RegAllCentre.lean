import SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3.RegBudget
import SupercriticalLQGUniqueness.Uniqueness.Objects.ClauseMeasurability.CentreBudget




 
set_option autoImplicit false
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3

theorem exists_s1_s2_s3_allCentre_budget
    (μ : Measure LQGMetric.DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : LQGMetric.DistC → LQGMetric.DistC) μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : LQGMetric.DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (pbar : Ioo (0 : ℝ) 1) :
    ∃ cReg a A : ℝ, 0 < cReg ∧ cReg < 1 ∧
      0 < a ∧ a < 1 ∧ 1 < A ∧ a⁻¹ < A ∧ ∃ k0 : ℕ, 48 ≤ k0 ∧
      ∀ C : Objects.CorrectedEvent.Constants, C.ξ = ξ → C.Q = Q →
        C.A_across ≤ a → A ≤ C.A_around → C.c_reg ≤ cReg → k0 ≤ C.k0 →
        ∀ z : ℂ,
          μ (Objects.Producer.centreTarget {g | ¬ Objects.CorrectedEvent.S1 C (D g) g} z) ≤
            ENNReal.ofReal ((1 - (pbar : ℝ)) / 10) ∧
          μ (Objects.Producer.centreTarget {g | ¬ Objects.CorrectedEvent.S2 C (D g) g} z) ≤
            ENNReal.ofReal ((1 - (pbar : ℝ)) / 10) ∧
          μ (Objects.Producer.centreTarget {g | ¬ Objects.CorrectedEvent.S3 C (D g)} z) ≤
            ENNReal.ofReal ((1 - (pbar : ℝ)) / 10) := by
  obtain ⟨cReg, hc0, hc1, k0, hk0, h3⟩ :=
    exists_s3_budget μ hμ ξ Q D hD pbar
  obtain ⟨a, A, ha0, ha1, hA1, hAinv, h12⟩ :=
    Objects.ClauseMeasurability.exists_s1_s2_allCentre_budget μ hμ ξ Q D hD pbar
  refine ⟨cReg, a, A, hc0, hc1, ha0, ha1, hA1, hAinv, k0, hk0, ?_⟩
  intro C hξ hQ hCa hCA hCc hk z
  obtain ⟨h1, h2⟩ := h12 C hξ hQ hCa hCA z
  refine ⟨h1, h2, ?_⟩
  rw [Objects.ClauseMeasurability.measure_s3_centreTarget_eq μ hμ C D hD.measurable z]
  exact h3 C hCc hk

end SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3
