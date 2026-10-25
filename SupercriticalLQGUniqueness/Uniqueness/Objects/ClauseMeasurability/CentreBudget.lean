import SupercriticalLQGUniqueness.Uniqueness.Objects.ClauseMeasurability.EventMeas
import SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS1S2.Tight
import SupercriticalLQGUniqueness.Uniqueness.Objects.CentreEvent.CentreLaw




 





set_option autoImplicit false
noncomputable section

open Set Metric MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.ClauseMeasurability

open LQGMetric (DistC)

 

theorem exists_s1_s2_allCentre_budget (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (pbar : Ioo (0 : ℝ) 1) :
    ∃ a A : ℝ, 0 < a ∧ a < 1 ∧ 1 < A ∧ a⁻¹ < A ∧
      ∀ C : Objects.CorrectedEvent.Constants, C.ξ = ξ → C.Q = Q →
        C.A_across ≤ a → A ≤ C.A_around → ∀ z : ℂ,
          μ (Objects.Producer.centreTarget {g | ¬ Objects.CorrectedEvent.S1 C (D g) g} z) ≤
            ENNReal.ofReal ((1 - (pbar : ℝ)) / 10) ∧
          μ (Objects.Producer.centreTarget {g | ¬ Objects.CorrectedEvent.S2 C (D g) g} z) ≤
            ENNReal.ofReal ((1 - (pbar : ℝ)) / 10) := by
  obtain ⟨a, A, ha0, ha1, hA1, hAinv, hb⟩ :=
    Objects.ProbabilityS1S2.exists_s1_s2_joint_budget μ hμ ξ Q D hD pbar
  refine ⟨a, A, ha0, ha1, hA1, hAinv, ?_⟩
  intro C hξ hQ hCa hCA z
  obtain ⟨h1, h2⟩ := hb C hξ hQ hCa hCA
  have hm1 : NullMeasurableSet {g | ¬ Objects.CorrectedEvent.S1 C (D g) g} μ :=
    (measurableSet_S1 C D hD.measurable).compl.nullMeasurableSet
  have hm2 : NullMeasurableSet {g | ¬ Objects.CorrectedEvent.S2 C (D g) g} μ :=
    (measurableSet_S2 C D hD.measurable).compl.nullMeasurableSet
  constructor
  · have heq : μ (Objects.Producer.centreTarget {g | ¬ Objects.CorrectedEvent.S1 C (D g) g} z) =
        μ {g | ¬ Objects.CorrectedEvent.S1 C (D g) g} := by
      simpa using (Objects.CentreEvent.measure_centreTarget_eq hμ _
        (by simpa using hm1) z)
    exact heq.le.trans h1
  · have heq : μ (Objects.Producer.centreTarget {g | ¬ Objects.CorrectedEvent.S2 C (D g) g} z) =
        μ {g | ¬ Objects.CorrectedEvent.S2 C (D g) g} := by
      simpa using (Objects.CentreEvent.measure_centreTarget_eq hμ _
        (by simpa using hm2) z)
    exact heq.le.trans h2

 

theorem measure_s3_centreTarget_eq (μ : Measure DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : DistC → DistC) μ)
    (C : Objects.CorrectedEvent.Constants) (D : DistC → LSCMetric)
    (hD : Measurable D) (z : ℂ) :
    μ (Objects.Producer.centreTarget {g | ¬ Objects.CorrectedEvent.S3 C (D g)} z) =
      μ {g | ¬ Objects.CorrectedEvent.S3 C (D g)} := by
  have hm : NullMeasurableSet {g | ¬ Objects.CorrectedEvent.S3 C (D g)} μ :=
    (measurableSet_S3 C D hD).compl.nullMeasurableSet
  simpa using (Objects.CentreEvent.measure_centreTarget_eq hμ _ (by simpa using hm) z)

end SupercriticalLQGUniqueness.Uniqueness.Objects.ClauseMeasurability
