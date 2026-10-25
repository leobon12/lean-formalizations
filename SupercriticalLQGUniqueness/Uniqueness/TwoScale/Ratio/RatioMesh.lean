import SupercriticalLQGUniqueness.Uniqueness.TwoScale.Ratio.RatioTranslate




 
set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.Ratio

open LQGMetric (DistC)

 

theorem ratio_finite_mesh_union
    (ξ : Ioi (0 : ℝ)) (Q : ℝ)
    (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (a : ℝ) (ha : 0 < a) :
    ∃ p c M : ℝ, 0 < p ∧ p < 1 ∧ 0 < c ∧ 1 ≤ M ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → DistC),
        IsNormalizedWholePlaneGFF h P →
        ∀ (mesh : Finset ℂ) (base : Ioi (0 : ℝ)) (K : ℕ),
          P {ω | ∃ z ∈ mesh,
            (LQGMetric.Blueprint.countOcc
              (fun k => {ω | h ω ∈ rawRatioEvent D z (ratioRadius base k)
                (ENNReal.ofReal M * ENNReal.ofReal M)}) K ω : ℝ) <
                (1 / 2 : ℝ) * K} ≤
            (mesh.card : ℝ≥0∞) *
              ENNReal.ofReal (c * Real.exp (-a * K)) := by
  obtain ⟨p, c, M, hp0, hp1, hc, hM, htail⟩ :=
    ratio_iteration_count_tail_at ξ Q D hD a ha
  refine ⟨p, c, M, hp0, hp1, hc, hM, ?_⟩
  intro Ω _ P _ h hh mesh base K
  let bad : ℂ → Set Ω := fun z =>
    {ω | (LQGMetric.Blueprint.countOcc
      (fun k => {ω | h ω ∈ rawRatioEvent D z (ratioRadius base k)
        (ENNReal.ofReal M * ENNReal.ofReal M)}) K ω : ℝ) <
        (1 / 2 : ℝ) * K}
  let ε : ℝ≥0∞ := ENNReal.ofReal (c * Real.exp (-a * K))
  have hset : {ω | ∃ z ∈ mesh, ω ∈ bad z} = ⋃ z ∈ mesh, bad z := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion]
    tauto
  change P {ω | ∃ z ∈ mesh, ω ∈ bad z} ≤ (mesh.card : ℝ≥0∞) * ε
  rw [hset]
  calc
    P (⋃ z ∈ mesh, bad z) ≤ ∑ z ∈ mesh, P (bad z) :=
      measure_biUnion_finset_le _ _
    _ ≤ ∑ _z ∈ mesh, ε := Finset.sum_le_sum (fun z _ => htail P h hh z base K)
    _ = (mesh.card : ℝ≥0∞) * ε := by
      simp only [Finset.sum_const, nsmul_eq_mul]


end SupercriticalLQGUniqueness.Uniqueness.TwoScale.Ratio
