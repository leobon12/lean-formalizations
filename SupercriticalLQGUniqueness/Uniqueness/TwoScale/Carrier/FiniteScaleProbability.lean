import SupercriticalLQGUniqueness.Uniqueness.TwoScale.Carrier.PolynomialTail
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.Carrier.FiniteScaleSample
import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier.Prob
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.Ratio.RatioFiniteAt




 



set_option autoImplicit false
noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.Carrier

open LQGMetric (DistC)

 


theorem finite_scale_good_sample_bad_probability
    (ξ : Ioi (0 : ℝ)) (Q : ℝ)
    (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (α : ℝ) (hα1 : α < 1) :
    ∃ p c M C : ℝ, 0 < p ∧ p < 1 ∧ 0 < c ∧ 1 ≤ M ∧ 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → DistC),
        IsNormalizedWholePlaneGFF h P →
        ∀ (lam R : ℝ) (hlam : 0 < lam), lam < 1 → (hR : 0 < R) → ∀ (z₀ : ℂ),
          P {ω | ¬ (
            BiLipschitz.Barrier.Barrier (D (h ω)) ∧
            (D (h ω)).IsLengthSpace ∧
            (∀ z ∈ TwoScale.Mesh.scaleMesh lam R z₀, ∀ k : ℕ,
              aroundDist (D (h ω))
                (BiLipschitz.OneScale.crossingAt z (TwoScale.Ratio.ratioRadius
                  (scaleBase lam R α hlam hR) k)) ≠ ∞) ∧
            ¬ ∃ z ∈ TwoScale.Mesh.scaleMesh lam R z₀,
              (LQGMetric.Blueprint.countOcc
                (fun k => {ω | h ω ∈ TwoScale.Ratio.rawRatioEvent D z
                  (TwoScale.Ratio.ratioRadius (scaleBase lam R α hlam hR) k)
                  (ENNReal.ofReal M * ENNReal.ofReal M)})
                (scaleCount lam α) ω : ℝ) <
                  (1 / 2 : ℝ) * scaleCount lam α)} ≤
            ENNReal.ofReal (C * lam ^ (4 : ℕ)) := by
  obtain ⟨p, c, M, C, hp, hp1, hc, hM, hC, htail⟩ :=
    scaleMesh_ratio_bad_tail_polynomial ξ Q D hD α hα1
  refine ⟨p, c, M, C, hp, hp1, hc, hM, hC, ?_⟩
  intro Ω _ P _ h hh lam R hlam hlam1 hR z₀
  let mesh := TwoScale.Mesh.scaleMesh lam R z₀
  let base := scaleBase lam R α hlam hR
  let bad : Set Ω := {ω | ∃ z ∈ mesh,
    (LQGMetric.Blueprint.countOcc
      (fun k => {ω | h ω ∈ TwoScale.Ratio.rawRatioEvent D z
        (TwoScale.Ratio.ratioRadius base k)
        (ENNReal.ofReal M * ENNReal.ofReal M)})
      (scaleCount lam α) ω : ℝ) <
        (1 / 2 : ℝ) * scaleCount lam α}
  let conull : Set Ω := {ω |
    BiLipschitz.Barrier.Barrier (D (h ω)) ∧
    (D (h ω)).IsLengthSpace ∧
    (∀ z ∈ mesh, ∀ k : ℕ,
      aroundDist (D (h ω))
        (BiLipschitz.OneScale.crossingAt z (TwoScale.Ratio.ratioRadius base k)) ≠ ∞)}
  have hQ : 0 < Q := Positivity.FromAxioms.axpos ξ Q D hD
  have hB := BiLipschitz.Barrier.ae_barrier hD hQ P h hh
  have hL := hD.2.1 P h
    (LQGMetric.GM.isGFFPlusCont_of_isWholePlaneGFF hh.1)
  have hF := TwoScale.Ratio.ae_finite_mesh_ratio_costs_pos_finite
    P h hh ξ Q D hD mesh base
  have hconull : ∀ᵐ ω ∂P, ω ∈ conull := by
    filter_upwards [hB, hL, hF] with ω hb hl hf
    exact ⟨hb, hl, fun z hz k => (hf z hz k).2.2⟩
  have hzero : P conullᶜ = 0 := (mem_ae_iff).mp hconull
  have hsubset : {ω | ¬ (ω ∈ conull ∧ ω ∉ bad)} ⊆ conullᶜ ∪ bad := by
    intro ω hw
    by_cases hc : ω ∈ conull
    · exact Or.inr (by by_contra hn; exact hw ⟨hc, hn⟩)
    · exact Or.inl hc
  have hbound : P {ω | ¬ (ω ∈ conull ∧ ω ∉ bad)} ≤ P bad := by
    calc
      P {ω | ¬ (ω ∈ conull ∧ ω ∉ bad)} ≤ P (conullᶜ ∪ bad) := measure_mono hsubset
      _ ≤ P conullᶜ + P bad := measure_union_le _ _
      _ = P bad := by rw [hzero, zero_add]
  simpa only [conull, bad, mesh, base, Set.mem_ofPred_eq, and_assoc] using
    hbound.trans (htail P h hh lam R hlam hlam1 hR z₀)


end SupercriticalLQGUniqueness.Uniqueness.TwoScale.Carrier
