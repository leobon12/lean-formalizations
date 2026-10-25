import SupercriticalLQGUniqueness.Uniqueness.TwoScale.Mesh.MeshEvent
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.Carrier.ScaleNumerics




 





set_option autoImplicit false
noncomputable section

open Set MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.Carrier

open LQGMetric (DistC)

 

theorem scaleMesh_ratio_bad_tail_polynomial
    (ξ : Ioi (0 : ℝ)) (Q : ℝ)
    (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (α : ℝ) (hα1 : α < 1) :
    ∃ p c M C : ℝ, 0 < p ∧ p < 1 ∧ 0 < c ∧ 1 ≤ M ∧ 0 < C ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → DistC),
        IsNormalizedWholePlaneGFF h P →
        ∀ (lam R : ℝ) (hlam : 0 < lam), lam < 1 → (hR : 0 < R) → ∀ (z₀ : ℂ),
          P {ω | ∃ z ∈ TwoScale.Mesh.scaleMesh lam R z₀,
            (LQGMetric.Blueprint.countOcc
              (fun k => {ω | h ω ∈ TwoScale.Ratio.rawRatioEvent D z
                (TwoScale.Ratio.ratioRadius (scaleBase lam R α hlam hR) k)
                (ENNReal.ofReal M * ENNReal.ofReal M)})
              (scaleCount lam α) ω : ℝ) <
                (1 / 2 : ℝ) * scaleCount lam α} ≤
            ENNReal.ofReal (C * lam ^ (4 : ℕ)) := by
  obtain ⟨p, c, M, hp0, hp1, hc, hM, htail⟩ :=
    TwoScale.Mesh.scaleMesh_ratio_bad_tail_real ξ Q D hD
      (countRate α) (countRate_pos hα1)
  let C : ℝ := 729 * c * Real.exp (countRate α)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨p, c, M, C, hp0, hp1, hc, hM, hC, ?_⟩
  intro Ω _ P _ h hh lam R hlam hlam1 hR z₀
  have hbound := htail P h hh lam R hlam hlam1.le hR z₀
    (scaleBase lam R α hlam hR) (scaleCount lam α)
  calc
    P {ω | ∃ z ∈ TwoScale.Mesh.scaleMesh lam R z₀,
      (LQGMetric.Blueprint.countOcc
        (fun k => {ω | h ω ∈ TwoScale.Ratio.rawRatioEvent D z
          (TwoScale.Ratio.ratioRadius (scaleBase lam R α hlam hR) k)
          (ENNReal.ofReal M * ENNReal.ofReal M)})
        (scaleCount lam α) ω : ℝ) <
          (1 / 2 : ℝ) * scaleCount lam α} ≤
        ENNReal.ofReal ((27 / lam) ^ 2 *
          (c * Real.exp (-countRate α * (scaleCount lam α : ℝ)))) := hbound
    _ ≤ ENNReal.ofReal (C * lam ^ (4 : ℕ)) :=
      ENNReal.ofReal_le_ofReal (mesh_count_tail_le_pow_four hlam hlam1 hα1 hc.le)


end SupercriticalLQGUniqueness.Uniqueness.TwoScale.Carrier
