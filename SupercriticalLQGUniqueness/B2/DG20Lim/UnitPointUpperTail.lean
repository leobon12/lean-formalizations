import SupercriticalLQGUniqueness.B2.DG20Lim.NormalizedPointCrossUpper

 


set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal
open LQGMetric LQGMetric.DDDF

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem exists_unit_point_upper_tail_of_section4
    (hS4 : B2.Iface.DG20Section4)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ ε, IsHeatSmoothing P h ε (X ε))
    (η : ℝ) (hη : 0 < η) :
    ∃ M : ℝ, 0 < M ∧ ∀ δ : Ioo (0 : ℝ) 1,
      P {ω | ENNReal.ofReal M <
        edist ((normalizedContLFPP (ξ : ℝ)
          (m ⟨δ, δ.property.1⟩) (X ⟨δ, δ.property.1⟩ ω)).pt 0)
          ((normalizedContLFPP (ξ : ℝ)
            (m ⟨δ, δ.property.1⟩) (X ⟨δ, δ.property.1⟩ ω)).pt 1)} ≤
        ENNReal.ofReal η := by
  have hT := (hS4 ξ Q hQ m hm).1 P h hh X hX
    (⟨univ, isOpen_univ⟩ : TopologicalSpace.Opens ℂ)
    isConnected_univ (0 : ℂ) (1 : ℂ)
    (mem_univ _) (mem_univ _) (by norm_num : (0 : ℂ) ≠ 1)
  obtain ⟨M, hM, htail⟩ := hT.2 η hη
  refine ⟨M, hM, ?_⟩
  intro δ
  calc
    P {ω | ENNReal.ofReal M <
      edist ((normalizedContLFPP (ξ : ℝ)
        (m ⟨δ, δ.property.1⟩) (X ⟨δ, δ.property.1⟩ ω)).pt 0)
        ((normalizedContLFPP (ξ : ℝ)
          (m ⟨δ, δ.property.1⟩) (X ⟨δ, δ.property.1⟩ ω)).pt 1)}
      ≤ P {ω | ENNReal.ofReal M <
        ENNReal.ofReal (m ⟨δ, δ.property.1⟩ : ℝ)⁻¹ *
          crossLenIn (ξ : ℝ) (X ⟨δ, δ.property.1⟩ ω)
            univ {0} {1}} := by
          apply measure_mono
          intro ω hω
          exact hω.trans_le
            (normalizedContLFPP_point_le_crossLenIn
              (ξ : ℝ) (m ⟨δ, δ.property.1⟩)
              (X ⟨δ, δ.property.1⟩ ω) univ 0 1)
    _ ≤ ENNReal.ofReal η := by
      simpa only [TopologicalSpace.Opens.coe_mk] using (htail δ).1

end SupercriticalLQGUniqueness.B2.DG20Lim
