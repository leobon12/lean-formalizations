import SupercriticalLQGUniqueness.B2.DG20Lim.PolarPointUpperTail
import SupercriticalLQGUniqueness.B2.DG20Lim.NormalizedAroundPointUpper

 

set_option autoImplicit false
noncomputable section

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open LQGMetric LQGMetric.DDDF

namespace SupercriticalLQGUniqueness.B2.DG20Lim

 

theorem exists_normalized_around_upper_tail_of_section4
    (hS4 : B2.Iface.DG20Section4)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ ε, IsHeatSmoothing P h ε (X ε))
    (A : EuclideanAnnulus) (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧
      ∀ ε : Ioo (0 : ℝ) 1,
        P {ω | ENNReal.ofReal C <
          (normalizedContLFPP (ξ : ℝ)
            (m ⟨(ε : ℝ), ε.property.1⟩)
            (X ⟨(ε : ℝ), ε.property.1⟩ ω)).aroundDist A.toSet
              A.innerBoundary A.outerBoundary} ≤
          ENNReal.ofReal η := by
  obtain ⟨z, w, M, hz, hw, hM, htail⟩ :=
    exists_polar_point_upper_tail_of_section4
      hS4 ξ Q hQ m hm P h hh X hX A η hη
  let C : ℝ := 6 * (M + 1)
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro ε
  let e : Ioi (0 : ℝ) := ⟨(ε : ℝ), ε.property.1⟩
  let N : Ω → ℝ≥0∞ := fun ω =>
    (normalizedContLFPP (ξ : ℝ) (m e) (X e ω)).aroundDist
      A.toSet A.innerBoundary A.outerBoundary
  let V : Fin 4 → Ω → ℝ≥0∞ := fun j ω =>
    ENNReal.ofReal ((m e : ℝ)⁻¹) *
      crossLenIn (ξ : ℝ) (X e ω)
        (B2.Strong.cfgOpens A j) {z j} {w j}
  have hsub : {ω | ENNReal.ofReal C < N ω} ⊆
      ⋃ j : Fin 4, {ω | ENNReal.ofReal M < V j ω} := by
    intro ω hbad
    by_contra hnot
    have hgood (j : Fin 4) : V j ω ≤ ENNReal.ofReal M := by
      exact le_of_not_gt (fun hj =>
        hnot (Set.mem_iUnion.mpr ⟨j, hj⟩))
    have hloop := normalizedContLFPP_aroundDist_lt_of_four_point_crossLe
      A (ξ : ℝ) (X e ω) (m e) z w hz hw M hM.le hgood
    exact (lt_asymm hbad hloop)
  change P {ω | ENNReal.ofReal C < N ω} ≤ ENNReal.ofReal η
  calc
    P {ω | ENNReal.ofReal C < N ω}
        ≤ P (⋃ j : Fin 4, {ω | ENNReal.ofReal M < V j ω}) :=
      measure_mono hsub
    _ ≤ ENNReal.ofReal η := by simpa only [V, e] using htail ε

end SupercriticalLQGUniqueness.B2.DG20Lim
