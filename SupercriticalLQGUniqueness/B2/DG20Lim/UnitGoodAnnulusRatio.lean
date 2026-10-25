import SupercriticalLQGUniqueness.B2.DG20Lim.UnitAnnulusCoords

 

set_option autoImplicit false
noncomputable section

open Set MeasureTheory ProbabilityTheory
open scoped ENNReal
open LQGMetric

namespace SupercriticalLQGUniqueness.B2.DG20Lim

 
private theorem ratio_tail_of_fixed_bounds
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (around across : Ω → ℝ≥0∞)
    (A B η : ℝ) (hA : 0 < A) (hB : 0 < B) (hη : 0 < η)
    (hupper : P {ω | ENNReal.ofReal A < around ω} ≤ ENNReal.ofReal (η / 2))
    (hlower : P {ω | across ω < ENNReal.ofReal B⁻¹} ≤ ENNReal.ofReal (η / 2)) :
    P {ω | ENNReal.ofReal (A * B) * across ω < around ω} ≤
      ENNReal.ofReal η := by
  have hsub : {ω | ENNReal.ofReal (A * B) * across ω < around ω} ⊆
      {ω | ENNReal.ofReal A < around ω} ∪
        {ω | across ω < ENNReal.ofReal B⁻¹} := by
    intro ω hbad
    by_cases hhigh : ENNReal.ofReal A < around ω
    · exact Or.inl hhigh
    · right
      by_contra hlow
      have hXa : around ω ≤ ENNReal.ofReal A := le_of_not_gt hhigh
      have hYb : ENNReal.ofReal B⁻¹ ≤ across ω := le_of_not_gt hlow
      have hprod : ENNReal.ofReal B * ENNReal.ofReal B⁻¹ = 1 := by
        rw [← ENNReal.ofReal_mul hB.le, mul_inv_cancel₀ hB.ne', ENNReal.ofReal_one]
      have hone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal B * across ω := by
        calc
          (1 : ℝ≥0∞) = ENNReal.ofReal B * ENNReal.ofReal B⁻¹ := hprod.symm
          _ ≤ ENNReal.ofReal B * across ω :=
            mul_le_mul_of_nonneg_left hYb zero_le
      have hgood : around ω ≤ ENNReal.ofReal (A * B) * across ω := by
        calc
          around ω ≤ ENNReal.ofReal A := hXa
          _ = ENNReal.ofReal A * 1 := (mul_one _).symm
          _ ≤ ENNReal.ofReal A * (ENNReal.ofReal B * across ω) :=
            mul_le_mul_of_nonneg_left hone zero_le
          _ = ENNReal.ofReal (A * B) * across ω := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul hA.le]
      exact (not_le_of_gt hbad) hgood
  calc
    P {ω | ENNReal.ofReal (A * B) * across ω < around ω}
        ≤ P ({ω | ENNReal.ofReal A < around ω} ∪
            {ω | across ω < ENNReal.ofReal B⁻¹}) := measure_mono hsub
    _ ≤ P {ω | ENNReal.ofReal A < around ω} +
          P {ω | across ω < ENNReal.ofReal B⁻¹} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (η / 2) + ENNReal.ofReal (η / 2) :=
      add_le_add hupper hlower
    _ = ENNReal.ofReal η := by
      have hhalf : 0 ≤ η / 2 := (half_pos hη).le
      rw [← ENNReal.ofReal_add hhalf hhalf]
      congr 1
      ring

 

theorem exists_unit_good_annulus_ratio_tail_of_inputs
    (hS4 : B2.Iface.DG20Section4)
    (hPerc : B2.Iface.DG20PercEstimate')
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : IsLFPPExponent ξ Q)
    (m : Ioi (0 : ℝ) → Ioi (0 : ℝ))
    (hm : ∀ ε, IsLFPPNormalizer ξ ε (m ε))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (X : Ioi (0 : ℝ) → Ω → C(ℂ, ℝ))
    (hX : ∀ ε, IsHeatSmoothing P h ε (X ε))
    (η : ℝ) (hη : 0 < η) :
    ∃ C ε₀ : ℝ, 0 < C ∧ 0 < ε₀ ∧
      ∀ ε : Ioo (0 : ℝ) 1, (ε : ℝ) < ε₀ →
        let D : Ω → ContMetric := fun ω =>
          normalizedContLFPP (ξ : ℝ)
            (m ⟨(ε : ℝ), ε.property.1⟩)
            (X ⟨(ε : ℝ), ε.property.1⟩ ω)
        P {ω | ENNReal.ofReal C *
          finiteCircleCoords (D ω) (unitInnerCircle, unitOuterCircle) <
          finiteAroundCoords (D ω) unitRatAnnulus} ≤
          ENNReal.ofReal η := by
  have hη2 : 0 < η / 2 := half_pos hη
  obtain ⟨A, hA, hupper⟩ :=
    exists_normalized_around_upper_tail_of_section4
      hS4 ξ Q hQ m hm P h hh X hX unitEuclideanAnnulus (η / 2) hη2
  obtain ⟨B, ε₀, hB, hε₀, hlower⟩ :=
    dg20_heat_circle_small_lower_of_perc hPerc ξ m hm P h hh X hX
      unitInnerCircle unitOuterCircle unitCircles_disjoint (η / 2) hη2
  refine ⟨A * B, ε₀, mul_pos hA hB, hε₀, ?_⟩
  intro ε hε
  dsimp
  let e : Ioi (0 : ℝ) := ⟨(ε : ℝ), ε.property.1⟩
  let D : Ω → ContMetric := fun ω => normalizedContLFPP (ξ : ℝ) (m e) (X e ω)
  let R : Ω → ℝ≥0∞ := fun ω => finiteAroundCoords (D ω) unitRatAnnulus
  let S : Ω → ℝ≥0∞ := fun ω =>
    finiteCircleCoords (D ω) (unitInnerCircle, unitOuterCircle)
  have hR : P {ω | ENNReal.ofReal A < R ω} ≤ ENNReal.ofReal (η / 2) := by
    calc
      P {ω | ENNReal.ofReal A < R ω} ≤
        P {ω | ENNReal.ofReal A <
          (D ω).aroundDist unitEuclideanAnnulus.toSet
            unitEuclideanAnnulus.innerBoundary
            unitEuclideanAnnulus.outerBoundary} := by
              apply measure_mono
              intro ω hω
              exact hω.trans_le (finiteAroundCoords_unit_le_euclidean (D ω))
      _ ≤ ENNReal.ofReal (η / 2) := by simpa only [D, e] using hupper ε
  have hS : P {ω | S ω < ENNReal.ofReal B⁻¹} ≤ ENNReal.ofReal (η / 2) := by
    simpa only [S, D, e] using hlower ε hε
  simpa only [D, R, S, e] using
    ratio_tail_of_fixed_bounds P R S A B η hA hB hη hR hS

end SupercriticalLQGUniqueness.B2.DG20Lim
