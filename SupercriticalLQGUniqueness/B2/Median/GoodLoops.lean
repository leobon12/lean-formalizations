import SupercriticalLQGUniqueness.B2.Iface.Statements
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.AnnulusIteration.Bridge

 







set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.Median

 


theorem exists_ratio_bound_of_twoSidedTight
    {Ω ι : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (X Y : ι → Ω → ℝ≥0∞)
    (hX : IsTwoSidedTight P X) (hY : IsTwoSidedTight P Y)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ i : ι,
      P {ω | ENNReal.ofReal C * Y i ω < X i ω} ≤ ENNReal.ofReal ε := by
  obtain ⟨A, hA, hAtail⟩ := hX.2 (ε / 2) (by positivity)
  obtain ⟨B, hB, hBtail⟩ := hY.2 (ε / 2) (by positivity)
  refine ⟨A * B, mul_pos hA hB, fun i => ?_⟩
  have hsub : {ω | ENNReal.ofReal (A * B) * Y i ω < X i ω} ⊆
      {ω | ENNReal.ofReal A < X i ω} ∪
        {ω | Y i ω < ENNReal.ofReal B⁻¹} := by
    intro ω hbad
    by_cases hhigh : ENNReal.ofReal A < X i ω
    · exact Or.inl hhigh
    · right
      by_contra hlow
      have hXa : X i ω ≤ ENNReal.ofReal A := le_of_not_gt hhigh
      have hYb : ENNReal.ofReal B⁻¹ ≤ Y i ω := le_of_not_gt hlow
      have hprod : ENNReal.ofReal B * ENNReal.ofReal B⁻¹ = 1 := by
        rw [← ENNReal.ofReal_mul hB.le, mul_inv_cancel₀ hB.ne', ENNReal.ofReal_one]
      have hone : (1 : ℝ≥0∞) ≤ ENNReal.ofReal B * Y i ω := by
        calc
          (1 : ℝ≥0∞) = ENNReal.ofReal B * ENNReal.ofReal B⁻¹ := hprod.symm
          _ ≤ ENNReal.ofReal B * Y i ω := mul_le_mul_of_nonneg_left hYb zero_le
      have hgood : X i ω ≤ ENNReal.ofReal (A * B) * Y i ω := by
        calc
          X i ω ≤ ENNReal.ofReal A := hXa
          _ = ENNReal.ofReal A * 1 := (mul_one _).symm
          _ ≤ ENNReal.ofReal A * (ENNReal.ofReal B * Y i ω) :=
            mul_le_mul_of_nonneg_left hone zero_le
          _ = ENNReal.ofReal (A * B) * Y i ω := by
            rw [← mul_assoc, ← ENNReal.ofReal_mul hA.le]
      exact (not_le_of_gt hbad) hgood
  calc
    P {ω | ENNReal.ofReal (A * B) * Y i ω < X i ω}
        ≤ P ({ω | ENNReal.ofReal A < X i ω} ∪
            {ω | Y i ω < ENNReal.ofReal B⁻¹}) := measure_mono hsub
    _ ≤ P {ω | ENNReal.ofReal A < X i ω} +
          P {ω | Y i ω < ENNReal.ofReal B⁻¹} := measure_union_le _ _
    _ ≤ ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
      add_le_add (hAtail i).1 (hBtail i).2
    _ = ENNReal.ofReal ε := by
      have hhalf : 0 ≤ ε / 2 := (div_pos hε (by norm_num)).le
      rw [← ENNReal.ofReal_add hhalf hhalf]
      congr 1
      ring

 


theorem exists_around_across_ratio_bound_at_origin
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (ξ : Set.Ioi (0 : ℝ))
    (D : LQGMetric.DistC → LSCMetric)
    (c : Set.Ioi (0 : ℝ) → Set.Ioi (0 : ℝ))
    (hweak : B2.Iface.IsPfeWeakMetric ξ D c)
    (h : Ω → LQGMetric.DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (A : EuclideanAnnulus) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : Set.Ioi (0 : ℝ),
      P {ω | ENNReal.ofReal C * acrossDist (D (h ω)) (A.dilate r r.2) <
        aroundDist (D (h ω)) (A.dilate r r.2)} ≤ ENNReal.ofReal ε := by
  obtain ⟨_, _, _, _, _, _, htight⟩ := hweak
  let av : Set.Ioi (0 : ℝ) → Ω → ℝ :=
    fun r ω => LQGMetric.circleAvg (h ω) (r : ℝ) 0
  have hav : ∀ r : Set.Ioi (0 : ℝ), ∀ᵐ ω ∂P,
      IsCircleAverage (h ω) r 0 (av r ω) := by
    intro r
    exact Uniqueness.Toolkit.AnnulusIteration.ae_isCircleAverage_circleAvg hh.1 r 0
  obtain ⟨hAcross, hAround⟩ := htight P h hh av hav A
  let k : Set.Ioi (0 : ℝ) → Ω → ℝ≥0∞ := fun r ω =>
    ENNReal.ofReal ((c r : ℝ)⁻¹ * Real.exp (-((ξ : ℝ) * av r ω)))
  obtain ⟨C, hC, hprob⟩ := exists_ratio_bound_of_twoSidedTight P
    (fun r ω => k r ω * aroundDist (D (h ω)) (A.dilate r r.2))
    (fun r ω => k r ω * acrossDist (D (h ω)) (A.dilate r r.2))
    hAround hAcross ε hε
  refine ⟨C, hC, fun r => ?_⟩
  have hset :
      {ω | ENNReal.ofReal C * acrossDist (D (h ω)) (A.dilate r r.2) <
        aroundDist (D (h ω)) (A.dilate r r.2)} =
      {ω | ENNReal.ofReal C *
        (k r ω * acrossDist (D (h ω)) (A.dilate r r.2)) <
          k r ω * aroundDist (D (h ω)) (A.dilate r r.2)} := by
    ext ω
    have hkpos : 0 < (c r : ℝ)⁻¹ * Real.exp (-((ξ : ℝ) * av r ω)) :=
      mul_pos (inv_pos.mpr (c r).property) (Real.exp_pos _)
    have hk0 : k r ω ≠ 0 := (ENNReal.ofReal_pos.mpr hkpos).ne'
    have hkTop : k r ω ≠ ∞ := ENNReal.ofReal_ne_top
    change ENNReal.ofReal C * acrossDist (D (h ω)) (A.dilate r r.2) <
        aroundDist (D (h ω)) (A.dilate r r.2) ↔
      ENNReal.ofReal C *
        (k r ω * acrossDist (D (h ω)) (A.dilate r r.2)) <
          k r ω * aroundDist (D (h ω)) (A.dilate r r.2)
    rw [show ENNReal.ofReal C *
          (k r ω * acrossDist (D (h ω)) (A.dilate r r.2)) =
        (ENNReal.ofReal C * acrossDist (D (h ω)) (A.dilate r r.2)) *
          k r ω by ac_rfl,
      mul_comm (k r ω) (aroundDist (D (h ω)) (A.dilate r r.2)),
      ENNReal.mul_lt_mul_iff_left hk0 hkTop]
  rw [hset]
  exact hprob r

end SupercriticalLQGUniqueness.B2.Median
