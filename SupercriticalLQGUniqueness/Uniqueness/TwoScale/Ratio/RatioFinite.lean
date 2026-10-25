import SupercriticalLQGUniqueness.Uniqueness.TwoScale.Ratio.RatioMesh




 
set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.Ratio

theorem ae_pos_finite_of_twoSidedTight
    {Ω ι : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ι → Ω → ℝ≥0∞) (hX : IsTwoSidedTight P X) (i : ι) :
    ∀ᵐ ω ∂P, X i ω ≠ 0 ∧ X i ω ≠ ∞ := by
  have hzero : P {ω | X i ω = 0} = 0 := by
    apply le_antisymm ?_ bot_le
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    have hεreal : 0 < (ε : ℝ) := by exact_mod_cast hε
    obtain ⟨M, hM, htail⟩ := hX.2 (ε : ℝ) hεreal
    have hMpos : 0 < M⁻¹ := inv_pos.mpr hM
    have hsub : {ω | X i ω = 0} ⊆ {ω | X i ω < ENNReal.ofReal M⁻¹} := by
      intro ω hω
      change X i ω = 0 at hω
      change X i ω < ENNReal.ofReal M⁻¹
      rw [hω]
      exact ENNReal.ofReal_pos.mpr hMpos
    simpa only [bot_eq_zero, zero_add, ENNReal.ofReal_coe_nnreal] using
      (measure_mono hsub).trans (htail i).2
  have htop : P {ω | X i ω = ∞} = 0 := by
    apply le_antisymm ?_ bot_le
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    have hεreal : 0 < (ε : ℝ) := by exact_mod_cast hε
    obtain ⟨M, _, htail⟩ := hX.2 (ε : ℝ) hεreal
    have hsub : {ω | X i ω = ∞} ⊆ {ω | ENNReal.ofReal M < X i ω} := by
      intro ω hω
      change X i ω = ∞ at hω
      change ENNReal.ofReal M < X i ω
      rw [hω]
      exact ENNReal.ofReal_lt_top
    simpa only [bot_eq_zero, zero_add, ENNReal.ofReal_coe_nnreal] using
      (measure_mono hsub).trans (htail i).1
  have hz : ∀ᵐ ω ∂P, X i ω ≠ 0 := (measure_eq_zero_iff_ae_notMem).mp hzero
  have ht : ∀ᵐ ω ∂P, X i ω ≠ ∞ := (measure_eq_zero_iff_ae_notMem).mp htop
  filter_upwards [hz, ht] with ω hz' ht'
  exact ⟨hz', ht'⟩

theorem pos_finite_of_scaled (n x : ℝ≥0∞) (hn0 : n ≠ 0)
    (hscaled : n * x ≠ 0 ∧ n * x ≠ ∞) :
    x ≠ 0 ∧ x ≠ ∞ := by
  constructor
  · intro hx
    exact hscaled.1 (by rw [hx, mul_zero])
  · intro hx
    exact hscaled.2 (by rw [hx, ENNReal.mul_top hn0])

theorem ae_origin_ratio_costs_pos_finite
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → LQGMetric.DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ)
    (D : LQGMetric.DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (base : Ioi (0 : ℝ)) :
    ∀ᵐ ω ∂P, ∀ k : ℕ,
      (acrossDist (D (h ω)) (BiLipschitz.OneScale.crossingAt 0 (ratioRadius base k)) ≠ 0 ∧
        acrossDist (D (h ω)) (BiLipschitz.OneScale.crossingAt 0 (ratioRadius base k)) ≠ ∞) ∧
      (aroundDist (D (h ω)) (BiLipschitz.OneScale.crossingAt 0 (ratioRadius base k)) ≠ 0 ∧
        aroundDist (D (h ω)) (BiLipschitz.OneScale.crossingAt 0 (ratioRadius base k)) ≠ ∞) := by
  have hV := hD.tightness P h hh (fun r ω => LQGMetric.circleAvg (h ω) r 0)
    (fun r => ae_isCircleAverage_old hh.1 r 0) BiLipschitz.OneScale.crossingShape
  have hVa : IsTwoSidedTight P
      (fun r ω => TwoScale.RatioMarginal.normAcross ξ Q D (h ω) BiLipschitz.OneScale.crossingShape r) := hV.1
  have hVr : IsTwoSidedTight P
      (fun r ω => TwoScale.RatioMarginal.normAround ξ Q D (h ω) BiLipschitz.OneScale.crossingShape r) := hV.2
  apply ae_all_iff.mpr
  intro k
  let r := ratioRadius base k
  have ha := ae_pos_finite_of_twoSidedTight P
    (fun r ω => TwoScale.RatioMarginal.normAcross ξ Q D (h ω) BiLipschitz.OneScale.crossingShape r) hVa r
  have hr := ae_pos_finite_of_twoSidedTight P
    (fun r ω => TwoScale.RatioMarginal.normAround ξ Q D (h ω) BiLipschitz.OneScale.crossingShape r) hVr r
  filter_upwards [ha, hr] with ω haω hrω
  let n : ℝ≥0∞ := ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ) * Q)) *
    Real.exp (-((ξ : ℝ) * LQGMetric.circleAvg (h ω) r 0)))
  have hnreal : 0 < (r : ℝ) ^ (-((ξ : ℝ) * Q)) *
      Real.exp (-((ξ : ℝ) * LQGMetric.circleAvg (h ω) r 0)) :=
    mul_pos (Real.rpow_pos_of_pos r.2 _) (Real.exp_pos _)
  have hn0 : n ≠ 0 := (ENNReal.ofReal_pos.mpr hnreal).ne'
  have hshape : BiLipschitz.OneScale.crossingAt 0 r =
      BiLipschitz.OneScale.crossingShape.dilate r r.2 := by
    unfold BiLipschitz.OneScale.crossingAt
    generalize hA : BiLipschitz.OneScale.crossingShape.dilate r r.2 = A
    cases A with
    | mk val hA' =>
      rcases val with ⟨z, inner, outer⟩
      apply Subtype.ext
      simp only [Positivity.Witnesses.annulusTranslate, EuclideanAnnulus.center,
        EuclideanAnnulus.innerRadius, EuclideanAnnulus.outerRadius, add_zero]
  have ha' : n * acrossDist (D (h ω)) (BiLipschitz.OneScale.crossingAt 0 r) ≠ 0 ∧
      n * acrossDist (D (h ω)) (BiLipschitz.OneScale.crossingAt 0 r) ≠ ∞ := by
    simpa only [TwoScale.RatioMarginal.normAcross, hshape] using haω
  have hr' : n * aroundDist (D (h ω)) (BiLipschitz.OneScale.crossingAt 0 r) ≠ 0 ∧
      n * aroundDist (D (h ω)) (BiLipschitz.OneScale.crossingAt 0 r) ≠ ∞ := by
    simpa only [TwoScale.RatioMarginal.normAround, hshape] using hrω
  exact ⟨pos_finite_of_scaled n _ hn0 ha',
    pos_finite_of_scaled n _ hn0 hr'⟩


end SupercriticalLQGUniqueness.Uniqueness.TwoScale.Ratio
