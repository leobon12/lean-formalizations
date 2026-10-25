import SupercriticalLQGUniqueness.Uniqueness.TwoScale.Ratio.RatioIteration




 
set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.Ratio

open LQGMetric (DistC addConst circleAvg)

private theorem ratio_iff_mul (n c x y : ℝ≥0∞)
    (hn0 : n ≠ 0) (hnTop : n ≠ ∞) :
    x ≤ c * y ↔ n * x ≤ c * (n * y) := by
  rw [mul_left_comm c n]
  simpa only [mul_comm n] using
    (ENNReal.mul_le_mul_iff_left hn0 hnTop (a := x) (b := c * y)).symm

theorem ratio_iff_normalized_at
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
    (g : DistC) (z : ℂ) (r : Ioi (0 : ℝ)) (c : ℝ≥0∞) :
    g ∈ rawRatioEvent D z r c ↔
      TwoScale.RatioMarginal.normAroundAt ξ Q D g BiLipschitz.OneScale.crossingShape z r ≤
        c * TwoScale.RatioMarginal.normAcrossAt ξ Q D g BiLipschitz.OneScale.crossingShape z r := by
  let n : ℝ≥0∞ := ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ) * Q)) *
    Real.exp (-((ξ : ℝ) * circleAvg g r z)))
  have hnreal : 0 < (r : ℝ) ^ (-((ξ : ℝ) * Q)) *
      Real.exp (-((ξ : ℝ) * circleAvg g r z)) :=
    mul_pos (Real.rpow_pos_of_pos r.2 _) (Real.exp_pos _)
  have hn0 : n ≠ 0 := (ENNReal.ofReal_pos.mpr hnreal).ne'
  have hnTop : n ≠ ∞ := ENNReal.ofReal_ne_top
  change aroundDist (D g) (BiLipschitz.OneScale.crossingAt z r) ≤
      c * acrossDist (D g) (BiLipschitz.OneScale.crossingAt z r) ↔
    n * aroundDist (D g) (BiLipschitz.OneScale.crossingAt z r) ≤
      c * (n * acrossDist (D g) (BiLipschitz.OneScale.crossingAt z r))
  exact ratio_iff_mul n c _ _ hn0 hnTop

theorem ratio_iff_normalized_origin
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric)
    (g : DistC) (r : Ioi (0 : ℝ)) (c : ℝ≥0∞) :
    g ∈ rawRatioEvent D 0 r c ↔
      TwoScale.RatioMarginal.normAround ξ Q D g BiLipschitz.OneScale.crossingShape r ≤
        c * TwoScale.RatioMarginal.normAcross ξ Q D g BiLipschitz.OneScale.crossingShape r := by
  have hzero : Positivity.Witnesses.annulusTranslate (BiLipschitz.OneScale.crossingShape.dilate r r.2) 0 =
      BiLipschitz.OneScale.crossingShape.dilate r r.2 := by
    generalize hA : BiLipschitz.OneScale.crossingShape.dilate r r.2 = A
    cases A with
    | mk val h =>
      rcases val with ⟨z, inner, outer⟩
      apply Subtype.ext
      simp only [Positivity.Witnesses.annulusTranslate, EuclideanAnnulus.center,
        EuclideanAnnulus.innerRadius, EuclideanAnnulus.outerRadius, add_zero]
  simpa only [ratio_iff_normalized_at, TwoScale.RatioMarginal.normAroundAt,
    TwoScale.RatioMarginal.normAcrossAt, TwoScale.RatioMarginal.normAround, TwoScale.RatioMarginal.normAcross,
    hzero]
    using ratio_iff_normalized_at ξ Q D g 0 r c

theorem ae_rawRatio_translate
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ)
    (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (z : ℂ) (r : Ioi (0 : ℝ)) (c : ℝ≥0∞) :
    ∀ᵐ ω ∂P,
      ((addConst (translateDist z (h ω)) (-circleAvg (h ω) 1 z)) ∈
        rawRatioEvent D 0 r c ↔ h ω ∈ rawRatioEvent D z r c) := by
  let hz : Ω → DistC := fun ω =>
    addConst (translateDist z (h ω)) (-circleAvg (h ω) 1 z)
  have hc := Positivity.Witnesses.ae_normalized_across_translate P h hh ξ Q D hD
    BiLipschitz.OneScale.crossingShape z r
  have ha := BiLipschitz.OneScale.ae_normalized_around_translate P h hh ξ Q D hD
    BiLipschitz.OneScale.crossingShape z r
  filter_upwards [hc, ha] with ω hcω haω
  have hc' : TwoScale.RatioMarginal.normAcross ξ Q D (hz ω) BiLipschitz.OneScale.crossingShape r =
      TwoScale.RatioMarginal.normAcrossAt ξ Q D (h ω) BiLipschitz.OneScale.crossingShape z r := hcω
  have ha' : TwoScale.RatioMarginal.normAround ξ Q D (hz ω) BiLipschitz.OneScale.crossingShape r =
      TwoScale.RatioMarginal.normAroundAt ξ Q D (h ω) BiLipschitz.OneScale.crossingShape z r := haω
  change hz ω ∈ rawRatioEvent D 0 r c ↔
    h ω ∈ rawRatioEvent D z r c
  rw [ratio_iff_normalized_origin ξ Q D (hz ω) r c,
    ratio_iff_normalized_at ξ Q D (h ω) z r c, hc', ha']

 
theorem ratio_iteration_count_tail_at
    (ξ : Ioi (0 : ℝ)) (Q : ℝ)
    (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (a : ℝ) (ha : 0 < a) :
    ∃ p c M : ℝ, 0 < p ∧ p < 1 ∧ 0 < c ∧ 1 ≤ M ∧
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P] (h : Ω → DistC),
        IsNormalizedWholePlaneGFF h P →
        ∀ (z : ℂ) (base : Ioi (0 : ℝ)) (K : ℕ),
          P {ω | (LQGMetric.Blueprint.countOcc
            (fun k => {ω | h ω ∈ rawRatioEvent D z (ratioRadius base k)
              (ENNReal.ofReal M * ENNReal.ofReal M)}) K ω : ℝ) <
              (1 / 2 : ℝ) * K} ≤
            ENNReal.ofReal (c * Real.exp (-a * K)) := by
  obtain ⟨p, c, M, hp0, hp1, hc, hM, htail⟩ :=
    ratio_iteration_count_tail ξ Q D hD a ha
  refine ⟨p, c, M, hp0, hp1, hc, hM, ?_⟩
  intro Ω _ P _ h hh z base K
  let hz : Ω → DistC := fun ω =>
    addConst (translateDist z (h ω)) (-circleAvg (h ω) 1 z)
  have hhz : IsNormalizedWholePlaneGFF hz P :=
    normalized_translate_sub_circleAvg hh z
  let rawOrigin : ℕ → Set Ω := fun k =>
    {ω | hz ω ∈ rawRatioEvent D 0 (ratioRadius base k)
      (ENNReal.ofReal M * ENNReal.ofReal M)}
  let rawAt : ℕ → Set Ω := fun k =>
    {ω | h ω ∈ rawRatioEvent D z (ratioRadius base k)
      (ENNReal.ofReal M * ENNReal.ofReal M)}
  have hae : ∀ᵐ ω ∂P, ∀ k, (ω ∈ rawOrigin k) ↔ (ω ∈ rawAt k) := by
    apply ae_all_iff.mpr
    intro k
    filter_upwards [ae_rawRatio_translate P h hh ξ Q D hD z
      (ratioRadius base k) (ENNReal.ofReal M * ENNReal.ofReal M)] with ω hω
    exact hω
  have heq : {ω | (LQGMetric.Blueprint.countOcc rawOrigin K ω : ℝ) <
      (1 / 2 : ℝ) * K} =ᵐ[P]
      {ω | (LQGMetric.Blueprint.countOcc rawAt K ω : ℝ) <
        (1 / 2 : ℝ) * K} := by
    filter_upwards [hae] with ω hω
    classical
    have hfilter : (Finset.Icc 1 K).filter (fun k => ω ∈ rawOrigin k) =
        (Finset.Icc 1 K).filter (fun k => ω ∈ rawAt k) := by
      ext k
      simp only [Finset.mem_filter]
      exact and_congr_right fun _ => hω k
    simp only [LQGMetric.Blueprint.countOcc, hfilter]
  have hbound := htail P hz hhz base K
  rw [measure_congr heq] at hbound
  exact hbound


end SupercriticalLQGUniqueness.Uniqueness.TwoScale.Ratio
