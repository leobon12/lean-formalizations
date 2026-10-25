import SupercriticalLQGUniqueness.Uniqueness.TwoScale.Ratio.RatioFinite




 
set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.Ratio

open LQGMetric (DistC addConst circleAvg)

private theorem crossingAt_zero_eq (r : Ioi (0 : ℝ)) :
    BiLipschitz.OneScale.crossingAt 0 r = BiLipschitz.OneScale.crossingShape.dilate r r.2 := by
  unfold BiLipschitz.OneScale.crossingAt
  generalize hA : BiLipschitz.OneScale.crossingShape.dilate r r.2 = A
  cases A with
  | mk val hA' =>
    rcases val with ⟨z, inner, outer⟩
    apply Subtype.ext
    simp only [Positivity.Witnesses.annulusTranslate, EuclideanAnnulus.center,
      EuclideanAnnulus.innerRadius, EuclideanAnnulus.outerRadius, add_zero]

private theorem scaled_pos_finite (n x : ℝ≥0∞)
    (hn0 : n ≠ 0) (hnTop : n ≠ ∞)
    (hx0 : x ≠ 0) (hxTop : x ≠ ∞) :
    n * x ≠ 0 ∧ n * x ≠ ∞ :=
  ⟨(ENNReal.mul_pos hn0 hx0).ne', ENNReal.mul_ne_top hnTop hxTop⟩

theorem ae_ratio_costs_pos_finite_at
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ)
    (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (z : ℂ) (base : Ioi (0 : ℝ)) :
    ∀ᵐ ω ∂P, ∀ k : ℕ,
      (acrossDist (D (h ω)) (BiLipschitz.OneScale.crossingAt z (ratioRadius base k)) ≠ 0 ∧
        acrossDist (D (h ω)) (BiLipschitz.OneScale.crossingAt z (ratioRadius base k)) ≠ ∞) ∧
      (aroundDist (D (h ω)) (BiLipschitz.OneScale.crossingAt z (ratioRadius base k)) ≠ 0 ∧
        aroundDist (D (h ω)) (BiLipschitz.OneScale.crossingAt z (ratioRadius base k)) ≠ ∞) := by
  let hz : Ω → DistC := fun ω =>
    addConst (translateDist z (h ω)) (-circleAvg (h ω) 1 z)
  have hhz : IsNormalizedWholePlaneGFF hz P :=
    normalized_translate_sub_circleAvg hh z
  have hOrig := ae_origin_ratio_costs_pos_finite P hz hhz ξ Q D hD base
  have hCross : ∀ᵐ ω ∂P, ∀ k : ℕ,
      TwoScale.RatioMarginal.normAcross ξ Q D (hz ω) BiLipschitz.OneScale.crossingShape (ratioRadius base k) =
      TwoScale.RatioMarginal.normAcrossAt ξ Q D (h ω) BiLipschitz.OneScale.crossingShape z
        (ratioRadius base k) := by
    apply ae_all_iff.mpr
    intro k
    exact Positivity.Witnesses.ae_normalized_across_translate P h hh ξ Q D hD
      BiLipschitz.OneScale.crossingShape z (ratioRadius base k)
  have hAround : ∀ᵐ ω ∂P, ∀ k : ℕ,
      TwoScale.RatioMarginal.normAround ξ Q D (hz ω) BiLipschitz.OneScale.crossingShape (ratioRadius base k) =
      TwoScale.RatioMarginal.normAroundAt ξ Q D (h ω) BiLipschitz.OneScale.crossingShape z
        (ratioRadius base k) := by
    apply ae_all_iff.mpr
    intro k
    exact BiLipschitz.OneScale.ae_normalized_around_translate P h hh ξ Q D hD
      BiLipschitz.OneScale.crossingShape z (ratioRadius base k)
  filter_upwards [hOrig, hCross, hAround] with ω ho hc ha
  intro k
  let r := ratioRadius base k
  let n0 : ℝ≥0∞ := ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ) * Q)) *
    Real.exp (-((ξ : ℝ) * circleAvg (hz ω) r 0)))
  let nz : ℝ≥0∞ := ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ) * Q)) *
    Real.exp (-((ξ : ℝ) * circleAvg (h ω) r z)))
  have hn0real : 0 < (r : ℝ) ^ (-((ξ : ℝ) * Q)) *
      Real.exp (-((ξ : ℝ) * circleAvg (hz ω) r 0)) :=
    mul_pos (Real.rpow_pos_of_pos r.2 _) (Real.exp_pos _)
  have hnzreal : 0 < (r : ℝ) ^ (-((ξ : ℝ) * Q)) *
      Real.exp (-((ξ : ℝ) * circleAvg (h ω) r z)) :=
    mul_pos (Real.rpow_pos_of_pos r.2 _) (Real.exp_pos _)
  have hn00 : n0 ≠ 0 := (ENNReal.ofReal_pos.mpr hn0real).ne'
  have hn0Top : n0 ≠ ∞ := ENNReal.ofReal_ne_top
  have hnz0 : nz ≠ 0 := (ENNReal.ofReal_pos.mpr hnzreal).ne'
  have hnzTop : nz ≠ ∞ := ENNReal.ofReal_ne_top
  have ho' := ho k
  have hA0 : TwoScale.RatioMarginal.normAcross ξ Q D (hz ω) BiLipschitz.OneScale.crossingShape r ≠ 0 ∧
      TwoScale.RatioMarginal.normAcross ξ Q D (hz ω) BiLipschitz.OneScale.crossingShape r ≠ ∞ := by
    change n0 * acrossDist (D (hz ω)) (BiLipschitz.OneScale.crossingShape.dilate r r.2) ≠ 0 ∧
      n0 * acrossDist (D (hz ω)) (BiLipschitz.OneScale.crossingShape.dilate r r.2) ≠ ∞
    rw [← crossingAt_zero_eq r]
    exact scaled_pos_finite n0 _ hn00 hn0Top ho'.1.1 ho'.1.2
  have hR0 : TwoScale.RatioMarginal.normAround ξ Q D (hz ω) BiLipschitz.OneScale.crossingShape r ≠ 0 ∧
      TwoScale.RatioMarginal.normAround ξ Q D (hz ω) BiLipschitz.OneScale.crossingShape r ≠ ∞ := by
    change n0 * aroundDist (D (hz ω)) (BiLipschitz.OneScale.crossingShape.dilate r r.2) ≠ 0 ∧
      n0 * aroundDist (D (hz ω)) (BiLipschitz.OneScale.crossingShape.dilate r r.2) ≠ ∞
    rw [← crossingAt_zero_eq r]
    exact scaled_pos_finite n0 _ hn00 hn0Top ho'.2.1 ho'.2.2
  have hAz : nz * acrossDist (D (h ω)) (BiLipschitz.OneScale.crossingAt z r) ≠ 0 ∧
      nz * acrossDist (D (h ω)) (BiLipschitz.OneScale.crossingAt z r) ≠ ∞ := by
    change TwoScale.RatioMarginal.normAcrossAt ξ Q D (h ω) BiLipschitz.OneScale.crossingShape z r ≠ 0 ∧
      TwoScale.RatioMarginal.normAcrossAt ξ Q D (h ω) BiLipschitz.OneScale.crossingShape z r ≠ ∞
    rw [← hc k]
    exact hA0
  have hRz : nz * aroundDist (D (h ω)) (BiLipschitz.OneScale.crossingAt z r) ≠ 0 ∧
      nz * aroundDist (D (h ω)) (BiLipschitz.OneScale.crossingAt z r) ≠ ∞ := by
    change TwoScale.RatioMarginal.normAroundAt ξ Q D (h ω) BiLipschitz.OneScale.crossingShape z r ≠ 0 ∧
      TwoScale.RatioMarginal.normAroundAt ξ Q D (h ω) BiLipschitz.OneScale.crossingShape z r ≠ ∞
    rw [← ha k]
    exact hR0
  exact ⟨pos_finite_of_scaled nz _ hnz0 hAz,
    pos_finite_of_scaled nz _ hnz0 hRz⟩

theorem ae_finite_mesh_ratio_costs_pos_finite
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC)
    (hh : IsNormalizedWholePlaneGFF h P)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ)
    (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    (mesh : Finset ℂ) (base : Ioi (0 : ℝ)) :
    ∀ᵐ ω ∂P, ∀ z ∈ mesh, ∀ k : ℕ,
      (acrossDist (D (h ω)) (BiLipschitz.OneScale.crossingAt z (ratioRadius base k)) ≠ 0 ∧
        acrossDist (D (h ω)) (BiLipschitz.OneScale.crossingAt z (ratioRadius base k)) ≠ ∞) ∧
      (aroundDist (D (h ω)) (BiLipschitz.OneScale.crossingAt z (ratioRadius base k)) ≠ 0 ∧
        aroundDist (D (h ω)) (BiLipschitz.OneScale.crossingAt z (ratioRadius base k)) ≠ ∞) := by
  classical
  have hall : ∀ᵐ ω ∂P, ∀ z : {z : ℂ // z ∈ mesh}, ∀ k : ℕ,
      (acrossDist (D (h ω)) (BiLipschitz.OneScale.crossingAt z (ratioRadius base k)) ≠ 0 ∧
        acrossDist (D (h ω)) (BiLipschitz.OneScale.crossingAt z (ratioRadius base k)) ≠ ∞) ∧
      (aroundDist (D (h ω)) (BiLipschitz.OneScale.crossingAt z (ratioRadius base k)) ≠ 0 ∧
        aroundDist (D (h ω)) (BiLipschitz.OneScale.crossingAt z (ratioRadius base k)) ≠ ∞) := by
    apply ae_all_iff.mpr
    intro z
    exact ae_ratio_costs_pos_finite_at P h hh ξ Q D hD z.1 base
  filter_upwards [hall] with ω hω
  intro z hz k
  exact hω ⟨z, hz⟩ k


end SupercriticalLQGUniqueness.Uniqueness.TwoScale.Ratio
