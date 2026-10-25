import SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3.TightNonzero
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.RatioMarginal.OneAnnulus




 


set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3

theorem ae_normCosts_pos_finite_at
    (μ : Measure LQGMetric.DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : LQGMetric.DistC → LQGMetric.DistC) μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : LQGMetric.DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (A : EuclideanAnnulus)
    (z : ℂ) (r : Ioi (0 : ℝ)) :
    ∀ᵐ g ∂μ, 0 < TwoScale.RatioMarginal.normAcrossAt ξ Q D g A z r ∧
      TwoScale.RatioMarginal.normAcrossAt ξ Q D g A z r < ⊤ ∧
      0 < TwoScale.RatioMarginal.normAroundAt ξ Q D g A z r ∧
      TwoScale.RatioMarginal.normAroundAt ξ Q D g A z r < ⊤ := by
  let hz : LQGMetric.DistC → LQGMetric.DistC := fun g =>
    LQGMetric.addConst (translateDist z g) (-LQGMetric.circleAvg g 1 z)
  have hhz : IsNormalizedWholePlaneGFF hz μ :=
    normalized_translate_sub_circleAvg hμ z
  have hV := hD.tightness μ hz hhz
    (fun t g => LQGMetric.circleAvg (hz g) t 0)
    (fun t => ae_isCircleAverage_old hhz.1 t 0) A
  have hC := ae_pos_lt_top_of_twoSidedTight μ
    (fun t g => TwoScale.RatioMarginal.normAcross ξ Q D (hz g) A t) hV.1 r
  have hA := ae_pos_lt_top_of_twoSidedTight μ
    (fun t g => TwoScale.RatioMarginal.normAround ξ Q D (hz g) A t) hV.2 r
  have hcross := Positivity.Witnesses.ae_normalized_across_translate μ id hμ ξ Q D hD A z r
  have haround := BiLipschitz.OneScale.ae_normalized_around_translate μ id hμ ξ Q D hD A z r
  filter_upwards [hC, hA, hcross, haround] with g hc ha hx hy
  change TwoScale.RatioMarginal.normAcross ξ Q D (hz g) A r =
    TwoScale.RatioMarginal.normAcrossAt ξ Q D g A z r at hx
  change TwoScale.RatioMarginal.normAround ξ Q D (hz g) A r =
    TwoScale.RatioMarginal.normAroundAt ξ Q D g A z r at hy
  rw [hx] at hc
  rw [hy] at ha
  exact ⟨hc.1, hc.2, ha.1, ha.2⟩

theorem ae_rawCosts_pos_finite_at
    (μ : Measure LQGMetric.DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : LQGMetric.DistC → LQGMetric.DistC) μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : LQGMetric.DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (A : EuclideanAnnulus)
    (z : ℂ) (r : Ioi (0 : ℝ)) :
    ∀ᵐ g ∂μ, 0 < acrossDist (D g) (Positivity.Witnesses.annulusTranslate (A.dilate r r.2) z) ∧
      acrossDist (D g) (Positivity.Witnesses.annulusTranslate (A.dilate r r.2) z) < ⊤ ∧
      0 < aroundDist (D g) (Positivity.Witnesses.annulusTranslate (A.dilate r r.2) z) ∧
      aroundDist (D g) (Positivity.Witnesses.annulusTranslate (A.dilate r r.2) z) < ⊤ := by
  filter_upwards [ae_normCosts_pos_finite_at μ hμ ξ Q D hD A z r] with g hg
  let n : ℝ≥0∞ := ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ) * Q)) *
    Real.exp (-((ξ : ℝ) * LQGMetric.circleAvg g r z)))
  have hn : 0 < n := ENNReal.ofReal_pos.mpr
    (mul_pos (Real.rpow_pos_of_pos r.2 _) (Real.exp_pos _))
  have hn0 : n ≠ 0 := hn.ne'
  change 0 < n * acrossDist (D g) (Positivity.Witnesses.annulusTranslate (A.dilate r r.2) z) ∧
    n * acrossDist (D g) (Positivity.Witnesses.annulusTranslate (A.dilate r r.2) z) < ⊤ ∧
    0 < n * aroundDist (D g) (Positivity.Witnesses.annulusTranslate (A.dilate r r.2) z) ∧
    n * aroundDist (D g) (Positivity.Witnesses.annulusTranslate (A.dilate r r.2) z) < ⊤ at hg
  exact ⟨(ENNReal.mul_pos_iff.mp hg.1).2,
    ENNReal.lt_top_of_mul_ne_top_right hg.2.1.ne hn0,
    (ENNReal.mul_pos_iff.mp hg.2.2.1).2,
    ENNReal.lt_top_of_mul_ne_top_right hg.2.2.2.ne hn0⟩

end SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3
