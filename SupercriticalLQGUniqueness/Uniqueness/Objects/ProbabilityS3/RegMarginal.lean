import SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3.PosFiniteAt




 


set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3

private def baseAnn : EuclideanAnnulus :=
  ⟨(0, (1 : ℝ), 2), by norm_num, by norm_num⟩

private theorem baseAnn_at (w : ℂ) (s : Ioi (0 : ℝ)) :
    Positivity.Witnesses.annulusTranslate (baseAnn.dilate s s.2) w =
      (⟨(w, (s : ℝ), 2 * (s : ℝ)), s.2,
        by have hs : (0 : ℝ) < s := s.2; linarith only [hs]⟩ : EuclideanAnnulus) := by
  apply Subtype.ext
  simp [Positivity.Witnesses.annulusTranslate, EuclideanAnnulus.dilate, baseAnn,
    EuclideanAnnulus.center, EuclideanAnnulus.innerRadius,
    EuclideanAnnulus.outerRadius, mul_comm]

theorem exists_regGood_uniform
    (μ : Measure LQGMetric.DistC) [IsProbabilityMeasure μ]
    (hμ : IsNormalizedWholePlaneGFF (id : LQGMetric.DistC → LQGMetric.DistC) μ)
    (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : LQGMetric.DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ c : ℝ, 0 < c ∧ c < 1 ∧
      ∀ (C : Objects.CorrectedEvent.Constants), C.c_reg ≤ c → ∀ (w : ℂ) (s : Ioi (0 : ℝ)),
        ENNReal.ofReal p ≤ μ {g | Objects.CorrectedEvent.regGood C (D g) s w} := by
  obtain ⟨M, hM, hRatio⟩ := TwoScale.RatioMarginal.center_raw_ratio_uniform ξ Q D hD baseAnn p hp0 hp1
  let c : ℝ := (M * M + 1)⁻¹
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hden : 1 < M * M + 1 := by nlinarith [mul_pos hM0 hM0]
  have hc0 : 0 < c := inv_pos.mpr (by linarith)
  have hc1 : c < 1 := (inv_lt_one₀ (by linarith)).mpr hden
  refine ⟨c, hc0, hc1, ?_⟩
  intro C hCc w s
  have hraw := hRatio μ id hμ w s
  have hfin := ae_rawCosts_pos_finite_at μ hμ ξ Q D hD baseAnn w s
  have heq := ae_regGood_iff_standard_costs μ hμ ξ Q D hD C w s s.2
  have hsub : ∀ᵐ g ∂μ,
      g ∈ {g | aroundDist (D g) (Positivity.Witnesses.annulusTranslate (baseAnn.dilate s s.2) w) ≤
        (ENNReal.ofReal M * ENNReal.ofReal M) *
          acrossDist (D g) (Positivity.Witnesses.annulusTranslate (baseAnn.dilate s s.2) w)} →
      g ∈ {g | Objects.CorrectedEvent.regGood C (D g) s w} := by
    filter_upwards [hfin, heq] with g hg he hratio
    rw [baseAnn_at w s] at hg hratio
    apply he.mpr
    refine ⟨hg.2.2.1, hg.2.2.2, hg.1, hg.2.1, ?_⟩
    have hcInv : (M * M + 1) ≤ C.c_reg⁻¹ := by
      have h := (inv_le_inv₀ hc0 C.regPos).2 hCc
      simpa only [c, inv_inv] using h
    have hMmul : ENNReal.ofReal M * ENNReal.ofReal M =
        ENNReal.ofReal (M * M) := (ENNReal.ofReal_mul hM0.le).symm
    have hlt : M * M ≤ C.c_reg⁻¹ := by linarith only [hcInv]
    calc
      aroundDist (D g) _ ≤
          ENNReal.ofReal (M * M) * acrossDist (D g) _ := by
            simpa only [hMmul] using hratio
      _ ≤ ENNReal.ofReal C.c_reg⁻¹ * acrossDist (D g) _ := by
        gcongr
  exact hraw.trans (measure_mono_ae hsub)

end SupercriticalLQGUniqueness.Uniqueness.Objects.ProbabilityS3
