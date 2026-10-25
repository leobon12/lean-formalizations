import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.L34




 












set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36

open LQGMetric (DistC addConst restrictTo)

 

theorem across_le_of_crossing {D : LSCMetric} (hB : BiLipschitz.Barrier.Barrier D) (hL : D.IsLengthSpace)
    (A : EuclideanAnnulus) {x y : ℂ} (hx : ‖x - A.center‖ ≤ A.innerRadius)
    (hy : A.outerRadius ≤ ‖y - A.center‖) : acrossDist D A ≤ D (x, y) := by
  refine le_trans ?_ (BiLipschitz.Barrier.iInf_internal_le D hB hL A.2.2.le (subset_univ _) hx hy)
  refine le_iInf fun p => le_iInf fun h1 => le_iInf fun h2 => ?_
  refine (iInf₂_le_of_le _ ?_ (iInf₂_le _ ?_)).trans (BiLipschitz.Barrier.edist_le_internal' D univ p)
  · exact Metric.mem_sphere.mpr (by rw [dist_eq_norm]; exact h1)
  · exact Metric.mem_sphere.mpr (by rw [dist_eq_norm]; exact h2)

 
def innerCrossAnn (z : ℂ) (r : Ioi (0 : ℝ)) : EuclideanAnnulus :=
  ⟨(z, ((r : ℝ) / 2, 3 * (r : ℝ) / 4)), by
    have hr : (0 : ℝ) < r := r.2
    show 0 < (r : ℝ) / 2 ∧ (r : ℝ) / 2 < 3 * (r : ℝ) / 4
    constructor <;> linarith⟩

theorem middle_ge_min_across {D : LSCMetric} (hB : BiLipschitz.Barrier.Barrier D) (hL : D.IsLengthSpace)
    (z : ℂ) (r : Ioi (0 : ℝ)) :
    min (acrossDist D (innerCrossAnn z r)) (acrossDist D (outerAnn z r)) ≤
      OptimalConstants.Ratios.setDist D (TwoScale.S36Events.eventMiddle z r) (TwoScale.S36Events.eventBoundary z r) := by
  refine le_iInf₂ fun x hx => le_iInf₂ fun y hy => ?_
  obtain ⟨hx1, hx2⟩ := hx
  rw [Metric.mem_ball, dist_eq_norm] at hx1
  rw [Metric.mem_closedBall, not_le, dist_eq_norm] at hx2
  rcases hy with hy | hy
  · rw [Metric.mem_sphere, dist_eq_norm] at hy
    refine (min_le_left _ _).trans ?_
    rw [D.isExtMetric.2.2.1]
    exact across_le_of_crossing hB hL _ (by change ‖y - z‖ ≤ (r : ℝ) / 2; rw [hy])
      (by change 3 * (r : ℝ) / 4 ≤ ‖x - z‖; exact hx2.le)
  · rw [Metric.mem_sphere, dist_eq_norm] at hy
    refine (min_le_right _ _).trans ?_
    exact across_le_of_crossing hB hL _ (by change ‖x - z‖ ≤ 3 * (r : ℝ) / 2; exact hx1.le)
      (by change 2 * (r : ℝ) ≤ ‖y - z‖; rw [hy])

 

theorem le_mul_of_normed_le {n N X M : ℝ≥0∞} (hnN : N * n = 1) (h : n * X ≤ M) :
    X ≤ M * N := by
  calc
    X = N * n * X := by rw [hnN, one_mul]
    _ = N * (n * X) := mul_assoc _ _ _
    _ ≤ N * M := mul_le_mul' le_rfl h
    _ = M * N := mul_comm _ _

theorem mul_le_of_le_normed {n N X M : ℝ≥0∞} (hnN : N * n = 1) (h : M ≤ n * X) :
    M * N ≤ X := by
  calc
    M * N ≤ n * X * N := mul_le_mul' h le_rfl
    _ = X * (N * n) := by ring
    _ = X := by rw [hnN, mul_one]

theorem normalizer_mul (ξ Q : ℝ) (r : Ioi (0 : ℝ)) (c : ℝ) :
    ENNReal.ofReal ((r : ℝ) ^ (ξ * Q) * Real.exp (ξ * c)) *
      ENNReal.ofReal ((r : ℝ) ^ (-(ξ * Q)) * Real.exp (-(ξ * c))) = 1 := by
  have hr : (0 : ℝ) < r := r.2
  rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_one]
  congr 1
  rw [Real.rpow_neg hr.le, Real.exp_neg]
  have h1 : (r : ℝ) ^ (ξ * Q) ≠ 0 := (Real.rpow_pos_of_pos hr _).ne'
  have h2 : Real.exp (ξ * c) ≠ 0 := (Real.exp_pos _).ne'
  field_simp

 

theorem measurable_normAcrossAt (ξ : Ioi (0 : ℝ)) (Q : ℝ) {D : DistC → LSCMetric}
    (hD : Measurable D) (A : EuclideanAnnulus) (z : ℂ) (r : Ioi (0 : ℝ)) :
    Measurable fun g => TwoScale.RatioMarginal.normAcrossAt ξ Q D g A z r := by
  unfold TwoScale.RatioMarginal.normAcrossAt
  exact (measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul
    (LQGMetric.measurable_circleAvg_left _ _)).neg)).ennreal_ofReal.mul
    ((measurable_acrossDist _).comp hD)

theorem measurable_normAroundAt (ξ : Ioi (0 : ℝ)) (Q : ℝ) {D : DistC → LSCMetric}
    (hD : Measurable D) (A : EuclideanAnnulus) (z : ℂ) (r : Ioi (0 : ℝ)) :
    Measurable fun g => TwoScale.RatioMarginal.normAroundAt ξ Q D g A z r := by
  unfold TwoScale.RatioMarginal.normAroundAt
  exact (measurable_const.mul (Real.measurable_exp.comp (measurable_const.mul
    (LQGMetric.measurable_circleAvg_left _ _)).neg)).ennreal_ofReal.mul
    ((measurable_aroundDist_fixed _).comp hD)

 

 
def shortShape {q : Ioo (0 : ℝ) (1 / 100)} (a : Ioo (1 - (q : ℝ)) 1) : EuclideanAnnulus :=
  ⟨(0, ((a : ℝ), 1)), by
    have h1 := q.2.2
    have h2 := a.2.1
    have h3 := a.2.2
    constructor <;> linarith⟩

theorem shortShape_translate {q : Ioo (0 : ℝ) (1 / 100)} (a : Ioo (1 - (q : ℝ)) 1) (z : ℂ)
    (r : Ioi (0 : ℝ)) :
    Positivity.Witnesses.annulusTranslate ((shortShape a).dilate r r.2) z = shortAnn z r a := by
  apply Subtype.ext
  change (((r : ℝ) • (0 : ℂ) + z, ((r : ℝ) * a, (r : ℝ) * 1)) : ℂ × ℝ × ℝ) =
    (z, ((a : ℝ) * r, (r : ℝ)))
  rw [smul_zero, zero_add, mul_one, mul_comm]

 

theorem E4_prob (ξ : Ioi (0 : ℝ)) (Q : ℝ) (D : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D)
    {q : Ioo (0 : ℝ) (1 / 100)} (a : Ioo (1 - (q : ℝ)) 1) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ∃ K : Ioi (1 : ℝ), ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
      [IsProbabilityMeasure P] (h : Ω → DistC), IsNormalizedWholePlaneGFF h P →
      ∀ (z : ℂ) (r : Ioi (0 : ℝ)), P {ω | ¬ E4Prop (D (h ω)) z r a K} ≤ ENNReal.ofReal p := by
  obtain ⟨M, hM, hprob⟩ := TwoScale.RatioMarginal.center_raw_ratio_uniform ξ Q D hD (shortShape a) (1 - p)
    (by linarith) (by linarith)
  have hMM : (1 : ℝ) < M * M + 1 := by nlinarith
  refine ⟨⟨M * M + 1, hMM⟩, ?_⟩
  intro Ω _ P _ h hh z r
  set G : Set Ω := {ω | aroundDist (D (h ω))
      (Positivity.Witnesses.annulusTranslate ((shortShape a).dilate r r.2) z) ≤
    (ENNReal.ofReal M * ENNReal.ofReal M) *
      acrossDist (D (h ω)) (Positivity.Witnesses.annulusTranslate ((shortShape a).dilate r r.2) z)}
  have hGm : MeasurableSet G :=
    measurableSet_le ((measurable_aroundDist_fixed _).comp (hD.measurable.comp hh.1.measurable))
      (measurable_const.mul ((measurable_acrossDist _).comp
        (hD.measurable.comp hh.1.measurable)))
  have hsub : {ω | ¬ E4Prop (D (h ω)) z r a ⟨M * M + 1, hMM⟩} ⊆ Gᶜ := by
    intro ω hω hG
    apply hω
    change aroundDist (D (h ω)) (shortAnn z r a) ≤
      ENNReal.ofReal (M * M + 1) * acrossDist (D (h ω)) (shortAnn z r a)
    have hG' : aroundDist (D (h ω)) (shortAnn z r a) ≤
        (ENNReal.ofReal M * ENNReal.ofReal M) * acrossDist (D (h ω)) (shortAnn z r a) := by
      have h' : aroundDist (D (h ω))
          (Positivity.Witnesses.annulusTranslate ((shortShape a).dilate r r.2) z) ≤
          (ENNReal.ofReal M * ENNReal.ofReal M) *
            acrossDist (D (h ω)) (Positivity.Witnesses.annulusTranslate ((shortShape a).dilate r r.2) z) := hG
      rwa [shortShape_translate] at h'
    refine hG'.trans (mul_le_mul' ?_ le_rfl)
    rw [← ENNReal.ofReal_mul (by linarith)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  calc
    P {ω | ¬ E4Prop (D (h ω)) z r a ⟨M * M + 1, hMM⟩} ≤ P Gᶜ := measure_mono hsub
    _ = 1 - P G := prob_compl_eq_one_sub hGm
    _ ≤ 1 - ENNReal.ofReal (1 - p) := tsub_le_tsub_left (hprob P h hh z r) 1
    _ = ENNReal.ofReal p := by
      rw [ENNReal.ofReal_sub _ hp0.le, ENNReal.ofReal_one,
        ENNReal.sub_sub_cancel ENNReal.one_ne_top (ENNReal.ofReal_le_one.mpr hp1.le)]

 

def outerShape : EuclideanAnnulus := ⟨(0, ((3 : ℝ) / 2, 2)), by norm_num, by norm_num⟩

def innerShape : EuclideanAnnulus := ⟨(0, ((1 : ℝ) / 2, 3 / 4)), by norm_num, by norm_num⟩

theorem outerShape_translate (z : ℂ) (r : Ioi (0 : ℝ)) :
    Positivity.Witnesses.annulusTranslate (outerShape.dilate r r.2) z = outerAnn z r := by
  apply Subtype.ext
  change (((r : ℝ) • (0 : ℂ) + z, ((r : ℝ) * (3 / 2), (r : ℝ) * 2)) : ℂ × ℝ × ℝ) =
    (z, (3 * (r : ℝ) / 2, 2 * (r : ℝ)))
  rw [smul_zero, zero_add]
  congr 1
  congr 1 <;> ring

theorem innerShape_translate (z : ℂ) (r : Ioi (0 : ℝ)) :
    Positivity.Witnesses.annulusTranslate (innerShape.dilate r r.2) z = innerCrossAnn z r := by
  apply Subtype.ext
  change (((r : ℝ) • (0 : ℂ) + z, ((r : ℝ) * (1 / 2), (r : ℝ) * (3 / 4))) : ℂ × ℝ × ℝ) =
    (z, ((r : ℝ) / 2, 3 * (r : ℝ) / 4))
  rw [smul_zero, zero_add]
  congr 1
  congr 1 <;> ring

 


theorem E2_prob (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q) (D : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (θ : Ioi (0 : ℝ)) (Cm Cp : ℝ) (p : ℝ) (hp0 : 0 < p)
    (hp1 : p < 1) :
    ∃ M₁ M₂ : ℝ, 0 < M₁ ∧ 0 < M₂ ∧ ∀ (q : Ioo (0 : ℝ) (1 / 100)) (a : Ioo (1 - (q : ℝ)) 1),
      M₁ ≤ (1 - (a : ℝ))⁻¹ → M₂ ≤ Cm / (2 * Cp) * (q : ℝ) ^ (-(θ : ℝ)) →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (h : Ω → DistC), IsNormalizedWholePlaneGFF h P → ∀ (z : ℂ) (r : Ioi (0 : ℝ)),
        P {ω | ¬ ∀ c : ℝ, IsCircleAverage (h ω) r z c →
          E2Prop (D (h ω)) (ξ : ℝ) Q z r q a θ Cm Cp c} ≤ ENNReal.ofReal p := by
  obtain ⟨Mo, hMo, hpo⟩ := TwoScale.RatioMarginal.center_ratio_uniform ξ Q D hD outerShape (1 - p / 2)
    (by linarith) (by linarith)
  obtain ⟨Mi, hMi, hpi⟩ := TwoScale.RatioMarginal.center_ratio_uniform ξ Q D hD innerShape (1 - p / 2)
    (by linarith) (by linarith)
  have hMo0 : 0 < Mo := by linarith
  have hMi0 : 0 < Mi := by linarith
  have hmax0 : 0 < max Mo Mi := lt_max_of_lt_left hMo0
  refine ⟨Mo, Mo * max Mo Mi, hMo0, by positivity, ?_⟩
  intro q a ha hq Ω _ P _ h hh z r
  set Go : Set Ω := {ω | ENNReal.ofReal Mo⁻¹ ≤ TwoScale.RatioMarginal.normAcrossAt ξ Q D (h ω) outerShape z r ∧
    TwoScale.RatioMarginal.normAroundAt ξ Q D (h ω) outerShape z r ≤ ENNReal.ofReal Mo}
  set Gi : Set Ω := {ω | ENNReal.ofReal Mi⁻¹ ≤ TwoScale.RatioMarginal.normAcrossAt ξ Q D (h ω) innerShape z r ∧
    TwoScale.RatioMarginal.normAroundAt ξ Q D (h ω) innerShape z r ≤ ENNReal.ofReal Mi}
  have hDm := hD.measurable.comp hh.1.measurable
  have hGo : MeasurableSet Go :=
    (measurableSet_le measurable_const
      ((measurable_normAcrossAt ξ Q hD.measurable _ z r).comp hh.1.measurable)).inter
    (measurableSet_le ((measurable_normAroundAt ξ Q hD.measurable _ z r).comp
      hh.1.measurable) measurable_const)
  have hGi : MeasurableSet Gi :=
    (measurableSet_le measurable_const
      ((measurable_normAcrossAt ξ Q hD.measurable _ z r).comp hh.1.measurable)).inter
    (measurableSet_le ((measurable_normAroundAt ξ Q hD.measurable _ z r).comp
      hh.1.measurable) measurable_const)
  have hBar := BiLipschitz.Barrier.ae_barrier hD hQ P h hh
  have hLen := hD.length P h (LQGMetric.GM.detGFFPlusCont hh.1)
  
  have hkey : ∀ᵐ ω ∂P, ω ∈ Go → ω ∈ Gi → ∀ c : ℝ, IsCircleAverage (h ω) r z c →
      E2Prop (D (h ω)) (ξ : ℝ) Q z r q a θ Cm Cp c := by
    filter_upwards [hBar, hLen] with ω hB hL hωo hωi c hc
    have hcv : LQGMetric.circleAvg (h ω) r z = c := hc.limUnder_eq
    set N := ENNReal.ofReal ((r : ℝ) ^ ((ξ : ℝ) * Q) * Real.exp ((ξ : ℝ) * c)) with hNdef
    set n := ENNReal.ofReal ((r : ℝ) ^ (-((ξ : ℝ) * Q)) * Real.exp (-((ξ : ℝ) * c)))
    have hnN : N * n = 1 := normalizer_mul (ξ : ℝ) Q r c
    obtain ⟨ho1, ho2⟩ := hωo
    obtain ⟨hi1, -⟩ := hωi
    unfold TwoScale.RatioMarginal.normAcrossAt at ho1 hi1
    unfold TwoScale.RatioMarginal.normAroundAt at ho2
    rw [hcv, outerShape_translate] at ho1 ho2
    rw [hcv, innerShape_translate] at hi1
    have haround : aroundDist (D (h ω)) (outerAnn z r) ≤ ENNReal.ofReal Mo * N :=
      le_mul_of_normed_le hnN ho2
    have hacrO : ENNReal.ofReal Mo⁻¹ * N ≤ acrossDist (D (h ω)) (outerAnn z r) :=
      mul_le_of_le_normed hnN ho1
    have hacrI : ENNReal.ofReal Mi⁻¹ * N ≤ acrossDist (D (h ω)) (innerCrossAnn z r) :=
      mul_le_of_le_normed hnN hi1
    have hm : ENNReal.ofReal (max Mo Mi)⁻¹ * N ≤
        OptimalConstants.Ratios.setDist (D (h ω)) (TwoScale.S36Events.eventMiddle z r) (TwoScale.S36Events.eventBoundary z r) := by
      refine le_trans ?_ (middle_ge_min_across hB hL z r)
      refine le_min (le_trans (mul_le_mul' ?_ le_rfl) hacrI)
        (le_trans (mul_le_mul' ?_ le_rfl) hacrO)
      · exact ENNReal.ofReal_le_ofReal (inv_anti₀ hMi0 (le_max_right _ _))
      · exact ENNReal.ofReal_le_ofReal (inv_anti₀ hMo0 (le_max_left _ _))
    have hNle : N ≤ ENNReal.ofReal (max Mo Mi) *
        OptimalConstants.Ratios.setDist (D (h ω)) (TwoScale.S36Events.eventMiddle z r) (TwoScale.S36Events.eventBoundary z r) := by
      have hk0 : ENNReal.ofReal (max Mo Mi) ≠ 0 := (ENNReal.ofReal_pos.mpr hmax0).ne'
      calc
        N = ENNReal.ofReal (max Mo Mi) * (ENNReal.ofReal (max Mo Mi)⁻¹ * N) := by
          rw [ENNReal.ofReal_inv_of_pos hmax0, ← mul_assoc,
            ENNReal.mul_inv_cancel hk0 ENNReal.ofReal_ne_top, one_mul]
        _ ≤ _ := mul_le_mul' le_rfl hm
    unfold E2Prop
    refine le_min ?_ ?_
    · refine haround.trans ?_
      have h1a : 0 ≤ (1 - (a : ℝ))⁻¹ := by
        have := a.2.2
        exact inv_nonneg.mpr (by linarith)
      rw [mul_assoc, ENNReal.ofReal_mul h1a]
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal ha) le_rfl
    · refine haround.trans ?_
      calc
        ENNReal.ofReal Mo * N ≤ ENNReal.ofReal Mo * (ENNReal.ofReal (max Mo Mi) *
            OptimalConstants.Ratios.setDist (D (h ω)) (TwoScale.S36Events.eventMiddle z r) (TwoScale.S36Events.eventBoundary z r)) :=
          mul_le_mul' le_rfl hNle
        _ = ENNReal.ofReal (Mo * max Mo Mi) *
            OptimalConstants.Ratios.setDist (D (h ω)) (TwoScale.S36Events.eventMiddle z r) (TwoScale.S36Events.eventBoundary z r) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hMo0.le]
        _ ≤ _ := mul_le_mul' (ENNReal.ofReal_le_ofReal hq) le_rfl
  have hsub : {ω | ¬ ∀ c : ℝ, IsCircleAverage (h ω) r z c →
      E2Prop (D (h ω)) (ξ : ℝ) Q z r q a θ Cm Cp c} ≤ᵐ[P] (Goᶜ ∪ Giᶜ : Set Ω) := by
    filter_upwards [hkey] with ω hω hbad
    by_contra hno
    simp only [mem_union, mem_compl_iff, not_or, not_not] at hno
    exact hbad (hω hno.1 hno.2)
  have hcompl : ∀ {G : Set Ω}, MeasurableSet G → ENNReal.ofReal (1 - p / 2) ≤ P G →
      P Gᶜ ≤ ENNReal.ofReal (p / 2) := by
    intro G hG hPG
    rw [prob_compl_eq_one_sub hG]
    calc
      1 - P G ≤ 1 - ENNReal.ofReal (1 - p / 2) := tsub_le_tsub_left hPG 1
      _ = ENNReal.ofReal (p / 2) := by
        rw [ENNReal.ofReal_sub _ (by linarith), ENNReal.ofReal_one,
          ENNReal.sub_sub_cancel ENNReal.one_ne_top (ENNReal.ofReal_le_one.mpr (by linarith))]
  calc
    P {ω | ¬ ∀ c : ℝ, IsCircleAverage (h ω) r z c →
        E2Prop (D (h ω)) (ξ : ℝ) Q z r q a θ Cm Cp c} ≤ P (Goᶜ ∪ Giᶜ) := measure_mono_ae hsub
    _ ≤ P Goᶜ + P Giᶜ := measure_union_le _ _
    _ ≤ ENNReal.ofReal (p / 2) + ENNReal.ofReal (p / 2) :=
      add_le_add (hcompl hGo (hpo P h hh z r)) (hcompl hGi (hpi P h hh z r))
    _ = ENNReal.ofReal p := by
      rw [← ENNReal.ofReal_add (by linarith) (by linarith)]
      congr 1
      ring

end SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36
