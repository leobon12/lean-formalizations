import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.GeoCompact




 





















set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36

open LQGMetric (DistC)

 

 
theorem variance_cInc_center {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistC}
    (hh : LQGMetric.IsWholePlaneGFF h P) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (hsr : s ≤ r)
    (z : ℂ) :
    Var[LQGMetric.CircleAvg.cInc h r z s z; P] = Real.log r - Real.log s := by
  rw [(LQGMetric.CircleAvg.map_cInc hh hr hs z z).2, LQGMetric.CircleAvg.incCov,
    LQGMetric.CircleAvg.circCov_center z hr r hr, LQGMetric.CircleAvg.circCov_center z hr s hs,
    LQGMetric.CircleAvg.circCov_center z hs r hr, LQGMetric.CircleAvg.circCov_center z hs s hs,
    inv_mul_cancel₀ hr.ne', inv_mul_cancel₀ hs.ne', Real.posLog_one]
  have h1 : Real.posLog (s⁻¹ * r) = Real.log r - Real.log s := by
    have hge : 1 ≤ s⁻¹ * r := by
      rw [← div_eq_inv_mul, one_le_div hs]
      exact hsr
    rw [Real.posLog_eq_log (by rw [abs_of_pos (by positivity)]; exact hge),
      Real.log_mul (inv_pos.mpr hs).ne' hr.ne', Real.log_inv]
    ring
  have h2 : Real.posLog (r⁻¹ * s) = 0 := by
    rw [Real.posLog_eq_zero_iff, abs_of_pos (by positivity), ← div_eq_inv_mul, div_le_one hr]
    exact hsr
  rw [h1, h2]
  ring

 

 
def baseAnn : EuclideanAnnulus :=
  ⟨(0, (1, 2)), by norm_num, by norm_num⟩

 
def innerScale (b : Ioi (0 : ℝ)) : Ioi (0 : ℝ) :=
  ⟨2 * (b : ℝ), mem_Ioi.mpr (mul_pos two_pos b.2)⟩

 
def outerScale (J : ℕ) (b : Ioi (0 : ℝ)) : Ioi (0 : ℝ) :=
  ⟨2 ^ J * (b : ℝ), mem_Ioi.mpr (mul_pos (pow_pos two_pos J) b.2)⟩

 


def GeoCompactEventB (d : LSCMetric) (J : ℕ) (b : Ioi (0 : ℝ)) : Prop :=
  aroundDist d (baseAnn.dilate (innerScale b) (innerScale b).2) <
    acrossDist d (baseAnn.dilate (outerScale J b) (outerScale J b).2)

 

theorem geodesic_stays_of_geoCompactEventB (d : LSCMetric) {J : ℕ} (hJ : 2 ≤ J)
    (b : Ioi (0 : ℝ)) (hE : GeoCompactEventB d J b) {P : ℝ → ℂ} {T : ℝ}
    (hP : ContinuousOn P (Icc 0 T))
    (hgeo : LQGMetric.MetricGeometry.IsGeodesicCurve (d.pt ∘ P) 0 T)
    (hunit : HasUnitSpeedOn (d.pt ∘ P) (Icc 0 T))
    (h0 : ‖P 0‖ ≤ b) (hT : ‖P T‖ ≤ b) :
    ∀ t ∈ Icc 0 T, ‖P t‖ < 2 ^ (J + 1) * b := by
  have hb : 0 < (b : ℝ) := b.2
  set A := baseAnn.dilate (innerScale b) (innerScale b).2 with hAdef
  set B := baseAnn.dilate (outerScale J b) (outerScale J b).2 with hBdef
  have hAc : A.center = 0 := by
    change ((2 * (b : ℝ)) • (0 : ℂ)) = 0
    exact smul_zero _
  have hBc : B.center = A.center := by
    rw [hAc]
    change ((2 ^ J * (b : ℝ)) • (0 : ℂ)) = 0
    exact smul_zero _
  have hAin : A.innerRadius = 2 * b := by
    change 2 * (b : ℝ) * 1 = 2 * b
    ring
  have hAout : A.outerRadius = 4 * b := by
    change 2 * (b : ℝ) * 2 = 4 * b
    ring
  have hBin : B.innerRadius = 2 ^ J * b := by
    change 2 ^ J * (b : ℝ) * 1 = 2 ^ J * b
    ring
  have hBout : B.outerRadius = 2 ^ (J + 1) * b := by
    change 2 ^ J * (b : ℝ) * 2 = 2 ^ (J + 1) * b
    ring
  have h4 : (4 : ℝ) ≤ 2 ^ J :=
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ J := pow_le_pow_right₀ one_le_two hJ
  have hAB : A.outerRadius ≤ B.innerRadius := by
    rw [hAout, hBin]
    exact mul_le_mul_of_nonneg_right h4 hb.le
  have h0' : dist (P 0) A.center ≤ A.innerRadius := by
    rw [hAc, hAin, dist_zero_right]
    linarith
  have hT' : dist (P T) A.center ≤ A.innerRadius := by
    rw [hAc, hAin, dist_zero_right]
    linarith
  intro t ht
  have hstay := geodesic_stays_of_around_lt d hP hgeo hunit A B hBc hAB h0' hT' hE t ht
  rw [hAc, hBout, dist_zero_right] at hstay
  exact hstay

 

 

theorem geo_scale_compare {M ξ Q b h₁ h₂ : ℝ} (N : ℕ) (hM : 1 ≤ M) (hξ : 0 < ξ) (hb : 0 < b)
    (hN : 2 * Real.log M ≤ ξ * Q * N * Real.log 2 / 2)
    (hX : |h₂ - h₁| < Q * N * Real.log 2 / 2) :
    M / ((2 * b) ^ (-(ξ * Q)) * Real.exp (-(ξ * h₁))) <
      M⁻¹ / ((2 ^ (N + 1) * b) ^ (-(ξ * Q)) * Real.exp (-(ξ * h₂))) := by
  have hr₁ : 0 < 2 * b := by positivity
  have hr₂ : 0 < 2 ^ (N + 1) * b := by positivity
  have hM0 : 0 < M := by linarith
  rw [Real.rpow_def_of_pos hr₁, Real.rpow_def_of_pos hr₂, ← Real.exp_add, ← Real.exp_add,
    div_eq_mul_inv, div_eq_mul_inv, ← Real.exp_neg, ← Real.exp_neg]
  have hlog : Real.log (2 ^ (N + 1) * b) = Real.log (2 * b) + N * Real.log 2 := by
    rw [Real.log_mul (by positivity) hb.ne', Real.log_mul two_ne_zero hb.ne', Real.log_pow]
    push_cast
    ring
  have hXl : -(Q * N * Real.log 2 / 2) < h₂ - h₁ := (abs_lt.mp hX).1
  have hXm : ξ * (-(Q * N * Real.log 2 / 2)) < ξ * (h₂ - h₁) := mul_lt_mul_of_pos_left hXl hξ
  have key : Real.log M + -(Real.log (2 * b) * -(ξ * Q) + -(ξ * h₁)) <
      -Real.log M + -(Real.log (2 ^ (N + 1) * b) * -(ξ * Q) + -(ξ * h₂)) := by
    rw [hlog]
    nlinarith
  calc M * Real.exp (-(Real.log (2 * b) * -(ξ * Q) + -(ξ * h₁)))
      = Real.exp (Real.log M + -(Real.log (2 * b) * -(ξ * Q) + -(ξ * h₁))) := by
        rw [Real.exp_add, Real.exp_log hM0]
    _ < Real.exp (-Real.log M + -(Real.log (2 ^ (N + 1) * b) * -(ξ * Q) + -(ξ * h₂))) :=
        Real.exp_lt_exp.mpr key
    _ = M⁻¹ * Real.exp (-(Real.log (2 ^ (N + 1) * b) * -(ξ * Q) + -(ξ * h₂))) := by
        rw [Real.exp_add, Real.exp_neg, Real.exp_log hM0]

 
theorem le_ofReal_div_of_mul_le {c M : ℝ} (hc : 0 < c) {x : ℝ≥0∞}
    (h : ENNReal.ofReal c * x ≤ ENNReal.ofReal M) : x ≤ ENNReal.ofReal (M / c) := by
  rw [ENNReal.ofReal_div_of_pos hc, ENNReal.le_div_iff_mul_le
    (Or.inl (ENNReal.ofReal_pos.mpr hc).ne') (Or.inl ENNReal.ofReal_ne_top), mul_comm]
  exact h

 
theorem ofReal_div_le_of_le_mul {c M : ℝ} (hc : 0 < c) {x : ℝ≥0∞}
    (h : ENNReal.ofReal M ≤ ENNReal.ofReal c * x) : ENNReal.ofReal (M / c) ≤ x := by
  rw [ENNReal.ofReal_div_of_pos hc, ENNReal.div_le_iff_le_mul
    (Or.inl (ENNReal.ofReal_pos.mpr hc).ne') (Or.inl ENNReal.ofReal_ne_top), mul_comm]
  exact h

 
theorem prob_compl_le_of_ge {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {S : Set Ω} (hS : MeasurableSet S) {δ : ℝ} (hδ1 : δ ≤ 1)
    (h : ENNReal.ofReal (1 - δ) ≤ P S) : P Sᶜ ≤ ENNReal.ofReal δ := by
  rw [prob_compl_eq_one_sub hS]
  calc 1 - P S ≤ 1 - ENNReal.ofReal (1 - δ) := tsub_le_tsub_left h 1
    _ = ENNReal.ofReal δ := by
      rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by linarith)]
      congr 1
      ring

 


theorem geoCompactB_prob (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q) (D : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) (η : ℝ) (hη : 0 < η) :
    ∃ J : ℕ, 2 ≤ J ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistC), IsNormalizedWholePlaneGFF h P → ∀ b : Ioi (0 : ℝ),
        P {ω | ¬ GeoCompactEventB (D (h ω)) J b} ≤ ENNReal.ofReal η := by
  set η' : ℝ := min η 1 with hη'def
  have hη'0 : 0 < η' := lt_min hη one_pos
  have hη'1 : η' ≤ 1 := min_le_right _ _
  have hη'η : η' ≤ η := min_le_left _ _
  have hξ : 0 < (ξ : ℝ) := ξ.2
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  obtain ⟨M, hM, hprob⟩ := TwoScale.RatioMarginal.origin_ratio_uniform ξ Q D hD baseAnn (1 - η' / 3)
    (by linarith) (by linarith)
  
  have hev1 : ∀ᶠ n : ℕ in atTop, 2 * Real.log M ≤ (ξ : ℝ) * Q * n * Real.log 2 / 2 := by
    have ht : Tendsto (fun n : ℕ => (ξ : ℝ) * Q * Real.log 2 / 2 * (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
    filter_upwards [ht.eventually_ge_atTop (2 * Real.log M)] with n hn
    linarith
  have hev2 : ∀ᶠ n : ℕ in atTop, 4 / (Q ^ 2 * Real.log 2) / n ≤ η' / 3 := by
    have h0 := tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) (4 / (Q ^ 2 * Real.log 2))
    exact h0.eventually (ge_mem_nhds (by positivity))
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hev1.and (hev2.and (eventually_ge_atTop 1)))
  obtain ⟨hN1, hN2, hN3⟩ := hN N le_rfl
  refine ⟨N + 1, by omega, ?_⟩
  intro Ω _ P _ h hh b
  have hb : 0 < (b : ℝ) := b.2
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN3
  set r₁ : Ioi (0 : ℝ) := innerScale b with hr₁def
  set r₂ : Ioi (0 : ℝ) := outerScale (N + 1) b with hr₂def
  have hr₁v : (r₁ : ℝ) = 2 * b := rfl
  have hr₂v : (r₂ : ℝ) = 2 ^ (N + 1) * b := rfl
  
  set S₁ : Set Ω := {ω | ENNReal.ofReal M⁻¹ ≤ TwoScale.RatioMarginal.normAcross ξ Q D (h ω) baseAnn r₁ ∧
    TwoScale.RatioMarginal.normAround ξ Q D (h ω) baseAnn r₁ ≤ ENNReal.ofReal M} with hS₁def
  set S₂ : Set Ω := {ω | ENNReal.ofReal M⁻¹ ≤ TwoScale.RatioMarginal.normAcross ξ Q D (h ω) baseAnn r₂ ∧
    TwoScale.RatioMarginal.normAround ξ Q D (h ω) baseAnn r₂ ≤ ENNReal.ofReal M} with hS₂def
  have hmeas : ∀ r : Ioi (0 : ℝ), MeasurableSet {ω | ENNReal.ofReal M⁻¹ ≤
      TwoScale.RatioMarginal.normAcross ξ Q D (h ω) baseAnn r ∧
      TwoScale.RatioMarginal.normAround ξ Q D (h ω) baseAnn r ≤ ENNReal.ofReal M} := fun r =>
    (measurableSet_le measurable_const
      ((TwoScale.RatioMarginal.measurable_normAcross ξ Q D hD baseAnn r).comp hh.1.measurable)).inter
      (measurableSet_le ((TwoScale.RatioMarginal.measurable_normAround ξ Q D hD baseAnn r).comp
        hh.1.measurable) measurable_const)
  have hS₁ : P S₁ᶜ ≤ ENNReal.ofReal (η' / 3) :=
    prob_compl_le_of_ge P (hmeas r₁) (by linarith) (hprob P h hh r₁)
  have hS₂ : P S₂ᶜ ≤ ENNReal.ofReal (η' / 3) :=
    prob_compl_le_of_ge P (hmeas r₂) (by linarith) (hprob P h hh r₂)
  
  set X := LQGMetric.CircleAvg.cInc h (r₂ : ℝ) 0 (r₁ : ℝ) 0 with hXdef
  have hlaw := LQGMetric.CircleAvg.map_cInc hh.1 r₂.2 r₁.2 0 0
  have hXm := (LQGMetric.CircleAvg.measurable_cInc hh.1 (r₂ : ℝ) 0 (r₁ : ℝ) 0).aemeasurable (μ := P)
  have hfacts := LQGMetric.CircleAvg.gaussianReal_facts hXm hlaw.1
  have hmean : P[X] = 0 := by
    rw [show P[X] = ∫ x, x ∂(P.map X) from (integral_map hXm aestronglyMeasurable_id).symm,
      hlaw.1, integral_id_gaussianReal]
  have hr12 : (r₁ : ℝ) ≤ r₂ := by
    rw [hr₁v, hr₂v]
    have h2 : (2 : ℝ) ≤ 2 ^ (N + 1) :=
      calc (2 : ℝ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (N + 1) := pow_le_pow_right₀ one_le_two (by omega)
    exact mul_le_mul_of_nonneg_right h2 hb.le
  have hvar : Var[X; P] = N * Real.log 2 := by
    rw [hXdef, variance_cInc_center hh.1 r₂.2 r₁.2 hr12 0, hr₁v, hr₂v,
      Real.log_mul (by positivity) hb.ne', Real.log_mul two_ne_zero hb.ne', Real.log_pow]
    push_cast
    ring
  set t : ℝ := Q * N * Real.log 2 / 2 with htdef
  have htpos : 0 < t := by positivity
  have hcheb : P {ω | t ≤ |X ω - P[X]|} ≤ ENNReal.ofReal (η' / 3) := by
    refine (meas_ge_le_variance_div_sq hfacts.2 htpos).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [hvar, htdef]
    have : N * Real.log 2 / (Q * N * Real.log 2 / 2) ^ 2 = 4 / (Q ^ 2 * Real.log 2) / N := by
      field_simp
      norm_num
    rw [this]
    exact hN2
  
  have hsub : {ω | ¬ GeoCompactEventB (D (h ω)) (N + 1) b} ⊆
      (S₁ᶜ ∪ S₂ᶜ) ∪ {ω | t ≤ |X ω - P[X]|} := by
    intro ω hω
    by_contra hno
    simp only [mem_union, mem_compl_iff, mem_ofPred_eq, not_or, not_not, not_le] at hno
    obtain ⟨⟨h1, h2⟩, h3⟩ := hno
    rw [hmean, sub_zero] at h3
    apply hω
    set c₁ : ℝ := (r₁ : ℝ) ^ (-((ξ : ℝ) * Q)) *
      Real.exp (-((ξ : ℝ) * LQGMetric.circleAvg (h ω) r₁ 0)) with hc₁def
    set c₂ : ℝ := (r₂ : ℝ) ^ (-((ξ : ℝ) * Q)) *
      Real.exp (-((ξ : ℝ) * LQGMetric.circleAvg (h ω) r₂ 0)) with hc₂def
    have hc₁ : 0 < c₁ := mul_pos (Real.rpow_pos_of_pos r₁.2 _) (Real.exp_pos _)
    have hc₂ : 0 < c₂ := mul_pos (Real.rpow_pos_of_pos r₂.2 _) (Real.exp_pos _)
    have haround : aroundDist (D (h ω)) (baseAnn.dilate r₁ r₁.2) ≤ ENNReal.ofReal (M / c₁) :=
      le_ofReal_div_of_mul_le hc₁ h1.2
    have hacross : ENNReal.ofReal (M⁻¹ / c₂) ≤ acrossDist (D (h ω)) (baseAnn.dilate r₂ r₂.2) :=
      ofReal_div_le_of_le_mul hc₂ h2.1
    have hXω : X ω = LQGMetric.circleAvg (h ω) r₂ 0 - LQGMetric.circleAvg (h ω) r₁ 0 := rfl
    have hX' : |LQGMetric.circleAvg (h ω) (r₂ : ℝ) 0 - LQGMetric.circleAvg (h ω) (r₁ : ℝ) 0| <
        Q * N * Real.log 2 / 2 := by
      rw [← hXω, ← htdef]
      exact h3
    rw [hr₁v, hr₂v] at hX'
    have hcmp : M / c₁ < M⁻¹ / c₂ := by
      rw [hc₁def, hc₂def, hr₁v, hr₂v]
      exact geo_scale_compare N hM hξ hb hN1 hX'
    have hpos : 0 < M⁻¹ / c₂ := div_pos (inv_pos.mpr (by linarith)) hc₂
    exact haround.trans_lt (((ENNReal.ofReal_lt_ofReal_iff hpos).mpr hcmp).trans_le hacross)
  calc P {ω | ¬ GeoCompactEventB (D (h ω)) (N + 1) b}
      ≤ P ((S₁ᶜ ∪ S₂ᶜ) ∪ {ω | t ≤ |X ω - P[X]|}) := measure_mono hsub
    _ ≤ P S₁ᶜ + P S₂ᶜ + P {ω | t ≤ |X ω - P[X]|} :=
        (measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)
    _ ≤ ENNReal.ofReal (η' / 3) + ENNReal.ofReal (η' / 3) + ENNReal.ofReal (η' / 3) :=
        add_le_add (add_le_add hS₁ hS₂) hcheb
    _ = ENNReal.ofReal η' := by
        rw [← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        ring
    _ ≤ ENNReal.ofReal η := ENNReal.ofReal_le_ofReal hη'η

end SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36
