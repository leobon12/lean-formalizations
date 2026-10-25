import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.ELocalB




 











set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36

open LQGMetric (DistC addConst restrictTo)

 

 
def translateMetric (M : LSCMetric) (w : ℂ) : LSCMetric :=
  ⟨fun p => M (p.1 + w, p.2 + w), by
    refine ⟨⟨fun x => M.isExtMetric.1 _, fun x y h => ?_, fun x y => M.isExtMetric.2.2.1 _ _,
      fun x y z => M.isExtMetric.2.2.2 _ _ _⟩, ?_⟩
    · exact add_right_cancel (M.isExtMetric.2.1 _ _ h)
    · exact M.lowerSemicontinuous.comp ((continuous_fst.add continuous_const).prodMk
        (continuous_snd.add continuous_const))⟩

@[simp] theorem translateMetric_apply (M : LSCMetric) (w x y : ℂ) :
    translateMetric M w (x, y) = M (x + w, y + w) := rfl

theorem len_translateMetric (M : LSCMetric) (w : ℂ) (P : ℝ → ℂ) (a b : ℝ) :
    (translateMetric M w).len P a b = M.len (fun t => P t + w) a b := by
  have h := @LQGMetric.MetricGeometry.eVariationOn_eq_mul_of_edist ℂ ℂ
    (@EMetricSpace.toPseudoEMetricSpace ℂ ((translateMetric M w).instEMetricSpace))
    (@EMetricSpace.toPseudoEMetricSpace ℂ (M.instEMetricSpace))
    P (fun t => P t + w) 1 (fun s t => by
      change M (P s + w, P t + w) = 1 * M (P s + w, P t + w)
      rw [one_mul]) (Icc a b)
  rw [one_mul] at h
  exact h

theorem isCurve_translateMetric_iff (M : LSCMetric) (w : ℂ) (P : ℝ → ℂ) (a b : ℝ) :
    (translateMetric M w).IsCurve P a b ↔ M.IsCurve (fun t => P t + w) a b := by
  constructor
  · rintro ⟨hab, hP⟩
    refine ⟨hab, fun t ht => ?_⟩
    have hlim := tendsto_iff_edist_tendsto_0.mp (hP t ht)
    exact tendsto_iff_edist_tendsto_0.mpr hlim
  · rintro ⟨hab, hP⟩
    refine ⟨hab, fun t ht => ?_⟩
    have hlim := tendsto_iff_edist_tendsto_0.mp (hP t ht)
    exact tendsto_iff_edist_tendsto_0.mpr hlim

theorem setDist_point_translateMetric (M : LSCMetric) (w x : ℂ) (ρ : ℝ) :
    OptimalConstants.Ratios.setDist (translateMetric M w) {x} (Metric.sphere x ρ) =
      OptimalConstants.Ratios.setDist M {x + w} (Metric.sphere (x + w) ρ) := by
  simp only [OptimalConstants.Ratios.setDist, iInf_singleton]
  apply le_antisymm
  · refine le_iInf₂ fun y hy => ?_
    have hy' : y - w ∈ Metric.sphere x ρ := by
      rw [Metric.mem_sphere] at hy ⊢
      rw [dist_eq_norm] at hy ⊢
      rw [← hy]
      congr 1
      ring
    refine (iInf₂_le (f := fun y (_ : y ∈ Metric.sphere x ρ) =>
      translateMetric M w (x, y)) (y - w) hy').trans (le_of_eq ?_)
    rw [translateMetric_apply, sub_add_cancel]
  · refine le_iInf₂ fun y hy => ?_
    have hy' : y + w ∈ Metric.sphere (x + w) ρ := by
      rw [Metric.mem_sphere] at hy ⊢
      rw [dist_add_right]
      exact hy
    exact (iInf₂_le (f := fun y (_ : y ∈ Metric.sphere (x + w) ρ) => M (x + w, y)) (y + w) hy')

 

section Affine

variable {M m : LSCMetric} {k : ℝ≥0∞} {w : ℂ}

theorem affine_scale (hm : ∀ x y, m (x, y) = k * M (x + w, y + w)) :
    ∀ x y, m (x, y) = k * translateMetric M w (x, y) := fun x y => hm x y

theorem isCurve_affine_iff (hk0 : k ≠ 0) (hkt : k ≠ ⊤)
    (hm : ∀ x y, m (x, y) = k * M (x + w, y + w)) (P : ℝ → ℂ) (a b : ℝ) :
    m.IsCurve P a b ↔ M.IsCurve (fun t => P t + w) a b := by
  rw [Positivity.Witnesses.isCurve_iff_of_dist_scale (translateMetric M w) m k hk0 hkt (affine_scale hm),
    isCurve_translateMetric_iff]

theorem len_affine (hm : ∀ x y, m (x, y) = k * M (x + w, y + w)) (P : ℝ → ℂ) (a b : ℝ) :
    m.len P a b = k * M.len (fun t => P t + w) a b := by
  rw [Positivity.Witnesses.len_eq_mul_of_dist_scale (translateMetric M w) m k (affine_scale hm),
    len_translateMetric]

theorem aroundDist_affine (hk0 : k ≠ 0) (hkt : k ≠ ⊤)
    (hm : ∀ x y, m (x, y) = k * M (x + w, y + w)) (A : EuclideanAnnulus) :
    aroundDist m A = k * aroundDist M (Positivity.Witnesses.annulusTranslate A w) := by
  rw [Positivity.Witnesses.aroundDist_eq_mul_of_dist_scale (translateMetric M w) m k hk0 hkt (affine_scale hm),
    BiLipschitz.OneScale.aroundDist_translate M (translateMetric M w) A w (fun x y => rfl)]

theorem setDist_point_affine (hk0 : k ≠ 0) (hkt : k ≠ ⊤)
    (hm : ∀ x y, m (x, y) = k * M (x + w, y + w)) (x : ℂ) (ρ : ℝ) :
    OptimalConstants.Ratios.setDist m {x} (Metric.sphere x ρ) =
      k * OptimalConstants.Ratios.setDist M {x + w} (Metric.sphere (x + w) ρ) := by
  rw [setDist_eq_mul_of_scale hk0 hkt (affine_scale hm), setDist_point_translateMetric]

end Affine

 

 

def HAt (D D' : LSCMetric) (ξ Q : ℝ) (z : ℂ) (r : Ioi (0 : ℝ)) (a : Ioo (3 / 4 : ℝ) 1)
    (C θ : Ioi (0 : ℝ)) (hCircle : ℝ) : Prop :=
  ∃ u v : ℂ, u ∈ Metric.sphere z (a * r) ∧ v ∈ Metric.sphere z r ∧
    ENNReal.ofReal C * D (u, v) ≤ D' (u, v) ∧
    ∃ (P : ℝ → ℂ) (s t : ℝ), OptimalConstants.Ratios.Geodesic D P s t u v ∧
      (∀ τ ∈ Icc s t, P τ ∈ Metric.closedBall z r \ Metric.ball z (a * r)) ∧
      Metric.diam (P '' Icc s t) ≤ r / 100 ∧
      D (u, v) ≤ ENNReal.ofReal ((1 - (a : ℝ))⁻¹ * (r : ℝ) ^ (ξ * Q) * Real.exp (ξ * hCircle)) ∧
      OptimalConstants.Ratios.EndpointLoop D r a θ u v u ∧ OptimalConstants.Ratios.EndpointLoop D r a θ u v v

 
theorem hAt_transport {M M' m m' : LSCMetric} {ξ t : ℝ} (w : ℂ)
    (hm : ∀ x y, m (x, y) = ENNReal.ofReal (Real.exp (ξ * t)) * M (x + w, y + w))
    (hm' : ∀ x y, m' (x, y) = ENNReal.ofReal (Real.exp (ξ * t)) * M' (x + w, y + w))
    (Q : ℝ) (r : Ioi (0 : ℝ)) (a : Ioo (3 / 4 : ℝ) 1) (C θ : Ioi (0 : ℝ)) (c : ℝ)
    (hH : HAt M M' ξ Q w r a C θ c) : OptimalConstants.Ratios.H m m' ξ Q r a C θ (c + t) := by
  set k : ℝ≥0∞ := ENNReal.ofReal (Real.exp (ξ * t)) with hkdef
  have hk0 : k ≠ 0 := expScale_ne_zero ξ t
  have hkt : k ≠ ⊤ := ENNReal.ofReal_ne_top
  obtain ⟨u, v, hu, hv, hC, P, s, s', hgeo, htr, hdiam, hN, hLu, hLv⟩ := hH
  obtain ⟨hcP, hPs, hPs', hlen, hfin⟩ := hgeo
  have hmuv : m (u - w, v - w) = k * M (u, v) := by rw [hm, sub_add_cancel, sub_add_cancel]
  have hmuv' : m' (u - w, v - w) = k * M' (u, v) := by rw [hm', sub_add_cancel, sub_add_cancel]
  have huv : u ≠ v := by
    intro he
    rw [Metric.mem_sphere] at hu hv
    rw [he, hv] at hu
    have ha : (a : ℝ) < 1 := a.2.2
    have hr : (0 : ℝ) < r := r.2
    nlinarith
  have hfin' : m (u - w, v - w) < ⊤ := by rw [hmuv]; exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top hfin
  have hloop : ∀ x, OptimalConstants.Ratios.EndpointLoop M r a θ u v x →
      OptimalConstants.Ratios.EndpointLoop m r a θ (u - w) (v - w) (x - w) := by
    intro x hL δ hδ0 hδa
    obtain ⟨A, hAc, hAi, hAo, hmax⟩ := hL δ hδ0 hδa
    let A' : EuclideanAnnulus := ⟨(x - w, (A.innerRadius, A.outerRadius)), A.2⟩
    have hA'eq : Positivity.Witnesses.annulusTranslate A' w = A := by
      apply Subtype.ext
      change ((x - w + w, (A.innerRadius, A.outerRadius)) : ℂ × ℝ × ℝ) = A.1
      rw [sub_add_cancel, ← hAc]
      rfl
    refine ⟨A', rfl, hAi, hAo, ?_⟩
    rw [setDist_point_affine hk0 hkt hm, aroundDist_affine hk0 hkt hm, hA'eq, sub_add_cancel,
      hmuv, ← mul_max, mul_left_comm]
    exact mul_le_mul' le_rfl hmax
  refine ⟨u - w, v - w, ?_, ?_, ?_, ?_, ?_, fun τ => P τ - w, s, s', ⟨?_, ?_, ?_, ?_, hfin'⟩,
    ?_, ?_, ?_, hloop u hLu, hloop v hLv⟩
  · rw [Metric.mem_sphere, dist_eq_norm, sub_zero, ← dist_eq_norm]
    exact Metric.mem_sphere.mp hu
  · rw [Metric.mem_sphere, dist_eq_norm, sub_zero, ← dist_eq_norm]
    exact Metric.mem_sphere.mp hv
  · intro hs
    have := hs (v - w) (fun h => huv (sub_left_injective h).symm)
    exact hfin'.ne this
  · intro hs
    have := hs (u - w) (fun h => huv (sub_left_injective h))
    rw [m.isExtMetric.2.2.1] at this
    exact hfin'.ne this
  · rw [hmuv, hmuv', mul_left_comm]
    exact mul_le_mul' le_rfl hC
  · rw [isCurve_affine_iff hk0 hkt hm]
    simpa only [sub_add_cancel] using hcP
  · simp only [hPs]
  · simp only [hPs']
  · rw [len_affine hm, hmuv]
    simpa only [sub_add_cancel] using congrArg (k * ·) hlen
  · intro τ hτ
    have h := htr τ hτ
    obtain ⟨h1, h2⟩ := h
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, ← dist_eq_norm]
      exact Metric.mem_closedBall.mp h1
    · rw [Metric.mem_ball, dist_eq_norm, sub_zero, ← dist_eq_norm]
      exact fun hlt => h2 (Metric.mem_ball.mpr hlt)
  · have hK : IsCompact (Metric.closedBall w (r : ℝ) \ Metric.ball w ((a : ℝ) * r)) :=
      (isCompact_closedBall _ _).diff Metric.isOpen_ball
    have hbdd : Bornology.IsBounded (P '' Icc s s') :=
      (isCompact_Icc.image_of_continuousOn
        (hcP.continuousOn_of_mapsTo hK fun τ hτ => htr τ hτ)).isBounded
    have hr0 : (0 : ℝ) ≤ (r : ℝ) / 100 := div_nonneg (le_of_lt r.2) (by norm_num)
    refine Metric.diam_le_of_forall_dist_le hr0 ?_
    rintro _ ⟨τ₁, h₁, rfl⟩ _ ⟨τ₂, h₂, rfl⟩
    rw [dist_sub_right]
    exact (Metric.dist_le_diam_of_mem hbdd ⟨τ₁, h₁, rfl⟩ ⟨τ₂, h₂, rfl⟩).trans hdiam
  · rw [hmuv, ofReal_N_shift, ← hkdef]
    exact mul_le_mul' le_rfl hN

 

 
theorem isCircleAverage_translate (g : DistC) (r : Ioi (0 : ℝ)) (z : ℂ) (c : ℝ) :
    IsCircleAverage (translateDist z g) r 0 c ↔ IsCircleAverage g r z c := by
  unfold IsCircleAverage
  have h : (fun n : ℕ => Real.circleAverage (fun x => (translateDist z g)
      (LQGMetric.bumpTest n x)) 0 (r : ℝ)) =
      fun n : ℕ => Real.circleAverage (fun x => g (LQGMetric.bumpTest n x)) z (r : ℝ) := by
    funext n
    have hfun : (fun x => (translateDist z g) (LQGMetric.bumpTest n x)) =
        fun x => g (LQGMetric.bumpTest n (x + z)) := by
      funext x
      rw [translateDist_eq_affineComp_one, LQGMetric.GFFInv.affineComp_apply,
        LQGMetric.GM.Tight.testAffinePull_one_bumpTest]
      simp
    rw [hfun]
    exact Real.circleAverage_map_add_const (f := fun x => g (LQGMetric.bumpTest n x))
  rw [h]

 
def recentredTranslate {Ω : Type} (h : Ω → DistC) (z : ℂ) (ω : Ω) : DistC :=
  addConst (translateDist z (h ω)) (-LQGMetric.circleAvg (h ω) 1 z)

 
theorem ae_hAt_to_H {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P) (ξ : Ioi (0 : ℝ)) (Q : ℝ)
    (D D' : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D')
    (z : ℂ) (r : Ioi (0 : ℝ)) (a : Ioo (3 / 4 : ℝ) 1) (C θ : Ioi (0 : ℝ)) :
    ∀ᵐ ω ∂P, ∀ c : ℝ, IsCircleAverage (h ω) r z c →
      HAt (D (h ω)) (D' (h ω)) (ξ : ℝ) Q z r a C θ c →
        OptimalConstants.Ratios.HEvent D D' (ξ : ℝ) Q r a C θ (recentredTranslate h z ω) := by
  have hplus : LQGMetric.IsGFFPlusCont h P := LQGMetric.GM.detGFFPlusCont hh.1
  have htrGFF : LQGMetric.IsWholePlaneGFF (fun ω => translateDist z (h ω)) P := by
    simpa only [translateDist_eq_affineComp_one] using hh.1.affineComp one_pos z
  have hplusTr : LQGMetric.IsGFFPlusCont (fun ω => translateDist z (h ω)) P :=
    LQGMetric.GM.Tight.isGFFPlusCont_of_wp htrGFF
  filter_upwards [hD.translation P h hplus z, hD'.translation P h hplus z,
    Positivity.Witnesses.ae_addConst_eq_mul P (fun ω => translateDist z (h ω)) hplusTr ξ Q D hD
      (fun ω => -LQGMetric.circleAvg (h ω) 1 z),
    Positivity.Witnesses.ae_addConst_eq_mul P (fun ω => translateDist z (h ω)) hplusTr ξ Q D' hD'
      (fun ω => -LQGMetric.circleAvg (h ω) 1 z)] with ω hT hT' hW hW' c hc hH
  set t := -LQGMetric.circleAvg (h ω) 1 z
  have hm : ∀ x y, D (recentredTranslate h z ω) (x, y) =
      ENNReal.ofReal (Real.exp ((ξ : ℝ) * t)) * D (h ω) (x + z, y + z) := by
    intro x y
    rw [recentredTranslate, hW (x, y)]
    congr 1
    exact hT x y
  have hm' : ∀ x y, D' (recentredTranslate h z ω) (x, y) =
      ENNReal.ofReal (Real.exp ((ξ : ℝ) * t)) * D' (h ω) (x + z, y + z) := by
    intro x y
    rw [recentredTranslate, hW' (x, y)]
    congr 1
    exact hT' x y
  refine ⟨c + t, ?_, hAt_transport z hm hm' Q r a C θ c hH⟩
  exact (isCircleAverage_addConst (translateDist z (h ω)) t r 0 c).mpr
    ((isCircleAverage_translate (h ω) r z c).mpr hc)

 
theorem prob_hAt_le {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P) (ξ : Ioi (0 : ℝ)) (Q : ℝ)
    (D D' : DistC → LSCMetric) (hD : IsWeakLQGMetric ξ Q D) (hD' : IsWeakLQGMetric ξ Q D')
    (z : ℂ) (r : Ioi (0 : ℝ)) (a : Ioo (3 / 4 : ℝ) 1) (C θ : Ioi (0 : ℝ)) :
    P {ω | ∃ c : ℝ, IsCircleAverage (h ω) r z c ∧
        HAt (D (h ω)) (D' (h ω)) (ξ : ℝ) Q z r a C θ c} ≤
      P {ω | OptimalConstants.Ratios.HEvent D D' (ξ : ℝ) Q r a C θ (h ω)} := by
  have hnorm := normalized_translate_sub_circleAvg hh z
  have hmeasT : Measurable (recentredTranslate h z) := hnorm.1.measurable
  calc
    P {ω | ∃ c : ℝ, IsCircleAverage (h ω) r z c ∧
        HAt (D (h ω)) (D' (h ω)) (ξ : ℝ) Q z r a C θ c} ≤
        P (recentredTranslate h z ⁻¹' {g | OptimalConstants.Ratios.HEvent D D' (ξ : ℝ) Q r a C θ g}) := by
      refine measure_mono_ae ?_
      filter_upwards [ae_hAt_to_H P h hh ξ Q D D' hD hD' z r a C θ] with ω hω hmem
      obtain ⟨c, hc, hH⟩ := hmem
      exact hω c hc hH
    _ = P (h ⁻¹' {g | OptimalConstants.Ratios.HEvent D D' (ξ : ℝ) Q r a C θ g}) :=
      prob_preimage_eq_of_map_eq P P hmeasT hh.1.measurable
        (map_normalized_translate_sub_circleAvg hh z)
        (HEvent_um D D' hD.measurable hD'.measurable (ξ : ℝ) Q r a C θ)
    _ = P {ω | OptimalConstants.Ratios.HEvent D D' (ξ : ℝ) Q r a C θ (h ω)} := rfl

end SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36
