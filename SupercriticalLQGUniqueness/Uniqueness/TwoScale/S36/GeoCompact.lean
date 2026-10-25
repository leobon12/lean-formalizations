import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.GeodesicExists
import SupercriticalLQGUniqueness.Uniqueness.Toolkit.PlanarSeparation.PaidTraces
import SupercriticalLQGUniqueness.Uniqueness.BiLipschitz.Barrier.Prob




 




















set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36

open LQGMetric (DistC)

 


theorem geodesic_stays_of_around_lt (D : LSCMetric) {P : ℝ → ℂ} {T : ℝ}
    (hP : ContinuousOn P (Icc 0 T))
    (hgeo : LQGMetric.MetricGeometry.IsGeodesicCurve (D.pt ∘ P) 0 T)
    (hunit : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 T))
    (A B : EuclideanAnnulus) (hBc : B.center = A.center)
    (hAB : A.outerRadius ≤ B.innerRadius)
    (h0 : dist (P 0) A.center ≤ A.innerRadius)
    (hT : dist (P T) A.center ≤ A.innerRadius)
    (hlt : aroundDist D A < acrossDist D B) :
    ∀ t ∈ Icc 0 T, dist (P t) A.center < B.outerRadius := by
  intro t ht
  by_contra hfar
  have hfar' : B.outerRadius ≤ dist (P t) A.center := not_lt.mp hfar
  have hA0 : 0 < A.innerRadius := A.2.1
  have hA1 : A.innerRadius < A.outerRadius := A.2.2
  have hB1 : B.innerRadius < B.outerRadius := B.2.2
  
  obtain ⟨π, s, s', hπ, hY, hsep, hlen⟩ : ∃ (π : ℝ → ℂ) (s s' : ℝ), D.IsCurve π s s' ∧
      (∀ τ ∈ Icc s s', π τ ∈ A.toSet) ∧
      Disconnects (π '' Icc s s') A.innerBoundary A.outerBoundary ∧
      D.len π s s' < acrossDist D B := by
    unfold aroundDist at hlt
    simp only [iInf_lt_iff] at hlt
    obtain ⟨π, s, s', hπ, hY, hsep, hlen⟩ := hlt
    exact ⟨π, s, s', hπ, hY, hsep, hlen⟩
  have hsep' : LQGMetric.Disconnects (π '' Icc s s')
      (Metric.sphere A.center A.innerRadius) (Metric.sphere A.center A.outerRadius) :=
    Toolkit.PlanarSeparation.candidate_disconnects_implies_path_hit hsep
  have hout : P t ∈ (Metric.ball A.center A.outerRadius)ᶜ := by
    simp only [mem_compl_iff, Metric.mem_ball, not_lt]
    linarith
  have hin0 : P 0 ∈ Metric.closedBall A.center A.innerRadius := Metric.mem_closedBall.mpr h0
  have hinT : P T ∈ Metric.closedBall A.center A.innerRadius := Metric.mem_closedBall.mpr hT
  
  obtain ⟨u, hu, huK⟩ := Toolkit.PlanarSeparation.pathHit_time ht.1 (hP.mono (Icc_subset_Icc le_rfl ht.2))
    (Toolkit.PlanarSeparation.annularPath_hit hA0 hA1 hsep') hin0 hout
  obtain ⟨v, hv, hvK⟩ := Toolkit.PlanarSeparation.pathHit_time ht.2 (hP.mono (Icc_subset_Icc ht.1 le_rfl))
    (Toolkit.PlanarSeparation.annularPath_hit_reverse hA0 hA1 hsep') hout hinT
  have huT : u ∈ Icc 0 T := ⟨hu.1, hu.2.trans ht.2⟩
  have hvT : v ∈ Icc 0 T := ⟨ht.1.trans hv.1, hv.2⟩
  have huv : u ≤ v := hu.2.trans hv.1
  have hcost : D (P u, P v) ≤ D.len π s s' := Toolkit.PlanarSeparation.trace_dist_le_len D π huK hvK
  have hdist : D (P u, P v) = ENNReal.ofReal (v - u) :=
    hgeo.edist_eq_of_hasUnitSpeedOn hunit huT hvT huv
  
  have hPu : dist (P u) A.center < A.outerRadius := by
    obtain ⟨q, hq, hqe⟩ := huK
    have hq' := (hY q hq).1
    rw [hqe] at hq'
    exact Metric.mem_ball.mp hq'
  have hf : ContinuousOn (fun τ => dist (P τ) A.center) (Icc u t) :=
    continuous_dist.comp_continuousOn
      ((hP.mono (Icc_subset_Icc huT.1 ht.2)).prodMk continuousOn_const)
  obtain ⟨σ, τ, huσ, hστ, hτt, hσr, hτr, -⟩ := LQGMetric.RectCross.exists_sub_crossing hu.2 hf
    hB1.le (hPu.le.trans hAB) hfar'
  have hσT : σ ∈ Icc 0 T := ⟨huT.1.trans huσ, (hστ.trans hτt).trans ht.2⟩
  have hτT : τ ∈ Icc 0 T := ⟨(huT.1.trans huσ).trans hστ, hτt.trans ht.2⟩
  have hcross : acrossDist D B ≤ D (P σ, P τ) := by
    refine iInf₂_le_of_le (P σ) ?_ (iInf₂_le (P τ) ?_)
    · change P σ ∈ Metric.sphere B.center B.innerRadius
      rw [Metric.mem_sphere, hBc]
      exact hσr
    · change P τ ∈ Metric.sphere B.center B.outerRadius
      rw [Metric.mem_sphere, hBc]
      exact hτr
  have hστd : D (P σ, P τ) = ENNReal.ofReal (τ - σ) :=
    hgeo.edist_eq_of_hasUnitSpeedOn hunit hσT hτT hστ
  have htime : ENNReal.ofReal (τ - σ) ≤ ENNReal.ofReal (v - u) :=
    ENNReal.ofReal_le_ofReal (by linarith [hv.1])
  have hchain : acrossDist D B < acrossDist D B :=
    calc acrossDist D B ≤ D (P σ, P τ) := hcross
      _ = ENNReal.ofReal (τ - σ) := hστd
      _ ≤ ENNReal.ofReal (v - u) := htime
      _ = D (P u, P v) := hdist.symm
      _ ≤ D.len π s s' := hcost
      _ < acrossDist D B := hlen
  exact lt_irrefl _ hchain

 
def sepAnnulus : EuclideanAnnulus :=
  ⟨(0, (2, 4)), by norm_num, by norm_num⟩

 
def GeoCompactEvent (D : LSCMetric) (n : ℕ) : Prop :=
  ∃ m : ℕ, 2 ≤ m ∧ m ≤ n ∧ aroundDist D sepAnnulus < acrossDist D (BiLipschitz.Barrier.dyadicAnnulus m)

theorem measurableSet_geoCompactEvent (D : DistC → LSCMetric) (hD : Measurable D) (n : ℕ) :
    MeasurableSet {g : DistC | GeoCompactEvent (D g) n} := by
  have hset : {g : DistC | GeoCompactEvent (D g) n} = ⋃ m ∈ Finset.Icc 2 n,
      {g : DistC | aroundDist (D g) sepAnnulus < acrossDist (D g) (BiLipschitz.Barrier.dyadicAnnulus m)} := by
    ext g
    simp only [GeoCompactEvent, mem_ofPred_eq, mem_iUnion, Finset.mem_Icc, exists_prop]
    constructor
    · rintro ⟨m, h2, hn, hlt⟩
      exact ⟨m, ⟨h2, hn⟩, hlt⟩
    · rintro ⟨m, ⟨h2, hn⟩, hlt⟩
      exact ⟨m, h2, hn, hlt⟩
  rw [hset]
  refine Finset.measurableSet_biUnion _ fun m _ => ?_
  exact measurableSet_lt ((measurable_aroundDist_fixed _).comp hD)
    ((SupercriticalLQGUniqueness.measurable_acrossDist _).comp hD)

 

theorem geodesic_stays_of_geoCompactEvent (D : LSCMetric) {n : ℕ} (hE : GeoCompactEvent D n)
    {P : ℝ → ℂ} {T : ℝ} (hP : ContinuousOn P (Icc 0 T))
    (hgeo : LQGMetric.MetricGeometry.IsGeodesicCurve (D.pt ∘ P) 0 T)
    (hunit : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 T))
    (h0 : ‖P 0‖ ≤ 1) (hT : ‖P T‖ ≤ 1) :
    ∀ t ∈ Icc 0 T, ‖P t‖ < 2 ^ (n + 1) := by
  obtain ⟨m, hm2, hmn, hlt⟩ := hE
  have hc : (BiLipschitz.Barrier.dyadicAnnulus m).center = sepAnnulus.center := rfl
  have hAB : sepAnnulus.outerRadius ≤ (BiLipschitz.Barrier.dyadicAnnulus m).innerRadius := by
    change (4 : ℝ) ≤ (2 : ℝ) ^ m
    calc (4 : ℝ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := pow_le_pow_right₀ one_le_two hm2
  have h0' : dist (P 0) sepAnnulus.center ≤ sepAnnulus.innerRadius := by
    change dist (P 0) 0 ≤ 2
    rw [dist_zero_right]
    linarith
  have hT' : dist (P T) sepAnnulus.center ≤ sepAnnulus.innerRadius := by
    change dist (P T) 0 ≤ 2
    rw [dist_zero_right]
    linarith
  intro t ht
  have h := geodesic_stays_of_around_lt D hP hgeo hunit sepAnnulus (BiLipschitz.Barrier.dyadicAnnulus m) hc hAB
    h0' hT' hlt t ht
  change dist (P t) 0 < (2 : ℝ) ^ (m + 1) at h
  rw [dist_zero_right] at h
  exact h.trans_le (pow_le_pow_right₀ one_le_two (by omega))

 
theorem dilate_one (A : EuclideanAnnulus) : A.dilate 1 one_pos = A := by
  apply Subtype.ext
  change ((1 : ℝ) • A.center, 1 * A.innerRadius, 1 * A.outerRadius) = A.1
  rw [one_smul, one_mul, one_mul]
  rfl

 

theorem geoCompact_prob (ξ : Ioi (0 : ℝ)) (Q : ℝ) (hQ : 0 < Q) (D : DistC → LSCMetric)
    (hD : IsWeakLQGMetric ξ Q D) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistC) (hh : IsNormalizedWholePlaneGFF h P)
    (η : ℝ) (hη : 0 < η) :
    ∃ n : ℕ, P {ω | ¬ GeoCompactEvent (D (h ω)) n} ≤ ENNReal.ofReal η := by
  set η' : ℝ := min η 1 with hη'def
  have hη'0 : 0 < η' := lt_min hη one_pos
  have hη'1 : η' ≤ 1 := min_le_right _ _
  have hη'η : η' ≤ η := min_le_left _ _
  obtain ⟨M, hM, hprob⟩ := TwoScale.RatioMarginal.origin_ratio_uniform ξ Q D hD sepAnnulus (1 - η' / 2)
    (by linarith) (by linarith)
  let r1 : Ioi (0 : ℝ) := ⟨1, mem_Ioi.mpr one_pos⟩
  have hgood := hprob P h hh r1
  set G : Set Ω := {ω | ENNReal.ofReal M⁻¹ ≤ TwoScale.RatioMarginal.normAcross ξ Q D (h ω) sepAnnulus r1 ∧
    TwoScale.RatioMarginal.normAround ξ Q D (h ω) sepAnnulus r1 ≤ ENNReal.ofReal M} with hGdef
  have hmeasG : MeasurableSet G :=
    ((measurableSet_le measurable_const
      ((TwoScale.RatioMarginal.measurable_normAcross ξ Q D hD sepAnnulus _).comp hh.1.measurable)).inter
      (measurableSet_le ((TwoScale.RatioMarginal.measurable_normAround ξ Q D hD sepAnnulus _).comp
        hh.1.measurable) measurable_const))
  
  have hfinG : ∀ ω ∈ G, aroundDist (D (h ω)) sepAnnulus < ⊤ := by
    intro ω hω
    have h2 := hω.2
    unfold TwoScale.RatioMarginal.normAround at h2
    change ENNReal.ofReal ((1 : ℝ) ^ (-((ξ : ℝ) * Q)) *
        Real.exp (-((ξ : ℝ) * LQGMetric.circleAvg (h ω) (1 : ℝ) 0))) *
        aroundDist (D (h ω)) (sepAnnulus.dilate 1 one_pos) ≤ ENNReal.ofReal M at h2
    rw [dilate_one] at h2
    have hn : 0 < ((1 : ℝ) ^ (-((ξ : ℝ) * Q)) *
        Real.exp (-((ξ : ℝ) * LQGMetric.circleAvg (h ω) (1 : ℝ) 0))) :=
      mul_pos (Real.rpow_pos_of_pos one_pos _) (Real.exp_pos _)
    by_contra htop
    rw [not_lt, top_le_iff] at htop
    rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.mpr hn).ne'] at h2
    exact ENNReal.ofReal_ne_top (top_le_iff.mp h2)
  
  set Bad : ℕ → Set Ω := fun n => {ω | ¬ GeoCompactEvent (D (h ω)) n} with hBaddef
  have hBadm : ∀ n, MeasurableSet (Bad n) := fun n =>
    ((measurableSet_geoCompactEvent D hD.measurable n).preimage hh.1.measurable).compl
  have hanti : Antitone Bad := by
    intro n n' hnn' ω hω hE
    apply hω
    obtain ⟨m, h2, hm, hlt⟩ := hE
    exact ⟨m, h2, hm.trans hnn', hlt⟩
  have hbar := BiLipschitz.Barrier.ae_barrier hD hQ P h hh
  have hinter : P (⋂ n, Bad n) ≤ ENNReal.ofReal (η' / 2) := by
    have hsub : (⋂ n, Bad n) ⊆ Gᶜ ∪ {ω | ¬ BiLipschitz.Barrier.Barrier (D (h ω))} := by
      intro ω hω
      by_contra hno
      simp only [mem_union, mem_compl_iff, mem_ofPred_eq, not_or, not_not] at hno
      obtain ⟨hωG, hωB⟩ := hno
      obtain ⟨k, hk⟩ := ENNReal.exists_nat_gt (hfinG ω hωG).ne
      obtain ⟨m, hm, hlt⟩ := hωB 2 k
      exact (mem_iInter.mp hω m) ⟨m, hm, le_rfl, hk.trans hlt⟩
    have hnull : P {ω | ¬ BiLipschitz.Barrier.Barrier (D (h ω))} = 0 := by
      rw [ae_iff] at hbar
      exact hbar
    calc P (⋂ n, Bad n) ≤ P (Gᶜ ∪ {ω | ¬ BiLipschitz.Barrier.Barrier (D (h ω))}) := measure_mono hsub
      _ ≤ P Gᶜ + P {ω | ¬ BiLipschitz.Barrier.Barrier (D (h ω))} := measure_union_le _ _
      _ = 1 - P G := by rw [hnull, add_zero, prob_compl_eq_one_sub hmeasG]
      _ ≤ 1 - ENNReal.ofReal (1 - η' / 2) := tsub_le_tsub_left hgood 1
      _ = ENNReal.ofReal (η' / 2) := by
        rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_sub _ (by linarith)]
        congr 1
        ring
  have htend := tendsto_measure_iInter_atTop (μ := P) (fun n => (hBadm n).nullMeasurableSet)
    hanti ⟨0, measure_ne_top P _⟩
  have hlt : P (⋂ n, Bad n) < ENNReal.ofReal η :=
    hinter.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hη).mpr (by linarith))
  obtain ⟨n, hn⟩ := ((tendsto_order.1 htend).2 _ hlt).exists
  exact ⟨n, hn.le⟩

end SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36
