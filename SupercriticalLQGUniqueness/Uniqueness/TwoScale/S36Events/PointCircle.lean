import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36Events.Clause5




set_option autoImplicit false
noncomputable section
open Set Metric LQGMetric.MetricGeometry
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36Events

 

theorem separator_hits_both_sides {P π : ℝ → ℂ}
    {T c s t : ℝ} {A : EuclideanAnnulus}
    (hc0 : 0 < c) (hcT : c < T)
    (hP : ContinuousOn P (Icc 0 T))
    (hcenter : P c = A.center)
    (hstart : A.outerRadius ≤ dist (P 0) A.center)
    (hend : A.outerRadius ≤ dist (P T) A.center)
    (hY : ∀ u ∈ Icc s t, π u ∈ A.toSet)
    (hsep : LQGMetric.Disconnects (π '' Icc s t)
      A.innerBoundary A.outerBoundary) :
    ∃ u v : ℝ, 0 ≤ u ∧ u < c ∧ c < v ∧ v ≤ T ∧
      P u ∈ π '' Icc s t ∧ P v ∈ π '' Icc s t ∧
      A.innerRadius < dist (P u) A.center ∧
      A.innerRadius < dist (P v) A.center := by
  have hsep' : LQGMetric.Disconnects (π '' Icc s t)
      (sphere A.center A.innerRadius) (sphere A.center A.outerRadius) :=
    by simpa only [EuclideanAnnulus.innerBoundary,
        EuclideanAnnulus.outerBoundary] using hsep
  have hann : π '' Icc s t ⊆
      {w | A.innerRadius < dist w A.center ∧ dist w A.center < A.outerRadius} := by
    intro w hw
    obtain ⟨q, hq, rfl⟩ := hw
    have hA : π q ∈ A.toSet := hY q hq
    change π q ∈ ball A.center A.outerRadius ∧
      π q ∉ closure (ball A.center A.innerRadius) at hA
    have hcl : closure (ball A.center A.innerRadius) =
        closedBall A.center A.innerRadius :=
      closure_ball A.center (ne_of_gt A.2.1)
    rw [hcl] at hA
    exact ⟨lt_of_not_ge (by simpa only [mem_closedBall] using hA.2),
      by simpa only [mem_ball] using hA.1⟩
  have h0out : P 0 ∈ (ball A.center A.outerRadius)ᶜ := by
    simpa only [mem_compl_iff, mem_ball, not_lt] using hstart
  have hTout : P T ∈ (ball A.center A.outerRadius)ᶜ := by
    simpa only [mem_compl_iff, mem_ball, not_lt] using hend
  have hcin : P c ∈ closedBall A.center A.innerRadius := by
    rw [hcenter]
    exact Metric.mem_closedBall_self A.2.1.le
  obtain ⟨u, hu, huK⟩ := Toolkit.PlanarSeparation.pathHit_time hc0.le
    (hP.mono (Icc_subset_Icc le_rfl hcT.le))
    (Toolkit.PlanarSeparation.annularPath_hit_reverse A.2.1 A.2.2 hsep')
    h0out hcin
  obtain ⟨v, hv, hvK⟩ := Toolkit.PlanarSeparation.pathHit_time hcT.le
    (hP.mono (Icc_subset_Icc hc0.le le_rfl))
    (Toolkit.PlanarSeparation.annularPath_hit A.2.1 A.2.2 hsep')
    hcin hTout
  have huAnn := hann huK
  have hvAnn := hann hvK
  have huc : u < c := by
    rcases eq_or_lt_of_le hu.2 with heq | hlt
    · have hbad : A.innerRadius < dist (P u) A.center := huAnn.1
      rw [heq, hcenter, dist_self] at hbad
      exact False.elim ((not_lt_of_ge A.2.1.le) hbad)
    · exact hlt
  have hcv : c < v := by
    rcases eq_or_lt_of_le hv.1 with heq | hlt
    · have hbad : A.innerRadius < dist (P v) A.center := hvAnn.1
      rw [← heq, hcenter, dist_self] at hbad
      exact False.elim ((not_lt_of_ge A.2.1.le) hbad)
    · exact hlt
  exact ⟨u, v, hu.1, huc, hcv, hv.2, huK, hvK, huAnn.1, hvAnn.1⟩

 

theorem pointSphereDist_le_around (D : LSCMetric) (A : EuclideanAnnulus)
    {P : ℝ → ℂ} {T c : ℝ}
    (hc0 : 0 < c) (hcT : c < T)
    (hP : ContinuousOn P (Icc 0 T))
    (hgeo : IsGeodesicCurve (D.pt ∘ P) 0 T)
    (hunit : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 T))
    (hcenter : P c = A.center)
    (hstart : A.outerRadius ≤ dist (P 0) A.center)
    (hend : A.outerRadius ≤ dist (P T) A.center) :
    OptimalConstants.Ratios.setDist D {A.center} (sphere A.center A.innerRadius) ≤
      aroundDist D A := by
  unfold aroundDist
  apply le_iInf
  intro π
  apply le_iInf
  intro s
  apply le_iInf
  intro t
  apply le_iInf
  intro hπ
  apply le_iInf
  intro hY
  apply le_iInf
  intro hsep
  have hsep' : LQGMetric.Disconnects (π '' Icc s t)
      A.innerBoundary A.outerBoundary :=
    Toolkit.PlanarSeparation.candidate_disconnects_implies_path_hit hsep
  obtain ⟨u, v, hu0, huc, hcv, hvT, huK, hvK, _, hvρ⟩ :=
    separator_hits_both_sides hc0 hcT hP hcenter hstart hend hY hsep'
  have hPc : ContinuousOn P (Icc c v) :=
    hP.mono (Icc_subset_Icc hc0.le hvT)
  have hf : ContinuousOn (fun j => dist (P j) A.center) (Icc c v) :=
    continuous_dist.comp_continuousOn (hPc.prodMk continuousOn_const)
  have hfc : dist (P c) A.center ≤ A.innerRadius := by
    rw [hcenter, dist_self]
    exact A.2.1.le
  obtain ⟨j, hj, hjρ⟩ := intermediate_value_Icc hcv.le hf ⟨hfc, hvρ.le⟩
  have hcircle : P j ∈ sphere A.center A.innerRadius := by
    rw [mem_sphere]
    exact hjρ
  have hset : OptimalConstants.Ratios.setDist D {A.center} (sphere A.center A.innerRadius) ≤
      D (A.center, P j) := by
    unfold OptimalConstants.Ratios.setDist
    exact iInf_le_of_le A.center (iInf_le_of_le (mem_singleton A.center)
      (iInf_le_of_le (P j) (iInf_le_of_le hcircle le_rfl)))
  have huT : u ∈ Icc (0 : ℝ) T := ⟨hu0, huc.le.trans hcT.le⟩
  have hvT' : v ∈ Icc (0 : ℝ) T := ⟨hc0.le.trans hcv.le, hvT⟩
  have hcT' : c ∈ Icc (0 : ℝ) T := ⟨hc0.le, hcT.le⟩
  have hjT : j ∈ Icc (0 : ℝ) T :=
    ⟨hc0.le.trans hj.1, hj.2.trans hvT⟩
  have hgeo₁ : D (P c, P j) = ENNReal.ofReal (j - c) :=
    hgeo.edist_eq_of_hasUnitSpeedOn hunit hcT' hjT hj.1
  have hgeo₂ : D (P u, P v) = ENNReal.ofReal (v - u) :=
    hgeo.edist_eq_of_hasUnitSpeedOn hunit huT hvT' (huc.le.trans hcv.le)
  have hcost : D (P u, P v) ≤ D.len π s t :=
    Toolkit.PlanarSeparation.trace_dist_le_len D π huK hvK
  calc
    OptimalConstants.Ratios.setDist D {A.center} (sphere A.center A.innerRadius) ≤
        D (A.center, P j) := hset
    _ = ENNReal.ofReal (j - c) := by rw [← hcenter]; exact hgeo₁
    _ ≤ ENNReal.ofReal (v - u) :=
      ENNReal.ofReal_le_ofReal (by linarith [hj.2, huc])
    _ = D (P u, P v) := hgeo₂.symm
    _ ≤ D.len π s t := hcost

 

theorem EndpointLoopAt.of_around (D : LSCMetric)
    {r a θ T c s t : ℝ} {P : ℝ → ℂ}
    (hr : 0 < r) (ha0 : 0 < a) (ha1 : a < 1)
    (hc0 : 0 < c) (hcT : c < T)
    (hP : ContinuousOn P (Icc 0 T))
    (hgeo : IsGeodesicCurve (D.pt ∘ P) 0 T)
    (hunit : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 T))
    (hstart : r ≤ dist (P 0) (P c))
    (hend : r ≤ dist (P T) (P c))
    (hAround : ∀ (δ : ℝ) (hδ : 0 < δ) (hδa : δ ≤ (1 - a) ^ 2),
      aroundDist D ⟨(P c, (δ * r, Real.sqrt δ * r)),
        TwoScale.Consolidated.loop_annulus_valid hr hδ (by
          nlinarith only [hδa, ha0, ha1] : δ < 1)⟩ ≤
        ENNReal.ofReal (δ ^ θ) * D (P s, P t)) :
    EndpointLoopAt D r a θ (P s) (P t) (P c) := by
  intro δ hδ hδa
  have hδ1 : δ < 1 := by nlinarith only [hδa, ha0, ha1]
  let A : EuclideanAnnulus :=
    ⟨(P c, (δ * r, Real.sqrt δ * r)),
      TwoScale.Consolidated.loop_annulus_valid hr hδ hδ1⟩
  have hroot : Real.sqrt δ ≤ 1 := by
    calc
      Real.sqrt δ ≤ Real.sqrt 1 := Real.sqrt_le_sqrt hδ1.le
      _ = 1 := by norm_num
  have hσr : A.outerRadius ≤ r := by
    change Real.sqrt δ * r ≤ r
    nlinarith only [mul_le_mul_of_nonneg_right hroot hr.le]
  have hcircle : OptimalConstants.Ratios.setDist D {P c} (sphere (P c) (δ * r)) ≤
      aroundDist D A :=
    pointSphereDist_le_around D A hc0 hcT hP hgeo hunit rfl
      (hσr.trans hstart) (hσr.trans hend)
  refine ⟨A, rfl, rfl, rfl, ?_⟩
  exact max_le (hcircle.trans (hAround δ hδ hδa)) (hAround δ hδ hδa)

 


theorem EventClause1.endpoint_loop_bounds (D : LSCMetric)
    {z : ℂ} {r q a θ T σ τ s t : ℝ} {P : ℝ → ℂ}
    (hr : 0 < r) (hq : q < 1) (ha0 : 0 < a) (ha1 : a < 1)
    (hsmall : (1 - a) ^ 2 ≤ q)
    (hE1 : EventClause1 D z r q θ)
    (hinternal : InternalBoundaryGeodesic D z r P σ τ)
    (hP : ContinuousOn P (Icc 0 T))
    (hgeo : IsGeodesicCurve (D.pt ∘ P) 0 T)
    (hunit : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 T))
    (hs0 : 0 < s) (hst : s < t) (htT : t < T)
    (hσs : σ ≤ s) (htτ : t ≤ τ)
    (hsmid : P s ∈ eventMiddle z r) (htmid : P t ∈ eventMiddle z r)
    (hsep : (1 - a) * r ≤ dist (P s) (P t))
    (h0s : r ≤ dist (P 0) (P s)) (hTs : r ≤ dist (P T) (P s))
    (h0t : r ≤ dist (P 0) (P t)) (hTt : r ≤ dist (P T) (P t)) :
    EndpointLoopAt D r a θ (P s) (P t) (P s) ∧
      EndpointLoopAt D r a θ (P s) (P t) (P t) := by
  have hAround (δ : ℝ) (hδ : 0 < δ) (hδa : δ ≤ (1 - a) ^ 2) :
      let As : EuclideanAnnulus :=
        ⟨(P s, (δ * r, Real.sqrt δ * r)),
          TwoScale.Consolidated.loop_annulus_valid hr hδ (hδa.trans_lt (by
            nlinarith only [ha0, ha1] : (1 - a) ^ 2 < 1))⟩
      let At : EuclideanAnnulus :=
        ⟨(P t, (δ * r, Real.sqrt δ * r)),
          TwoScale.Consolidated.loop_annulus_valid hr hδ (hδa.trans_lt (by
            nlinarith only [ha0, ha1] : (1 - a) ^ 2 < 1))⟩
      aroundDist D As ≤ ENNReal.ofReal (δ ^ θ) * D (P s, P t) ∧
        aroundDist D At ≤ ENNReal.ofReal (δ ^ θ) * D (P s, P t) := by
    have hroot : Real.sqrt δ ≤ 1 - a := by
      calc
        Real.sqrt δ ≤ Real.sqrt ((1 - a) ^ 2) := Real.sqrt_le_sqrt hδa
        _ = 1 - a := by rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (by linarith)]
    have hfar : Real.sqrt δ * r ≤ dist (P s) (P t) :=
      (mul_le_mul_of_nonneg_right hroot hr.le).trans hsep
    have hδq : δ ≤ q := hδa.trans hsmall
    exact EventClause1.endpoint_around_bounds D hr hq hE1 hinternal
      hP hgeo hunit hs0.le hst.le htT.le hσs htτ hsmid htmid
      hδ hδq hfar
  constructor
  · apply EndpointLoopAt.of_around D hr ha0 ha1 hs0
      (hst.trans htT) hP hgeo hunit h0s hTs
    intro δ hδ hδa
    exact (hAround δ hδ hδa).1
  · apply EndpointLoopAt.of_around D hr ha0 ha1 (hs0.trans hst)
      htT hP hgeo hunit h0t hTt
    intro δ hδ hδa
    exact (hAround δ hδ hδa).2

end SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36Events
