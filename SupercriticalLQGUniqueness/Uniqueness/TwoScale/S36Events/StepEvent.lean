import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36Events.PointCircle




set_option autoImplicit false
noncomputable section
open Set Metric LQGMetric.MetricGeometry
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36Events

 

theorem CoveredStep.event_endpoint_geometry
    {P : ℝ → ℂ} {Good : ℂ → ℝ → Prop}
    {ε b α T : ℝ} {z w : ℂ}
    (st : TwoScale.Stopping.CoveredStep P Good ε b α z w)
    (q : Ioo (0 : ℝ) (1 / 100))
    (aEvt : Ioo (1 - (q : ℝ)) 1)
    (hα : α = (aEvt : ℝ))
    (hP0 : P 0 = z) (hPT : P T = w)
    (hr : 0 < st.radius) :
    (1 - (aEvt : ℝ)) ^ 2 ≤ (q : ℝ) ∧
      P st.s ∈ eventMiddle st.center st.radius ∧
      P st.t ∈ eventMiddle st.center st.radius ∧
      (1 - (aEvt : ℝ)) * st.radius ≤ dist (P st.s) (P st.t) ∧
      st.radius ≤ dist (P 0) (P st.s) ∧
      st.radius ≤ dist (P T) (P st.s) ∧
      st.radius ≤ dist (P 0) (P st.t) ∧
      st.radius ≤ dist (P T) (P st.t) := by
  have hqsmall : (q : ℝ) < 1 / 100 := q.2.2
  have ha1 : (aEvt : ℝ) < 1 := aEvt.2.2
  have ha0 : 0 < (aEvt : ℝ) := by linarith [aEvt.2.1]
  have ha34 : 3 / 4 < (aEvt : ℝ) := by linarith [aEvt.2.1]
  have hsmall : (1 - (aEvt : ℝ)) ^ 2 ≤ (q : ℝ) := by
    nlinarith only [aEvt.2.1, ha1, ha0, hqsmall]
  have hPs : dist (P st.s) st.center = (aEvt : ℝ) * st.radius := by
    exact (mem_sphere.mp st.inner_hit).trans
      (congrArg (fun x : ℝ => x * st.radius) hα)
  have hPt : dist (P st.t) st.center = st.radius := by
    simpa only [one_mul] using (mem_sphere.mp st.outer_hit)
  have hsmid : P st.s ∈ eventMiddle st.center st.radius := by
    change P st.s ∈ ball st.center (3 * st.radius / 2) ∧
      P st.s ∉ closedBall st.center (3 * st.radius / 4)
    constructor
    · rw [mem_ball, hPs]
      nlinarith only [ha1, hr]
    · rw [mem_closedBall, hPs, not_le]
      nlinarith only [ha34, hr]
  have htmid : P st.t ∈ eventMiddle st.center st.radius := by
    change P st.t ∈ ball st.center (3 * st.radius / 2) ∧
      P st.t ∉ closedBall st.center (3 * st.radius / 4)
    constructor
    · rw [mem_ball, hPt]
      nlinarith only [hr]
    · rw [mem_closedBall, hPt, not_le]
      nlinarith only [hr]
  have hsep : (1 - (aEvt : ℝ)) * st.radius ≤
      dist (P st.s) (P st.t) := by
    have htri := dist_triangle (P st.t) (P st.s) st.center
    rw [dist_comm (P st.t) (P st.s), hPt, hPs] at htri
    nlinarith only [htri]
  have h0far : 2 * st.radius < dist (P 0) st.center := by
    rw [hP0, dist_comm]
    exact st.z_far
  have hTfar : 2 * st.radius < dist (P T) st.center := by
    rw [hPT, dist_comm]
    exact st.w_far
  have h0s : st.radius ≤ dist (P 0) (P st.s) := by
    have htri := dist_triangle (P 0) (P st.s) st.center
    rw [hPs] at htri
    nlinarith only [h0far, htri, ha1, hr]
  have hTs : st.radius ≤ dist (P T) (P st.s) := by
    have htri := dist_triangle (P T) (P st.s) st.center
    rw [hPs] at htri
    nlinarith only [hTfar, htri, ha1, hr]
  have h0t : st.radius ≤ dist (P 0) (P st.t) := by
    have htri := dist_triangle (P 0) (P st.t) st.center
    rw [hPt] at htri
    linarith
  have hTt : st.radius ≤ dist (P T) (P st.t) := by
    have htri := dist_triangle (P T) (P st.t) st.center
    rw [hPt] at htri
    linarith
  exact ⟨hsmall, hsmid, htmid, hsep, h0s, hTs, h0t, hTt⟩

 

theorem CoveredStep.endpoint_loops_of_clause1
    (D : LSCMetric) {P : ℝ → ℂ} {Good : ℂ → ℝ → Prop}
    {ε b α T : ℝ} {z w : ℂ}
    (st : TwoScale.Stopping.CoveredStep P Good ε b α z w)
    (q : Ioo (0 : ℝ) (1 / 100))
    (aEvt : Ioo (1 - (q : ℝ)) 1)
    (θ : ℝ) (hα : α = (aEvt : ℝ))
    (hP : ContinuousOn P (Icc 0 T))
    (hgeo : IsGeodesicCurve (D.pt ∘ P) 0 T)
    (hunit : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 T))
    (hP0 : P 0 = z) (hPT : P T = w)
    (hr : 0 < st.radius) (ha0 : 0 < st.a) (htT : st.t < T)
    (hE1 : EventClause1 D st.center st.radius q θ) :
    EndpointLoopAt D st.radius aEvt θ (P st.s) (P st.t) (P st.s) ∧
      EndpointLoopAt D st.radius aEvt θ (P st.s) (P st.t) (P st.t) := by
  have hαhalf : 1 / 2 < α := by
    rw [hα]
    linarith [aEvt.2.1, q.2.2]
  obtain ⟨σ, τ, hσ0, hσs, htτ, hτT, hinternal⟩ :=
    CoveredStep.internal_boundary_geodesic D st hP hgeo hunit hP0 hPT
      hr hαhalf ha0 htT
  obtain ⟨hsmall, hsmid, htmid, hsep, h0s, hTs, h0t, hTt⟩ :=
    CoveredStep.event_endpoint_geometry st q aEvt hα hP0 hPT hr
  have hq1 : (q : ℝ) < 1 :=
    q.2.2.trans (by norm_num : (1 / 100 : ℝ) < 1)
  have haEvt0 : 0 < (aEvt : ℝ) := by
    linarith [aEvt.2.1, q.2.2]
  exact EventClause1.endpoint_loop_bounds D hr hq1 haEvt0 aEvt.2.2
    hsmall hE1 hinternal hP hgeo hunit (ha0.trans st.a_lt_s)
    st.s_lt_t htT hσs.le htτ.le hsmid htmid hsep
    h0s hTs h0t hTt

 

theorem CoveredStep.attained_increment
    (D D' : LSCMetric) {P : ℝ → ℂ} {Good : ℂ → ℝ → Prop}
    {ε b α T : ℝ} {z w : ℂ}
    (st : TwoScale.Stopping.CoveredStep P Good ε b α z w)
    (ξ Q : ℝ) (q : Ioo (0 : ℝ) (1 / 100))
    (aEvt : Ioo (1 - (q : ℝ)) 1)
    (K : Ioi (1 : ℝ)) (C θ : Ioi (0 : ℝ))
    (Cminus Cplus hCircle : ℝ)
    (hα : α = (aEvt : ℝ))
    (hP : ContinuousOn P (Icc 0 T))
    (hgeo : IsGeodesicCurve (D.pt ∘ P) 0 T)
    (hunit : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 T))
    (hP0 : P 0 = z) (hPT : P T = w)
    (hr : 0 < st.radius) (ha0 : 0 < st.a) (htT : st.t < T)
    (hE : Attained D D' ξ Q st.center ⟨st.radius, hr⟩ q aEvt K C θ
      Cminus Cplus hCircle) :
    D' (P st.s, P st.t) ≤
      ENNReal.ofReal ((C : ℝ) * (st.t - st.s)) := by
  have hαhalf : 1 / 2 < α := by
    rw [hα]
    linarith [aEvt.2.1, q.2.2]
  obtain ⟨σ, τ, hσ0, hσs, htτ, hτT, hinternal⟩ :=
    CoveredStep.internal_boundary_geodesic D st hP hgeo hunit hP0 hPT
      hr hαhalf ha0 htT
  have hE3 : EventClause3 D st.center st.radius q α := by
    simpa only [hα] using hE.2.2.1
  obtain ⟨hgap, hdiam⟩ :=
    CoveredStep.short_segment_of_clause3 D st q.2.1.le q.2.2.le
      hr ha0 hσs.le htτ.le hinternal hE3
  obtain ⟨houterCost, htinyCost⟩ :=
    CoveredStep.outer_and_tiny_bounds D st hP hgeo hunit hP0 hPT
      hr ha0.le htT q
  obtain ⟨_, hsmid, htmid, _, _, _, _, _⟩ :=
    CoveredStep.event_endpoint_geometry st q aEvt hα hP0 hPT hr
  have hhit : ∃ v ∈ Icc σ τ,
      P v ∈ ball (P st.t) ((q : ℝ) * st.radius) :=
    ⟨st.t, ⟨hσs.le.trans st.s_lt_t.le, htτ.le⟩,
      Metric.mem_ball_self (mul_pos q.2.1 hr)⟩
  have hshield := Attained.shield_of_crossing D D' ξ Q st.center
    (P st.t) ⟨st.radius, hr⟩ q aEvt K C θ Cminus Cplus hCircle
    hE hinternal htmid hhit htinyCost
  have hloop := CoveredStep.endpoint_loops_of_clause1 D st q aEvt θ
    hα hP hgeo hunit hP0 hPT hr ha0 htT hE.1
  have hUs : P st.s ∈ sphere st.center ((aEvt : ℝ) * st.radius) := by
    rw [mem_sphere]
    exact (mem_sphere.mp st.inner_hit).trans
      (congrArg (fun x : ℝ => x * st.radius) hα)
  have hUt : P st.t ∈ sphere st.center st.radius := st.outer_hit
  have hCarrier : ∀ j ∈ Icc st.s st.t,
      P j ∈ closedBall st.center st.radius \ ball st.center ((aEvt : ℝ) * st.radius) := by
    intro j hj
    change P j ∈ closedBall st.center st.radius ∧
      P j ∉ ball st.center ((aEvt : ℝ) * st.radius)
    simpa only [hα] using st.annulus_segment j hj
  have htime : D (P st.s, P st.t) = ENNReal.ofReal (st.t - st.s) :=
    hgeo.edist_eq_of_hasUnitSpeedOn hunit
      ⟨(ha0.trans st.a_lt_s).le, st.s_lt_t.le.trans htT.le⟩
      ⟨(ha0.trans st.a_lt_s).le.trans st.s_lt_t.le, htT.le⟩
      st.s_lt_t.le
  have houter : aroundDist D
      ⟨(st.center, (3 * st.radius / 2, 2 * st.radius)), by
        constructor <;> nlinarith⟩ ≤
      ENNReal.ofReal ((1 - (aEvt : ℝ))⁻¹ * st.radius ^ (ξ * Q) *
        Real.exp (ξ * hCircle)) :=
    hE.2.1.trans (min_le_left _ _)
  have hHiii : D (P st.s, P st.t) ≤
      ENNReal.ofReal ((1 - (aEvt : ℝ))⁻¹ * st.radius ^ (ξ * Q) *
        Real.exp (ξ * hCircle)) := houterCost.trans houter
  have htiny : ∃ A : EuclideanAnnulus,
      A.center = P st.t ∧ A.innerRadius = (q : ℝ) * st.radius ∧
      A.outerRadius = Real.sqrt (q : ℝ) * st.radius ∧
      aroundDist D A ≤ ENNReal.ofReal (Cminus / (2 * Cplus)) *
        OptimalConstants.Ratios.setDist D (eventMiddle st.center st.radius)
          (eventBoundary st.center st.radius) := by
    refine ⟨⟨(P st.t, ((q : ℝ) * st.radius,
      Real.sqrt (q : ℝ) * st.radius)),
        TwoScale.Consolidated.loop_annulus_valid hr q.2.1
          (q.2.2.trans (by norm_num : (1 / 100 : ℝ) < 1))⟩,
      rfl, rfl, rfl, ?_⟩
    exact hshield
  have hGeoSeg : OptimalConstants.Ratios.Geodesic D P st.s st.t (P st.s) (P st.t) :=
    geodesic_of_unit_speed D hgeo hunit
      (ha0.trans st.a_lt_s).le st.s_lt_t.le htT.le rfl rfl
  have hE5 := hE.2.2.2.2 (P st.s) (P st.t) hUs hUt hgap htiny
    ⟨P, st.s, st.t, hGeoSeg, hCarrier, hdiam, hHiii, hloop.1, hloop.2⟩
  calc
    D' (P st.s, P st.t) ≤ ENNReal.ofReal (C : ℝ) *
        D (P st.s, P st.t) := hE5
    _ = ENNReal.ofReal ((C : ℝ) * (st.t - st.s)) := by
      rw [htime, ENNReal.ofReal_mul C.2.le]

 

theorem strict_metric_telescope_from_attained (D D' : LSCMetric)
    {P : ℝ → ℂ} {Good : ℂ → ℝ → Prop}
    {ε b α T Cplus C' a : ℝ} {z w : ℂ}
    (steps : List (TwoScale.Stopping.CoveredStep P Good ε b α z w))
    (ξ Q : ℝ) (q : Ioo (0 : ℝ) (1 / 100))
    (aEvt : Ioo (1 - (q : ℝ)) 1)
    (K : Ioi (1 : ℝ)) (C θ : Ioi (0 : ℝ))
    (Cminus : ℝ)
    (hα : α = (aEvt : ℝ))
    (hε : 0 < ε) (hb : 0 < b) (hCC : (C : ℝ) ≤ Cplus)
    (hgap : (C : ℝ) + (K : ℝ) / ((K : ℝ) + 1) *
      (Cplus - (C : ℝ)) < C')
    (hP : ContinuousOn P (Icc 0 T))
    (hgeo : IsGeodesicCurve (D.pt ∘ P) 0 T)
    (hunit : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 T))
    (hP0 : P 0 = z) (hPT : P T = w)
    (hT : 0 < T) (ha : 0 < a)
    (hne : steps ≠ []) (hfrom : TwoScale.Stopping.StepsFrom a steps)
    (hlast : ∀ st ∈ steps, st.t < T)
    (hbilip : ∀ x y : ℂ,
      D' (x, y) ≤ ENNReal.ofReal Cplus * D (x, y))
    (hEvent : ∀ st ∈ steps, ∃ (hr : 0 < st.radius) (hCircle : ℝ),
      Attained D D' ξ Q st.center ⟨st.radius, hr⟩
        q aEvt K C θ Cminus Cplus hCircle) :
    D' (P a, P (TwoScale.Stopping.StepsEnd a steps)) <
      ENNReal.ofReal (C' * T) := by
  have hαhalf : 1 / 2 < α := by
    rw [hα]
    linarith [aEvt.2.1, q.2.2]
  have hα1 : α < 1 := by rw [hα]; exact aEvt.2.2
  have hstarts := TwoScale.Stopping.steps_start_pos steps ha hfrom
  have hEratio : ∀ st ∈ steps, aroundDist D
      ⟨(st.center, (α * st.radius, st.radius)), by
        have hr : 0 < st.radius :=
          (by positivity : 0 < ε ^ 2 * b) |>.trans_le st.radius_min
        constructor <;> nlinarith⟩ ≤
      ENNReal.ofReal (K : ℝ) * acrossDist D
      ⟨(st.center, (α * st.radius, st.radius)), by
        have hr : 0 < st.radius :=
          (by positivity : 0 < ε ^ 2 * b) |>.trans_le st.radius_min
        constructor <;> nlinarith⟩ := by
    intro st hmem
    obtain ⟨hr, hCircle, hE⟩ := hEvent st hmem
    simpa only [hα] using hE.2.2.2.1
  have hEgeo : ∀ st ∈ steps,
      D' (P st.s, P st.t) ≤
        ENNReal.ofReal ((C : ℝ) * (st.t - st.s)) := by
    intro st hmem
    obtain ⟨hr, hCircle, hE⟩ := hEvent st hmem
    exact CoveredStep.attained_increment D D' st ξ Q q aEvt K C θ
      Cminus Cplus hCircle hα hP hgeo hunit hP0 hPT hr
      (hstarts st hmem) (hlast st hmem) hE
  have hK0 : 0 ≤ (K : ℝ) := by
    have hK1 : (1 : ℝ) < (K : ℝ) := K.2
    linarith
  exact TwoScale.Stopping.strict_metric_telescope_from_E D D' steps hε hb
    hαhalf hα1 hK0 C.2.le hCC hgap
    hP hgeo hunit hP0 hPT
    hT ha hne hfrom hlast hbilip hEratio hEgeo

end SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36Events
