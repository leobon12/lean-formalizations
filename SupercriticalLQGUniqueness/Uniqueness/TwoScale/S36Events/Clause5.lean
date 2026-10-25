import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36Events.AttainedEvent
import SupercriticalLQGUniqueness.Uniqueness.TwoScale.Stopping.S35Separator




 





set_option autoImplicit false
noncomputable section
open Set Metric LQGMetric.MetricGeometry
open scoped ENNReal
namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36Events

 
theorem geodesic_of_unit_speed (D : LSCMetric) {P : ℝ → ℂ}
    {T s t : ℝ} {u v : ℂ}
    (hgeo : IsGeodesicCurve (D.pt ∘ P) 0 T)
    (hunit : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 T))
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T)
    (hu : P s = u) (hv : P t = v) :
    OptimalConstants.Ratios.Geodesic D P s t u v := by
  have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs, hst.trans ht⟩
  have htT : t ∈ Icc (0 : ℝ) T := ⟨hs.trans hst, ht⟩
  have hcurve : D.IsCurve P s t :=
    ⟨hst, hgeo.2.1.mono (Icc_subset_Icc hs ht)⟩
  have hlen : D.len P s t = ENNReal.ofReal (t - s) :=
    curveLength_of_hasUnitSpeedOn hunit hsT htT
  have hdist : D (u, v) = ENNReal.ofReal (t - s) := by
    rw [← hu, ← hv]
    exact hgeo.edist_eq_of_hasUnitSpeedOn hunit hsT htT hst
  exact ⟨hcurve, hu, hv, hlen.trans hdist.symm, hdist ▸ ENNReal.ofReal_lt_top⟩

 

theorem internalBoundaryGeodesic_of_unit_speed (D : LSCMetric)
    {P : ℝ → ℂ} {T s t r : ℝ} {z : ℂ}
    (hgeo : IsGeodesicCurve (D.pt ∘ P) 0 T)
    (hunit : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 T))
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T)
    (htrace : ∀ v ∈ Icc s t, P v ∈ eventCarrier z r)
    (hFs : P s ∈ eventBoundary z r)
    (hFt : P t ∈ eventBoundary z r) :
    InternalBoundaryGeodesic D z r P s t := by
  have hstart : P s ∈ eventCarrier z r := htrace s ⟨le_refl s, hst⟩
  have hend : P t ∈ eventCarrier z r := htrace t ⟨hst, le_refl t⟩
  obtain ⟨hcurve, _, _, hlen, hfin⟩ :=
    geodesic_of_unit_speed D hgeo hunit hs hst ht (u := P s) (v := P t) rfl rfl
  have hupper : D.internal (eventCarrier z r) (⟨P s, hstart⟩, ⟨P t, hend⟩) ≤
      D.len P s t := by
    unfold LSCMetric.internal
    exact iInf_le_of_le P (iInf_le_of_le s (iInf_le_of_le t
      (iInf_le_of_le hcurve (iInf_le_of_le htrace
        (iInf_le_of_le rfl (iInf_le_of_le rfl le_rfl))))))
  have hlower : D.len P s t ≤
      D.internal (eventCarrier z r) (⟨P s, hstart⟩, ⟨P t, hend⟩) := by
    rw [hlen]
    rw [LSCMetric.internal_eq_internalEDist]
    exact LQGMetric.MetricGeometry.edist_le_internalEDist
      (X := D.Space) _ _ _
  exact ⟨hstart, hend, hcurve, htrace, hFs, hFt,
    le_antisymm hlower hupper, hlen ▸ hfin⟩

 

theorem EventClause3.diam_le (D : LSCMetric) {z : ℂ} {r q a : ℝ}
    (hE3 : EventClause3 D z r q a)
    {P : ℝ → ℂ} {σ τ s t : ℝ}
    (hinternal : InternalBoundaryGeodesic D z r P σ τ)
    (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hs0 : 0 < s)
    (hσs : σ ≤ s) (htτ : t ≤ τ)
    (hshort : ∀ u ∈ Icc s t,
      P u ∈ closedBall z r \ ball z (a * r)) :
    Metric.diam (P '' Icc s t) ≤ q * r := by
  apply Metric.diam_le_of_forall_dist_le (mul_nonneg hq hr)
  intro x hx y hy
  obtain ⟨u, hu, rfl⟩ := hx
  obtain ⟨v, hv, rfl⟩ := hy
  rcases lt_trichotomy u v with huv | heq | hvu
  · exact hE3 P σ τ hinternal u v (hs0.trans_le hu.1) huv
      ⟨hσs.trans hu.1, hu.2.trans htτ⟩
      ⟨hσs.trans hv.1, hv.2.trans htτ⟩
      (fun w hw => hshort w (Icc_subset_Icc hu.1 hv.2 hw))
  · rw [heq, dist_self]
    exact mul_nonneg hq hr
  · rw [dist_comm]
    exact hE3 P σ τ hinternal v u (hs0.trans_le hv.1) hvu
      ⟨hσs.trans hv.1, hv.2.trans htτ⟩
      ⟨hσs.trans hu.1, hu.2.trans htτ⟩
      (fun w hw => hshort w (Icc_subset_Icc hv.1 hu.2 hw))

 

theorem shield_cost_of_reg_and_outer
    {q θ k : ℝ} (hq : 0 < q)
    {tinyAround tinyAcross outerAround m : ENNReal}
    (hreg : tinyAround ≤ ENNReal.ofReal (q ^ θ) * tinyAcross)
    (hcross : tinyAcross ≤ outerAround)
    (houter : outerAround ≤ ENNReal.ofReal (k * q ^ (-θ)) * m) :
    tinyAround ≤ ENNReal.ofReal k * m := by
  have hpow : 0 ≤ q ^ θ := (Real.rpow_pos_of_pos hq θ).le
  have hpowNeg : 0 ≤ q ^ (-θ) := (Real.rpow_pos_of_pos hq (-θ)).le
  have hprod : q ^ θ * (k * q ^ (-θ)) = k := by
    rw [Real.rpow_neg hq.le]
    have hne : q ^ θ ≠ 0 := (Real.rpow_pos_of_pos hq θ).ne'
    calc
      q ^ θ * (k * (q ^ θ)⁻¹) = k * (q ^ θ * (q ^ θ)⁻¹) := by ring
      _ = k := by simp [hne]
  calc
    tinyAround ≤ ENNReal.ofReal (q ^ θ) * tinyAcross := hreg
    _ ≤ ENNReal.ofReal (q ^ θ) * outerAround := by gcongr
    _ ≤ ENNReal.ofReal (q ^ θ) *
        (ENNReal.ofReal (k * q ^ (-θ)) * m) := by gcongr
    _ = ENNReal.ofReal k * m := by
      rw [← mul_assoc, ← ENNReal.ofReal_mul hpow, hprod]

 
theorem annulus_eq_of_data {A B : EuclideanAnnulus}
    (hc : A.center = B.center)
    (hρ : A.innerRadius = B.innerRadius)
    (hσ : A.outerRadius = B.outerRadius) : A = B := by
  apply Subtype.ext
  exact Prod.ext hc (Prod.ext hρ hσ)

 

theorem EventClause1.at_hit (D : LSCMetric) {z x : ℂ}
    {r q θ δ : ℝ} (hr : 0 < r) (hq : q < 1)
    (hE1 : EventClause1 D z r q θ)
    {P : ℝ → ℂ} {s t : ℝ}
    (hinternal : InternalBoundaryGeodesic D z r P s t)
    (hδ : 0 < δ) (hδq : δ ≤ q)
    (hx : x ∈ eventMiddle z r)
    (hhit : ∃ v ∈ Icc s t, P v ∈ ball x (δ * r)) :
    let A : EuclideanAnnulus :=
      ⟨(x, (δ * r, Real.sqrt δ * r)),
        TwoScale.Consolidated.loop_annulus_valid hr hδ (hδq.trans_lt hq)⟩
    aroundDist D A ≤ ENNReal.ofReal (δ ^ θ) * acrossDist D A := by
  obtain ⟨A, hc, hρ, hσ, hbound⟩ :=
    hE1 P s t hinternal δ hδ hδq x hx hhit
  have hA : A = ⟨(x, (δ * r, Real.sqrt δ * r)),
      TwoScale.Consolidated.loop_annulus_valid hr hδ (hδq.trans_lt hq)⟩ :=
    annulus_eq_of_data hc hρ hσ
  simpa only [hA] using hbound

 

theorem Attained.shield_of_crossing (D D' : LSCMetric)
    (ξ Q : ℝ) (z x : ℂ)
    (r : Ioi (0 : ℝ)) (q : Ioo (0 : ℝ) (1 / 100))
    (a : Ioo (1 - (q : ℝ)) 1) (K : Ioi (1 : ℝ))
    (C θ : Ioi (0 : ℝ))
    (Cminus Cplus hCircle : ℝ)
    (hE : Attained D D' ξ Q z r q a K C θ Cminus Cplus hCircle)
    {P : ℝ → ℂ} {s t : ℝ}
    (hinternal : InternalBoundaryGeodesic D z r P s t)
    (hx : x ∈ eventMiddle z r)
    (hhit : ∃ v ∈ Icc s t, P v ∈ ball x ((q : ℝ) * r))
    (hcross : acrossDist D
      ⟨(x, ((q : ℝ) * r, Real.sqrt (q : ℝ) * r)),
        TwoScale.Consolidated.loop_annulus_valid r.2 q.2.1
          (lt_trans q.2.2 (by norm_num : (1 / 100 : ℝ) < 1))⟩ ≤
      aroundDist D ⟨(z, (3 * r / 2, 2 * r)), by
        have hr : 0 < (r : ℝ) := r.2
        constructor <;> nlinarith⟩) :
    aroundDist D
      ⟨(x, ((q : ℝ) * r, Real.sqrt (q : ℝ) * r)),
        TwoScale.Consolidated.loop_annulus_valid r.2 q.2.1
          (lt_trans q.2.2 (by norm_num : (1 / 100 : ℝ) < 1))⟩ ≤
      ENNReal.ofReal (Cminus / (2 * Cplus)) *
        OptimalConstants.Ratios.setDist D (eventMiddle z r) (eventBoundary z r) := by
  obtain ⟨hE1, hE2, _, _, _⟩ := hE
  have hq1 : (q : ℝ) < 1 :=
    q.2.2.trans (by norm_num : (1 / 100 : ℝ) < 1)
  have hreg := EventClause1.at_hit D r.2 hq1 hE1 hinternal
    q.2.1 le_rfl hx hhit
  have houter : aroundDist D
      ⟨(z, (3 * r / 2, 2 * r)), by
        have hr : 0 < (r : ℝ) := r.2
        constructor <;> nlinarith⟩ ≤
      ENNReal.ofReal (Cminus / (2 * Cplus) * (q : ℝ) ^ (-(θ : ℝ))) *
        OptimalConstants.Ratios.setDist D (eventMiddle z r) (eventBoundary z r) :=
    hE2.trans (min_le_right _ _)
  exact shield_cost_of_reg_and_outer q.2.1 hreg hcross houter

theorem isOpen_eventOpen (z : ℂ) (r : ℝ) :
    IsOpen (eventOpen z r) := by
  unfold eventOpen
  exact isOpen_ball.sdiff isClosed_closedBall

theorem isClosed_eventCarrier (z : ℂ) (r : ℝ) :
    IsClosed (eventCarrier z r) := by
  unfold eventCarrier
  exact isClosed_closedBall.sdiff isOpen_ball

theorem eventOpen_subset_carrier (z : ℂ) (r : ℝ) :
    eventOpen z r ⊆ eventCarrier z r := by
  intro x hx
  change x ∈ ball z (2 * r) ∧ x ∉ closedBall z (r / 2) at hx
  change x ∈ closedBall z (2 * r) ∧ x ∉ ball z (r / 2)
  exact ⟨ball_subset_closedBall hx.1,
    fun hb => hx.2 (ball_subset_closedBall hb)⟩

theorem eventBoundary_of_carrier_not_open {z x : ℂ} {r : ℝ}
    (hY : x ∈ eventCarrier z r) (hO : x ∉ eventOpen z r) :
    x ∈ eventBoundary z r := by
  change x ∈ closedBall z (2 * r) ∧ x ∉ ball z (r / 2) at hY
  change ¬(x ∈ ball z (2 * r) ∧ x ∉ closedBall z (r / 2)) at hO
  change x ∈ sphere z (r / 2) ∪ sphere z (2 * r)
  have hinner : r / 2 ≤ dist x z := le_of_not_gt hY.2
  have houter : dist x z ≤ 2 * r := Metric.mem_closedBall.mp hY.1
  by_cases h : dist x z = r / 2
  · exact Or.inl (Metric.mem_sphere.mpr h)
  · right
    apply Metric.mem_sphere.mpr
    have hnotInner : x ∉ closedBall z (r / 2) := by
      intro hx
      exact h (le_antisymm (Metric.mem_closedBall.mp hx) hinner)
    have hnotOuter : x ∉ ball z (2 * r) := by
      intro hx
      exact hO ⟨hx, hnotInner⟩
    exact le_antisymm houter (le_of_not_gt hnotOuter)

 

theorem event_boundary_excursion {P : ℝ → ℂ}
    {T s t r : ℝ} {z : ℂ}
    (hP : ContinuousOn P (Icc 0 T))
    (hs0 : 0 < s) (hst : s < t) (htT : t < T)
    (hP0 : P 0 ∉ eventOpen z r)
    (hPT : P T ∉ eventOpen z r)
    (hshort : ∀ u ∈ Icc s t, P u ∈ eventOpen z r) :
    ∃ σ τ : ℝ, 0 ≤ σ ∧ σ < s ∧ t < τ ∧ τ ≤ T ∧
      P σ ∈ eventBoundary z r ∧ P τ ∈ eventBoundary z r ∧
      ∀ u ∈ Icc σ τ, P u ∈ eventCarrier z r := by
  let O := eventOpen z r
  let σ := sSup {u ∈ Icc 0 s | P u ∉ O}
  let τ := sInf {u ∈ Icc s T | P u ∉ O}
  have hq : s ∈ Ioo (0 : ℝ) T := ⟨hs0, hst.trans htT⟩
  have hcomp := Toolkit.PlanarSeparation.excursionComponentCode
    (P := P) (O := O) (T := T) (q := s) (by linarith) hP
      (isOpen_eventOpen z r) hP0 hPT hq
      (hshort s ⟨le_refl s, hst.le⟩)
  change 0 ≤ σ ∧ σ < s ∧ s < τ ∧ τ ≤ T ∧
    P σ ∉ O ∧ P τ ∉ O ∧ ∀ u ∈ Ioo σ τ, P u ∈ O at hcomp
  obtain ⟨hσ0, hσs, hsτ, hτT, hσoff, hτoff, hinside⟩ := hcomp
  have htτ : t < τ := by
    by_contra hn
    have hτt : τ ≤ t := le_of_not_gt hn
    exact hτoff (hshort τ ⟨hsτ.le, hτt⟩)
  have hστ : σ < τ := hσs.trans hsτ
  have hmap : MapsTo P (Ioo σ τ) O := hinside
  have hcont : ContinuousOn P (closure (Ioo σ τ)) := by
    rw [closure_Ioo hστ.ne]
    exact hP.mono (Icc_subset_Icc hσ0 hτT)
  have hcl : MapsTo P (closure (Ioo σ τ)) (closure O) :=
    hmap.closure_of_continuousOn hcont
  have hYcl : closure O ⊆ eventCarrier z r :=
    closure_minimal (eventOpen_subset_carrier z r) (isClosed_eventCarrier z r)
  have htrace : ∀ u ∈ Icc σ τ, P u ∈ eventCarrier z r := by
    intro u hu
    apply hYcl
    apply hcl
    rw [closure_Ioo hστ.ne]
    exact hu
  exact ⟨σ, τ, hσ0, hσs, htτ, hτT,
    eventBoundary_of_carrier_not_open (htrace σ ⟨le_rfl, hστ.le⟩) hσoff,
    eventBoundary_of_carrier_not_open (htrace τ ⟨hστ.le, le_rfl⟩) hτoff,
    htrace⟩

 

theorem CoveredStep.internal_boundary_geodesic
    (D : LSCMetric) {P : ℝ → ℂ} {Good : ℂ → ℝ → Prop}
    {ε b α T : ℝ} {z w : ℂ}
    (st : TwoScale.Stopping.CoveredStep P Good ε b α z w)
    (hP : ContinuousOn P (Icc 0 T))
    (hgeo : IsGeodesicCurve (D.pt ∘ P) 0 T)
    (hunit : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 T))
    (hP0 : P 0 = z) (hPT : P T = w)
    (hr : 0 < st.radius) (hα : 1 / 2 < α)
    (ha0 : 0 < st.a) (htT : st.t < T) :
    ∃ σ τ : ℝ, 0 ≤ σ ∧ σ < st.s ∧ st.t < τ ∧ τ ≤ T ∧
      InternalBoundaryGeodesic D st.center st.radius P σ τ := by
  have hshort : ∀ u ∈ Icc st.s st.t,
      P u ∈ eventOpen st.center st.radius := by
    intro u hu
    obtain ⟨hOuter, hInner⟩ := st.annulus_segment u hu
    change P u ∈ ball st.center (2 * st.radius) ∧
      P u ∉ closedBall st.center (st.radius / 2)
    have hOuter' : dist (P u) st.center ≤ st.radius :=
      Metric.mem_closedBall.mp hOuter
    have hInner' : α * st.radius ≤ dist (P u) st.center :=
      le_of_not_gt hInner
    constructor
    · exact Metric.mem_ball.mpr (by linarith)
    · intro hbad
      have hbad' : dist (P u) st.center ≤ st.radius / 2 :=
        Metric.mem_closedBall.mp hbad
      nlinarith
  have hstart : P 0 ∉ eventOpen st.center st.radius := by
    rw [hP0]
    intro h
    have hdist : dist z st.center < 2 * st.radius := Metric.mem_ball.mp h.1
    rw [dist_comm] at hdist
    exact (not_lt_of_ge st.z_far.le) hdist
  have hend : P T ∉ eventOpen st.center st.radius := by
    rw [hPT]
    intro h
    have hdist : dist w st.center < 2 * st.radius := Metric.mem_ball.mp h.1
    rw [dist_comm] at hdist
    exact (not_lt_of_ge st.w_far.le) hdist
  obtain ⟨σ, τ, hσ0, hσs, htτ, hτT, hFs, hFt, htrace⟩ :=
    event_boundary_excursion hP (ha0.trans st.a_lt_s) st.s_lt_t htT
      hstart hend hshort
  have hστ : σ ≤ τ := (hσs.trans st.s_lt_t).trans htτ |>.le
  refine ⟨σ, τ, hσ0, hσs, htτ, hτT, ?_⟩
  exact internalBoundaryGeodesic_of_unit_speed D hgeo hunit
    hσ0 hστ hτT htrace hFs hFt

 

theorem CoveredStep.short_segment_of_clause3
    (D : LSCMetric) {P : ℝ → ℂ} {Good : ℂ → ℝ → Prop}
    {ε b α q : ℝ} {z w : ℂ}
    (st : TwoScale.Stopping.CoveredStep P Good ε b α z w)
    (hq : 0 ≤ q) (hqsmall : q ≤ 1 / 100)
    (hr : 0 < st.radius) (ha0 : 0 < st.a)
    {σ τ : ℝ} (hσs : σ ≤ st.s) (htτ : st.t ≤ τ)
    (hinternal : InternalBoundaryGeodesic D st.center st.radius P σ τ)
    (hE3 : EventClause3 D st.center st.radius q α) :
    dist (P st.s) (P st.t) ≤ q * st.radius ∧
      Metric.diam (P '' Icc st.s st.t) ≤ st.radius / 100 := by
  have hs0 : 0 < st.s := ha0.trans st.a_lt_s
  have hshort : ∀ u ∈ Icc st.s st.t,
      P u ∈ closedBall st.center st.radius \ ball st.center (α * st.radius) := by
    intro u hu
    exact st.annulus_segment u hu
  have hdist : dist (P st.s) (P st.t) ≤ q * st.radius :=
    hE3 P σ τ hinternal st.s st.t hs0 st.s_lt_t
      ⟨hσs, st.s_lt_t.le.trans htτ⟩
      ⟨hσs.trans st.s_lt_t.le, htτ⟩ hshort
  have hdiam : Metric.diam (P '' Icc st.s st.t) ≤ q * st.radius :=
    EventClause3.diam_le D hE3 hinternal hq hr.le hs0 hσs htτ hshort
  exact ⟨hdist, hdiam.trans (by
    have hmul := mul_le_mul_of_nonneg_right hqsmall hr.le
    nlinarith only [hmul])⟩

 

theorem CoveredStep.outer_and_tiny_bounds
    (D : LSCMetric) {P : ℝ → ℂ} {Good : ℂ → ℝ → Prop}
    {ε b α T : ℝ} {z w : ℂ}
    (st : TwoScale.Stopping.CoveredStep P Good ε b α z w)
    (hP : ContinuousOn P (Icc 0 T))
    (hgeo : IsGeodesicCurve (D.pt ∘ P) 0 T)
    (hunit : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 T))
    (hP0 : P 0 = z) (hPT : P T = w)
    (hr : 0 < st.radius) (ha0 : 0 ≤ st.a) (htT : st.t < T)
    (q : Ioo (0 : ℝ) (1 / 100)) :
    D (P st.s, P st.t) ≤
      aroundDist D ⟨(st.center, (3 * st.radius / 2, 2 * st.radius)),
        by constructor <;> nlinarith⟩ ∧
    acrossDist D
      ⟨(P st.t, ((q : ℝ) * st.radius, Real.sqrt (q : ℝ) * st.radius)),
        TwoScale.Consolidated.loop_annulus_valid hr q.2.1
          (q.2.2.trans (by norm_num : (1 / 100 : ℝ) < 1))⟩ ≤
      aroundDist D ⟨(st.center, (3 * st.radius / 2, 2 * st.radius)),
        by constructor <;> nlinarith⟩ := by
  have hq1 : (q : ℝ) < 1 :=
    q.2.2.trans (by norm_num : (1 / 100 : ℝ) < 1)
  have hρ : 0 < (q : ℝ) * st.radius := mul_pos q.2.1 hr
  have hρσ : (q : ℝ) * st.radius <
      Real.sqrt (q : ℝ) * st.radius :=
    mul_lt_mul_of_pos_right (TwoScale.Consolidated.lt_sqrt_self q.2.1 hq1) hr
  have hσ : Real.sqrt (q : ℝ) * st.radius < st.radius / 2 := by
    have hroot : Real.sqrt (q : ℝ) < 1 / 2 :=
      (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1 / 2)).2 (by
        nlinarith only [q.2.2])
    nlinarith only [mul_lt_mul_of_pos_right hroot hr]
  obtain ⟨s', t', _, _, hgap, houter, hcross⟩ :=
    TwoScale.Stopping.covered_step_loop_bounds D st hP hgeo hunit hP0 hPT
      hr ha0 htT hρ hρσ hσ
  have hsT : st.s ∈ Icc (0 : ℝ) T :=
    ⟨ha0.trans st.a_lt_s.le, st.s_lt_t.le.trans htT.le⟩
  have htT' : st.t ∈ Icc (0 : ℝ) T :=
    ⟨(ha0.trans st.a_lt_s.le).trans st.s_lt_t.le, htT.le⟩
  have hdist : D (P st.s, P st.t) = ENNReal.ofReal (st.t - st.s) :=
    hgeo.edist_eq_of_hasUnitSpeedOn hunit hsT htT' st.s_lt_t.le
  constructor
  · rw [hdist]
    exact (ENNReal.ofReal_le_ofReal hgap).trans houter
  · exact hcross.trans houter

 

theorem across_le_geodesic_from_start (D : LSCMetric) {P : ℝ → ℂ}
    {T s t ρ σ : ℝ}
    (hP : ContinuousOn P (Icc 0 T))
    (hgeo : IsGeodesicCurve (D.pt ∘ P) 0 T)
    (hunit : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 T))
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T)
    (hρ : 0 < ρ) (hρσ : ρ < σ)
    (hfar : σ ≤ dist (P t) (P s)) :
    acrossDist D ⟨(P s, (ρ, σ)), ⟨hρ, hρσ⟩⟩ ≤ D (P s, P t) := by
  have hPc : ContinuousOn P (Icc s t) :=
    hP.mono (Icc_subset_Icc hs ht)
  have hf : ContinuousOn (fun u => dist (P u) (P s)) (Icc s t) :=
    continuous_dist.comp_continuousOn (hPc.prodMk continuousOn_const)
  obtain ⟨u, v, hsu, huv, hvt, hu, hv, _⟩ :=
    LQGMetric.RectCross.exists_sub_crossing hst hf hρσ.le
      (by rw [dist_self]; exact hρ.le) hfar
  have hcross : acrossDist D ⟨(P s, (ρ, σ)), ⟨hρ, hρσ⟩⟩ ≤
      D (P u, P v) := by
    unfold acrossDist
    exact iInf_le_of_le (P u) (iInf_le_of_le
      (by simpa only [EuclideanAnnulus.innerBoundary, EuclideanAnnulus.center,
          EuclideanAnnulus.innerRadius, mem_sphere] using hu)
      (iInf_le_of_le (P v) (iInf_le_of_le
        (by simpa only [EuclideanAnnulus.outerBoundary, EuclideanAnnulus.center,
            EuclideanAnnulus.outerRadius, mem_sphere] using hv) le_rfl)))
  have huT : u ∈ Icc (0 : ℝ) T :=
    ⟨hs.trans hsu, (huv.trans hvt).trans ht⟩
  have hvT : v ∈ Icc (0 : ℝ) T :=
    ⟨hs.trans (hsu.trans huv), hvt.trans ht⟩
  have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs, hst.trans ht⟩
  have htT : t ∈ Icc (0 : ℝ) T := ⟨hs.trans hst, ht⟩
  have hduv : D (P u, P v) = ENNReal.ofReal (v - u) :=
    hgeo.edist_eq_of_hasUnitSpeedOn hunit huT hvT huv
  have hdst : D (P s, P t) = ENNReal.ofReal (t - s) :=
    hgeo.edist_eq_of_hasUnitSpeedOn hunit hsT htT hst
  calc
    acrossDist D ⟨(P s, (ρ, σ)), ⟨hρ, hρσ⟩⟩ ≤ D (P u, P v) := hcross
    _ = ENNReal.ofReal (v - u) := hduv
    _ ≤ ENNReal.ofReal (t - s) := ENNReal.ofReal_le_ofReal (by linarith)
    _ = D (P s, P t) := hdst.symm

 
theorem across_le_geodesic_from_end (D : LSCMetric) {P : ℝ → ℂ}
    {T s t ρ σ : ℝ}
    (hP : ContinuousOn P (Icc 0 T))
    (hgeo : IsGeodesicCurve (D.pt ∘ P) 0 T)
    (hunit : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 T))
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T)
    (hρ : 0 < ρ) (hρσ : ρ < σ)
    (hfar : σ ≤ dist (P s) (P t)) :
    acrossDist D ⟨(P t, (ρ, σ)), ⟨hρ, hρσ⟩⟩ ≤ D (P s, P t) := by
  have hPc : ContinuousOn P (Icc s t) :=
    hP.mono (Icc_subset_Icc hs ht)
  have hf : ContinuousOn (fun u => dist (P u) (P t)) (Icc s t) :=
    continuous_dist.comp_continuousOn (hPc.prodMk continuousOn_const)
  obtain ⟨u, v, hsu, huv, hvt, hu, hv, _⟩ :=
    LQGMetric.RectCross.exists_sub_crossing' hst hf hρσ.le
      hfar (by rw [dist_self]; exact hρ.le)
  have hcross : acrossDist D ⟨(P t, (ρ, σ)), ⟨hρ, hρσ⟩⟩ ≤
      D (P v, P u) := by
    unfold acrossDist
    exact iInf_le_of_le (P v) (iInf_le_of_le
      (by simpa only [EuclideanAnnulus.innerBoundary, EuclideanAnnulus.center,
          EuclideanAnnulus.innerRadius, mem_sphere] using hv)
      (iInf_le_of_le (P u) (iInf_le_of_le
        (by simpa only [EuclideanAnnulus.outerBoundary, EuclideanAnnulus.center,
            EuclideanAnnulus.outerRadius, mem_sphere] using hu) le_rfl)))
  have huT : u ∈ Icc (0 : ℝ) T :=
    ⟨hs.trans hsu, (huv.trans hvt).trans ht⟩
  have hvT : v ∈ Icc (0 : ℝ) T :=
    ⟨hs.trans (hsu.trans huv), hvt.trans ht⟩
  have hsT : s ∈ Icc (0 : ℝ) T := ⟨hs, hst.trans ht⟩
  have htT : t ∈ Icc (0 : ℝ) T := ⟨hs.trans hst, ht⟩
  have hduv : D (P u, P v) = ENNReal.ofReal (v - u) :=
    hgeo.edist_eq_of_hasUnitSpeedOn hunit huT hvT huv
  have hdst : D (P s, P t) = ENNReal.ofReal (t - s) :=
    hgeo.edist_eq_of_hasUnitSpeedOn hunit hsT htT hst
  calc
    acrossDist D ⟨(P t, (ρ, σ)), ⟨hρ, hρσ⟩⟩ ≤ D (P v, P u) := hcross
    _ = D (P u, P v) := D.2.1.2.2.1 _ _
    _ = ENNReal.ofReal (v - u) := hduv
    _ ≤ ENNReal.ofReal (t - s) := ENNReal.ofReal_le_ofReal (by linarith)
    _ = D (P s, P t) := hdst.symm

 
theorem EventClause1.endpoint_around_bounds (D : LSCMetric)
    {z : ℂ} {r q θ T σ τ s t δ : ℝ} {P : ℝ → ℂ}
    (hr : 0 < r) (hq : q < 1)
    (hE1 : EventClause1 D z r q θ)
    (hinternal : InternalBoundaryGeodesic D z r P σ τ)
    (hP : ContinuousOn P (Icc 0 T))
    (hgeo : IsGeodesicCurve (D.pt ∘ P) 0 T)
    (hunit : HasUnitSpeedOn (D.pt ∘ P) (Icc 0 T))
    (hs0 : 0 ≤ s) (hst : s ≤ t) (htT : t ≤ T)
    (hσs : σ ≤ s) (htτ : t ≤ τ)
    (hsmid : P s ∈ eventMiddle z r) (htmid : P t ∈ eventMiddle z r)
    (hδ : 0 < δ) (hδq : δ ≤ q)
    (hfar : Real.sqrt δ * r ≤ dist (P s) (P t)) :
    let As : EuclideanAnnulus :=
      ⟨(P s, (δ * r, Real.sqrt δ * r)),
        TwoScale.Consolidated.loop_annulus_valid hr hδ (hδq.trans_lt hq)⟩
    let At : EuclideanAnnulus :=
      ⟨(P t, (δ * r, Real.sqrt δ * r)),
        TwoScale.Consolidated.loop_annulus_valid hr hδ (hδq.trans_lt hq)⟩
    aroundDist D As ≤ ENNReal.ofReal (δ ^ θ) * D (P s, P t) ∧
    aroundDist D At ≤ ENNReal.ofReal (δ ^ θ) * D (P s, P t) := by
  have hρ : 0 < δ * r := mul_pos hδ hr
  have hρσ : δ * r < Real.sqrt δ * r :=
    mul_lt_mul_of_pos_right (TwoScale.Consolidated.lt_sqrt_self hδ (hδq.trans_lt hq)) hr
  have hsint : s ∈ Icc σ τ := ⟨hσs, hst.trans htτ⟩
  have htint : t ∈ Icc σ τ := ⟨hσs.trans hst, htτ⟩
  have hsreg := EventClause1.at_hit D hr hq hE1 hinternal
    hδ hδq hsmid ⟨s, hsint, by simpa using (Metric.mem_ball_self hρ :
      P s ∈ ball (P s) (δ * r))⟩
  have htreg := EventClause1.at_hit D hr hq hE1 hinternal
    hδ hδq htmid ⟨t, htint, by simpa using (Metric.mem_ball_self hρ :
      P t ∈ ball (P t) (δ * r))⟩
  constructor
  · calc
      _ ≤ ENNReal.ofReal (δ ^ θ) * acrossDist D _ := hsreg
      _ ≤ ENNReal.ofReal (δ ^ θ) * D (P s, P t) := by
        gcongr
        exact across_le_geodesic_from_start D hP hgeo hunit
          hs0 hst htT hρ hρσ (by rw [dist_comm]; exact hfar)
  · calc
      _ ≤ ENNReal.ofReal (δ ^ θ) * acrossDist D _ := htreg
      _ ≤ ENNReal.ofReal (δ ^ θ) * D (P s, P t) := by
        gcongr
        exact across_le_geodesic_from_end D hP hgeo hunit
          hs0 hst htT hρ hρσ hfar

end SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36Events
