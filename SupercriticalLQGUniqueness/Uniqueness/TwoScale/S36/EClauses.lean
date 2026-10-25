import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.IntCode




 













set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36

 

theorem isCompact_eventCarrier (z : ℂ) (r : ℝ) : IsCompact (TwoScale.S36Events.eventCarrier z r) :=
  (isCompact_closedBall _ _).diff Metric.isOpen_ball

theorem isClosed_eventBoundary (z : ℂ) (r : ℝ) : IsClosed (TwoScale.S36Events.eventBoundary z r) :=
  Metric.isClosed_sphere.union Metric.isClosed_sphere

theorem isOpen_eventMiddle (z : ℂ) (r : ℝ) : IsOpen (TwoScale.S36Events.eventMiddle z r) :=
  Metric.isOpen_ball.sdiff Metric.isClosed_closedBall

 
def shortCarrier (z : ℂ) (r a : ℝ) : Set ℂ :=
  Metric.closedBall z r \ Metric.ball z (a * r)

theorem isCompact_shortCarrier (z : ℂ) (r a : ℝ) : IsCompact (shortCarrier z r a) :=
  (isCompact_closedBall _ _).diff Metric.isOpen_ball

 
theorem ibg_iff (D : LSCMetric) (z : ℂ) (r : ℝ) (P : ℝ → ℂ) (s t : ℝ) :
    TwoScale.S36Events.InternalBoundaryGeodesic D z r P s t ↔
      IsIntGeod D (TwoScale.S36Events.eventCarrier z r) P s t ∧ P s ∈ TwoScale.S36Events.eventBoundary z r ∧
        P t ∈ TwoScale.S36Events.eventBoundary z r := by
  constructor
  · rintro ⟨hu, hv, hc, htr, hs, ht, hlen, hfin⟩
    exact ⟨⟨hc, htr, hlen, hfin⟩, hs, ht⟩
  · rintro ⟨⟨hc, htr, hlen, hfin⟩, hs, ht⟩
    exact ⟨htr s ⟨le_rfl, hc.1⟩, htr t ⟨hc.1, le_rfl⟩, hc, htr, hs, ht, hlen, hfin⟩

 
theorem annulus_eq_mk {A : EuclideanAnnulus} {x : ℂ} {ρ σ : ℝ} (hc : A.center = x)
    (hi : A.innerRadius = ρ) (ho : A.outerRadius = σ) (h : 0 < ρ ∧ ρ < σ) :
    A = ⟨(x, (ρ, σ)), h⟩ :=
  Subtype.ext (Prod.ext hc (Prod.ext hi ho))

 

 
def E1Code (D : LSCMetric) (z : ℂ) (r q θ : ℝ) : Prop :=
  ∀ (γ : PathCode) (δ : ℝ) (x : ℂ), IsIntCode D (TwoScale.S36Events.eventCarrier z r) γ →
    γ 0 ∈ TwoScale.S36Events.eventBoundary z r → γ 1 ∈ TwoScale.S36Events.eventBoundary z r →
    0 < δ → δ ≤ q → x ∈ TwoScale.S36Events.eventMiddle z r → (∃ τ, γ τ ∈ Metric.ball x (δ * r)) →
    TwoScale.Consolidated.aroundAt D x (δ * r) (Real.sqrt δ * r) ≤
      ENNReal.ofReal (δ ^ θ) * TwoScale.S36Events.spherePairInf D x (δ * r) (Real.sqrt δ * r)

theorem eventClause1_iff_code (D : LSCMetric) (z : ℂ) {r q : ℝ} (θ : ℝ) (hr : 0 < r)
    (hq : q < 1) : TwoScale.S36Events.EventClause1 D z r q θ ↔ E1Code D z r q θ := by
  have hY := isCompact_eventCarrier z r
  constructor
  · intro hE γ δ x hγ hγ0 hγ1 hδ0 hδq hx hhit
    obtain ⟨τ, hτ⟩ := hhit
    have hδ1 : δ < 1 := hδq.trans_lt hq
    have hP := intGeod_of_intCode hγ
    have hibg : TwoScale.S36Events.InternalBoundaryGeodesic D z r (codeExt γ) 0 1 := by
      refine (ibg_iff D z r _ 0 1).mpr ⟨hP, ?_, ?_⟩
      · rw [codeExt_zero]
        exact hγ0
      · rw [codeExt_one]
        exact hγ1
    have hhit' : ∃ v ∈ Icc (0 : ℝ) 1, codeExt γ v ∈ Metric.ball x (δ * r) :=
      ⟨τ, τ.2, by rw [codeExt_of_mem γ τ.2]; exact hτ⟩
    obtain ⟨A, hc, hi, ho, hA⟩ := hE (codeExt γ) 0 1 hibg δ hδ0 hδq x hx hhit'
    have hvalid := TwoScale.Consolidated.loop_annulus_valid hr hδ0 hδ1
    have hAeq : A = ⟨(x, (δ * r, Real.sqrt δ * r)), hvalid⟩ := annulus_eq_mk hc hi ho hvalid
    rw [TwoScale.Consolidated.aroundAt_eq D x _ _ hvalid]
    subst hAeq
    exact hA
  · intro hC P s t hibg δ hδ0 hδq x hx hhit
    obtain ⟨v, hv, hvx⟩ := hhit
    have hδ1 : δ < 1 := hδq.trans_lt hq
    obtain ⟨hP, hs, ht⟩ := (ibg_iff D z r P s t).mp hibg
    obtain ⟨γ, hγ, hγ0, hγ1, -, hseg⟩ := exists_intCode_of_intGeod hY hP
    obtain ⟨σ, -, -, hσ, -, -⟩ := hseg v hv v hv le_rfl
    have hvalid := TwoScale.Consolidated.loop_annulus_valid hr hδ0 hδ1
    refine ⟨⟨(x, (δ * r, Real.sqrt δ * r)), hvalid⟩, rfl, rfl, rfl, ?_⟩
    have hγ0F : γ 0 ∈ TwoScale.S36Events.eventBoundary z r := by rw [hγ0]; exact hs
    have hγ1F : γ 1 ∈ TwoScale.S36Events.eventBoundary z r := by rw [hγ1]; exact ht
    have h := hC γ δ x hγ hγ0F hγ1F hδ0 hδq hx ⟨σ, by rw [hσ]; exact hvx⟩
    rw [TwoScale.Consolidated.aroundAt_eq D x _ _ hvalid] at h
    exact h

 

 
def E3Code (D : LSCMetric) (z : ℂ) (r q a : ℝ) : Prop :=
  ∀ (γ : PathCode) (σ σ' : ℝ), IsIntCode D (TwoScale.S36Events.eventCarrier z r) γ →
    γ 0 ∈ TwoScale.S36Events.eventBoundary z r → γ 1 ∈ TwoScale.S36Events.eventBoundary z r →
    0 ≤ σ → σ ≤ σ' → σ' ≤ 1 →
    (∀ τ : ℝ, codeExt γ (max σ (min σ' τ)) ∈ shortCarrier z r a) →
    dist (codeExt γ σ) (codeExt γ σ') ≤ q * r

theorem eventClause3_iff_code (D : LSCMetric) (z : ℂ) {r q : ℝ} (a : ℝ) (hr : 0 < r)
    (hq : 0 < q) : TwoScale.S36Events.EventClause3 D z r q a ↔ E3Code D z r q a := by
  have hY := isCompact_eventCarrier z r
  constructor
  · intro hE γ σ σ' hγ hγ0 hγ1 hσ0 hσσ' hσ'1 hseg
    rcases eq_or_lt_of_le hσσ' with heq | hlt
    · rw [heq, dist_self]
      exact (mul_pos hq hr).le
    · let P' : ℝ → ℂ := fun τ => codeExt γ (τ - 1)
      have hP' : IsIntGeod D (TwoScale.S36Events.eventCarrier z r) P' 1 2 := intGeod_shift_of_intCode hγ
      have hibg : TwoScale.S36Events.InternalBoundaryGeodesic D z r P' 1 2 := by
        refine (ibg_iff D z r P' 1 2).mpr ⟨hP', ?_, ?_⟩
        · change codeExt γ (1 - 1) ∈ _
          rw [sub_self, codeExt_zero]
          exact hγ0
        · change codeExt γ (2 - 1) ∈ _
          norm_num
          rw [codeExt_one]
          exact hγ1
      have h := hE P' 1 2 hibg (1 + σ) (1 + σ') (by linarith) (by linarith)
        ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ (by
          intro τ hτ
          have hm : max σ (min σ' (τ - 1)) = τ - 1 := by
            rw [min_eq_right (by linarith [hτ.2]), max_eq_right (by linarith [hτ.1])]
          have h1 := hseg (τ - 1)
          rw [hm] at h1
          exact h1)
      change dist (codeExt γ (1 + σ - 1)) (codeExt γ (1 + σ' - 1)) ≤ q * r at h
      simpa only [add_sub_cancel_left] using h
  · intro hC P s t hibg v w hv0 hvw hv hw hsegP
    obtain ⟨hP, hs, ht⟩ := (ibg_iff D z r P s t).mp hibg
    obtain ⟨γ, hγ, hγ0, hγ1, -, hseg⟩ := exists_intCode_of_intGeod hY hP
    obtain ⟨σ, σ', hσσ', hσ, hσ', hmid⟩ := hseg v hv w hw hvw.le
    have hγ0F : γ 0 ∈ TwoScale.S36Events.eventBoundary z r := by rw [hγ0]; exact hs
    have hγ1F : γ 1 ∈ TwoScale.S36Events.eventBoundary z r := by rw [hγ1]; exact ht
    have h := hC γ σ σ' hγ hγ0F hγ1F σ.2.1 hσσ' σ'.2.2 (by
      intro τ
      have hm1 : (σ : ℝ) ≤ max (σ : ℝ) (min (σ' : ℝ) τ) := le_max_left _ _
      have hm2 : max (σ : ℝ) (min (σ' : ℝ) τ) ≤ σ' := max_le hσσ' (min_le_left _ _)
      have hmem : max (σ : ℝ) (min (σ' : ℝ) τ) ∈ Icc (0 : ℝ) 1 :=
        ⟨σ.2.1.trans hm1, hm2.trans σ'.2.2⟩
      rw [codeExt_of_mem γ hmem]
      obtain ⟨x, hx, hxeq⟩ := hmid ⟨_, hmem⟩ hm1 hm2
      rw [hxeq]
      exact hsegP x hx)
    rw [codeExt_of_mem γ σ.2, codeExt_of_mem γ σ'.2] at h
    rw [← hσ, ← hσ']
    exact h

 

 
def aWin {q : Ioo (0 : ℝ) (1 / 100)} (a : Ioo (1 - (q : ℝ)) 1) : Ioo (3 / 4 : ℝ) 1 :=
  ⟨a, by have := q.2.2; have := a.2.1; linarith, a.2.2⟩

theorem endpointLoopAt_iff (D : LSCMetric) (r : Ioi (0 : ℝ)) {q : Ioo (0 : ℝ) (1 / 100)}
    (a : Ioo (1 - (q : ℝ)) 1) (θ : Ioi (0 : ℝ)) (u v x : ℂ) :
    TwoScale.S36Events.EndpointLoopAt D r a θ u v x ↔ OptimalConstants.Ratios.EndpointLoop D r (aWin a) θ u v x :=
  Iff.rfl

 
def E5Code (D D' : LSCMetric) (ξ Q : ℝ) (z : ℂ) (r : Ioi (0 : ℝ))
    (q : Ioo (0 : ℝ) (1 / 100)) (a : Ioo (1 - (q : ℝ)) 1) (C θ : Ioi (0 : ℝ))
    (Cminus Cplus : ℝ) (c : ℝ) : Prop :=
  ∀ (u v : ℂ) (γ : PathCode), u ∈ Metric.sphere z (a * r) → v ∈ Metric.sphere z r →
    dist u v ≤ q * r →
    TwoScale.Consolidated.aroundAt D v (q * r) (Real.sqrt q * r) ≤ ENNReal.ofReal (Cminus / (2 * Cplus)) *
      OptimalConstants.Ratios.setDist D (TwoScale.S36Events.eventMiddle z r) (TwoScale.S36Events.eventBoundary z r) →
    IsGeoCode D γ → γ 0 = u → γ 1 = v → (∀ τ, γ τ ∈ shortCarrier z r a) →
    (∀ τ₁ τ₂, dist (γ τ₁) (γ τ₂) ≤ (r : ℝ) / 100) →
    D (u, v) ≤ ENNReal.ofReal ((1 - (a : ℝ))⁻¹ * (r : ℝ) ^ (ξ * Q) * Real.exp (ξ * c)) →
    (D, (u, D (u, v))) ∈ LoopSet r (aWin a) θ → (D, (v, D (u, v))) ∈ LoopSet r (aWin a) θ →
    D' (u, v) ≤ ENNReal.ofReal C * D (u, v)

 
def E5Lit (D D' : LSCMetric) (ξ Q : ℝ) (z : ℂ) (r : Ioi (0 : ℝ))
    (q : Ioo (0 : ℝ) (1 / 100)) (a : Ioo (1 - (q : ℝ)) 1) (C θ : Ioi (0 : ℝ))
    (Cminus Cplus : ℝ) (c : ℝ) : Prop :=
  ∀ u v : ℂ, u ∈ Metric.sphere z (a * r) →
    v ∈ Metric.sphere z r → dist u v ≤ q * r →
    (∃ A : EuclideanAnnulus, A.center = v ∧ A.innerRadius = q * r ∧
      A.outerRadius = Real.sqrt q * r ∧
      aroundDist D A ≤ ENNReal.ofReal (Cminus / (2 * Cplus)) *
        OptimalConstants.Ratios.setDist D (TwoScale.S36Events.eventMiddle z r) (TwoScale.S36Events.eventBoundary z r)) →
    (∃ (P : ℝ → ℂ) (s t : ℝ), OptimalConstants.Ratios.Geodesic D P s t u v ∧
      (∀ τ ∈ Icc s t, P τ ∈ Metric.closedBall z r \ Metric.ball z (a * r)) ∧
      Metric.diam (P '' Icc s t) ≤ r / 100 ∧
      D (u,v) ≤ ENNReal.ofReal ((1-(a : ℝ))⁻¹ * (r : ℝ) ^ (ξ*Q) * Real.exp (ξ*c)) ∧
      TwoScale.S36Events.EndpointLoopAt D r a θ u v u ∧ TwoScale.S36Events.EndpointLoopAt D r a θ u v v) →
    D' (u,v) ≤ ENNReal.ofReal C * D (u,v)

theorem e5Lit_iff_code (D D' : LSCMetric) (ξ Q : ℝ) (z : ℂ) (r : Ioi (0 : ℝ))
    (q : Ioo (0 : ℝ) (1 / 100)) (a : Ioo (1 - (q : ℝ)) 1) (C θ : Ioi (0 : ℝ))
    (Cminus Cplus : ℝ) (c : ℝ) :
    E5Lit D D' ξ Q z r q a C θ Cminus Cplus c ↔ E5Code D D' ξ Q z r q a C θ Cminus Cplus c := by
  have hK := isCompact_shortCarrier z r a
  have hr : (0 : ℝ) < r := r.2
  have hq0 : (0 : ℝ) < q := q.2.1
  have hq1 : (q : ℝ) < 1 := by have := q.2.2; linarith
  have hvalid := TwoScale.Consolidated.loop_annulus_valid hr hq0 hq1
  constructor
  · intro hL u v γ hu hv huv hsh hγ hγ0 hγ1 hγK hγd hN hLu hLv
    have hshA : ∃ A : EuclideanAnnulus, A.center = v ∧ A.innerRadius = q * r ∧
        A.outerRadius = Real.sqrt q * r ∧
        aroundDist D A ≤ ENNReal.ofReal (Cminus / (2 * Cplus)) *
          OptimalConstants.Ratios.setDist D (TwoScale.S36Events.eventMiddle z r) (TwoScale.S36Events.eventBoundary z r) := by
      refine ⟨⟨(v, ((q : ℝ) * r, Real.sqrt q * r)), hvalid⟩, rfl, rfl, rfl, ?_⟩
      rw [← TwoScale.Consolidated.aroundAt_eq D v _ _ hvalid]
      exact hsh
    obtain ⟨P, s, t, hgeo, htr, hdiam⟩ :=
      (exists_geodesic_iff_code D u v hK ((r : ℝ) / 100)).mpr ⟨γ, hγ, hγ0, hγ1, hγK, hγd⟩
    have hfin : D (u, v) ≠ ⊤ := hgeo.2.2.2.2.ne
    exact hL u v hu hv huv hshA ⟨P, s, t, hgeo, htr, hdiam, hN,
      (endpointLoop_iff_mem_loopSet D r (aWin a) θ u v u hfin).mpr hLu,
      (endpointLoop_iff_mem_loopSet D r (aWin a) θ u v v hfin).mpr hLv⟩
  · intro hC u v hu hv huv hshA hgeoEx
    obtain ⟨A, hc, hi, ho, hA⟩ := hshA
    obtain ⟨P, s, t, hgeo, htr, hdiam, hN, hLu, hLv⟩ := hgeoEx
    have hAeq : A = ⟨(v, ((q : ℝ) * r, Real.sqrt q * r)), hvalid⟩ :=
      annulus_eq_mk hc hi ho hvalid
    have hsh : TwoScale.Consolidated.aroundAt D v (q * r) (Real.sqrt q * r) ≤
        ENNReal.ofReal (Cminus / (2 * Cplus)) *
          OptimalConstants.Ratios.setDist D (TwoScale.S36Events.eventMiddle z r) (TwoScale.S36Events.eventBoundary z r) := by
      rw [TwoScale.Consolidated.aroundAt_eq D v _ _ hvalid, ← hAeq]
      exact hA
    obtain ⟨γ, hγ, hγ0, hγ1, hγK, hγd⟩ :=
      (exists_geodesic_iff_code D u v hK ((r : ℝ) / 100)).mp ⟨P, s, t, hgeo, htr, hdiam⟩
    have hfin : D (u, v) ≠ ⊤ := hgeo.2.2.2.2.ne
    exact hC u v γ hu hv huv hsh hγ hγ0 hγ1 hγK hγd hN
      ((endpointLoop_iff_mem_loopSet D r (aWin a) θ u v u hfin).mp hLu)
      ((endpointLoop_iff_mem_loopSet D r (aWin a) θ u v v hfin).mp hLv)

end SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36
