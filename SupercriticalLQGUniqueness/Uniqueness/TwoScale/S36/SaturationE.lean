import SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36.Saturation




 











set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36

theorem toSet_subset_shell (A : EuclideanAnnulus) :
    A.toSet ⊆ {y | A.innerRadius ≤ dist y A.center ∧ dist y A.center < A.outerRadius} := by
  intro y hy
  refine ⟨?_, Metric.mem_ball.mp hy.1⟩
  by_contra hlt
  exact hy.2 (subset_closure (Metric.mem_ball.mpr (lt_of_not_ge hlt)))

theorem shortCarrier_subset_carrier {z : ℂ} {r a : ℝ} (hr : 0 < r) (ha : 1 / 2 ≤ a) :
    shortCarrier z r a ⊆ TwoScale.S36Events.eventCarrier z r := by
  rintro y ⟨hy1, hy2⟩
  rw [Metric.mem_closedBall] at hy1
  rw [Metric.mem_ball, not_lt] at hy2
  refine ⟨Metric.mem_closedBall.mpr (by linarith), ?_⟩
  rw [Metric.mem_ball, not_lt]
  nlinarith

theorem eventOpen_subset_carrier' (z : ℂ) {r : ℝ} (hr : 0 < r) :
    TwoScale.S36Events.eventOpen z r ⊆ TwoScale.S36Events.eventCarrier z r := by
  rw [← eventOpen_union_boundary z hr]
  exact subset_union_left

 
theorem attained_transfer {d₁ e₁ d₂ e₂ : LSCMetric}
    (hBd₁ : BiLipschitz.Barrier.Barrier d₁) (hBe₁ : BiLipschitz.Barrier.Barrier e₁)
    (hBd₂ : BiLipschitz.Barrier.Barrier d₂) (hBe₂ : BiLipschitz.Barrier.Barrier e₂)
    (hLd₁ : d₁.IsLengthSpace) (hLe₁ : e₁.IsLengthSpace)
    (hLd₂ : d₂.IsLengthSpace) (hLe₂ : e₂.IsLengthSpace)
    {Cm Cp : ℝ} (hCm : 0 < Cm) (hCmp : Cm ≤ Cp)
    (hcmp₁ : ∀ x y, ENNReal.ofReal Cm * d₁ (x, y) ≤ e₁ (x, y) ∧
      e₁ (x, y) ≤ ENNReal.ofReal Cp * d₁ (x, y))
    (hcmp₂ : ∀ x y, ENNReal.ofReal Cm * d₂ (x, y) ≤ e₂ (x, y) ∧
      e₂ (x, y) ≤ ENNReal.ofReal Cp * d₂ (x, y))
    (ξ Q : ℝ) (z : ℂ) (r : Ioi (0 : ℝ)) (q : Ioo (0 : ℝ) (1 / 100))
    (a : Ioo (1 - (q : ℝ)) 1) (K : Ioi (1 : ℝ)) (C θ : Ioi (0 : ℝ)) (c : ℝ)
    (hm₁ : OptimalConstants.Ratios.setDist d₁ (TwoScale.S36Events.eventMiddle z r) (TwoScale.S36Events.eventBoundary z r) < ⊤)
    (hm₂ : OptimalConstants.Ratios.setDist d₂ (TwoScale.S36Events.eventMiddle z r) (TwoScale.S36Events.eventBoundary z r) < ⊤)
    {U : Set ℂ} (hYU : TwoScale.S36Events.eventCarrier z r ⊆ U)
    (hId : ∀ x y, intExt d₁ U x y = intExt d₂ U x y)
    (hIe : ∀ x y, intExt e₁ U x y = intExt e₂ U x y)
    (hA : TwoScale.S36Events.Attained d₁ e₁ ξ Q z r q a K C θ Cm Cp c) :
    TwoScale.S36Events.Attained d₂ e₂ ξ Q z r q a K C θ Cm Cp c := by
  have hr : (0 : ℝ) < r := r.2
  have hq0 : (0 : ℝ) < q := q.2.1
  have hq1 : (q : ℝ) < 1 / 100 := q.2.2
  have ha1 : (a : ℝ) < 1 := a.2.2
  have haq : 1 - (q : ℝ) < a := a.2.1
  have hsq : Real.sqrt q < 1 / 10 := sqrt_lt_tenth hq0.le hq1
  have hId' : ∀ x y, intExt d₂ U x y = intExt d₁ U x y := fun x y => (hId x y).symm
  obtain ⟨h1, h2, h3, h4, h5⟩ := (attained_iff d₁ e₁ ξ Q z r q a K C θ Cm Cp c).mp hA
  refine (attained_iff d₂ e₂ ξ Q z r q a K C θ Cm Cp c).mpr ⟨?_, ?_, ?_, ?_, ?_⟩
  · 
    intro P s t hibg δ hδ0 hδq x hx hhit
    obtain ⟨A, hc, hi, ho, hAle⟩ := h1 P s t (ibg_transfer hYU hId' hibg) δ hδ0 hδq x hx hhit
    refine ⟨A, hc, hi, ho, ?_⟩
    have hsqδ : Real.sqrt δ ≤ Real.sqrt q := Real.sqrt_le_sqrt hδq
    have hoR : A.outerRadius ≤ (r : ℝ) / 5 := by rw [ho]; nlinarith
    have hoR' : A.outerRadius < (r : ℝ) / 5 := by rw [ho]; nlinarith
    rw [← around_transfer hId ((small_annulus_subset hr hx hc hoR).trans hYU),
      ← across_transfer hBd₁ hBd₂ hLd₁ hLd₂ hId hoR'
        ((small_across_subset hr hx hc).trans hYU)]
    exact hAle
  · 
    have hout : (outerAnn z r).toSet ⊆ U := by
      refine (toSet_subset_shell _).trans (fun y hy => hYU ?_)
      obtain ⟨hy1, hy2⟩ := hy
      change 3 * (r : ℝ) / 2 ≤ dist y z at hy1
      change dist y z < 2 * (r : ℝ) at hy2
      refine ⟨Metric.mem_closedBall.mpr hy2.le, ?_⟩
      rw [Metric.mem_ball, not_lt]
      linarith
    unfold E2Prop at h2 ⊢
    rw [← around_transfer hId hout, ← middle_transfer hBd₁ hBd₂ hLd₁ hLd₂ hr hYU hId]
    exact h2
  · 
    intro P s t hibg v w hv0 hvw hv hw hseg
    exact h3 P s t (ibg_transfer hYU hId' hibg) v w hv0 hvw hv hw hseg
  · 
    have hsh : (shortAnn z r a).toSet ⊆ U := by
      refine (toSet_subset_shell _).trans (fun y hy => hYU ?_)
      obtain ⟨hy1, hy2⟩ := hy
      change (a : ℝ) * r ≤ dist y z at hy1
      change dist y z < (r : ℝ) at hy2
      refine ⟨Metric.mem_closedBall.mpr (by linarith), ?_⟩
      rw [Metric.mem_ball, not_lt]
      nlinarith
    have hR : (shortAnn z r a).outerRadius < 3 * (r : ℝ) / 2 := by
      change (r : ℝ) < 3 * (r : ℝ) / 2
      linarith
    have hsub : {y : ℂ | (shortAnn z r a).innerRadius < ‖y - (shortAnn z r a).center‖ ∧
        ‖y - (shortAnn z r a).center‖ < 3 * (r : ℝ) / 2} ⊆ U := by
      intro y hy
      apply hYU
      obtain ⟨hy1, hy2⟩ := hy
      change (a : ℝ) * r < ‖y - z‖ at hy1
      change ‖y - z‖ < 3 * (r : ℝ) / 2 at hy2
      rw [← dist_eq_norm] at hy1 hy2
      refine ⟨Metric.mem_closedBall.mpr (by linarith), ?_⟩
      rw [Metric.mem_ball, not_lt]
      nlinarith
    unfold E4Prop at h4 ⊢
    rw [← around_transfer hId hsh, ← across_transfer hBd₁ hBd₂ hLd₁ hLd₂ hId hR hsub]
    exact h4
  · 
    intro u v hu hv huv hshA hgeo
    obtain ⟨A, hAc, hAi, hAo, hAsh⟩ := hshA
    have hvM : v ∈ TwoScale.S36Events.eventMiddle z r :=
      sphere_subset_middle hr (by linarith) (by linarith) hv
    have huM : u ∈ TwoScale.S36Events.eventMiddle z r :=
      sphere_subset_middle hr (by nlinarith) (by nlinarith) hu
    have hAoR : A.outerRadius ≤ (r : ℝ) / 5 := by rw [hAo]; nlinarith
    have hAsub : A.toSet ⊆ U := (small_annulus_subset hr hvM hAc hAoR).trans hYU
    have hmeq := middle_transfer hBd₁ hBd₂ hLd₁ hLd₂ hr hYU hId
    have hareq := around_transfer hId hAsub
    have hq1' : (q : ℝ) < 1 := by linarith
    have hvalid := TwoScale.Consolidated.loop_annulus_valid hr hq0 hq1'
    have hAeq : A = ⟨(v, ((q : ℝ) * r, Real.sqrt q * r)), hvalid⟩ :=
      annulus_eq_mk hAc hAi hAo hvalid
    have hsh₂ : TwoScale.Consolidated.aroundAt d₂ v (q * r) (Real.sqrt q * r) ≤
        ENNReal.ofReal (Cm / (2 * Cp)) *
          OptimalConstants.Ratios.setDist d₂ (TwoScale.S36Events.eventMiddle z r) (TwoScale.S36Events.eventBoundary z r) := by
      rw [TwoScale.Consolidated.aroundAt_eq d₂ v _ _ hvalid, ← hAeq]
      exact hAsh
    have hsh₁ : TwoScale.Consolidated.aroundAt d₁ v (q * r) (Real.sqrt q * r) ≤
        ENNReal.ofReal (Cm / (2 * Cp)) *
          OptimalConstants.Ratios.setDist d₁ (TwoScale.S36Events.eventMiddle z r) (TwoScale.S36Events.eventBoundary z r) := by
      rw [TwoScale.Consolidated.aroundAt_eq d₁ v _ _ hvalid, ← hAeq, hareq, hmeq]
      exact hAsh
    have hT₁ := shield_internal_eq
      (fun γ a b hγ => BiLipschitz.Barrier.continuousOn_of_barrier_of_length _ hBd₁ hLd₁ hγ)
      (fun γ a b hγ => BiLipschitz.Barrier.continuousOn_of_barrier_of_length _ hBe₁ hLe₁ hγ)
      hLd₁ hLe₁ hCm hCmp hcmp₁ hr hq0 hq1 hv huv hm₁ hsh₁
    have hT₂ := shield_internal_eq
      (fun γ a b hγ => BiLipschitz.Barrier.continuousOn_of_barrier_of_length _ hBd₂ hLd₂ hγ)
      (fun γ a b hγ => BiLipschitz.Barrier.continuousOn_of_barrier_of_length _ hBe₂ hLe₂ hγ)
      hLd₂ hLe₂ hCm hCmp hcmp₂ hr hq0 hq1 hv huv hm₂ hsh₂
    have hVU : TwoScale.S36Events.eventOpen z r ⊆ U := (eventOpen_subset_carrier' z hr).trans hYU
    have hduv : d₁ (u, v) = d₂ (u, v) := by
      rw [← hT₁.1, ← hT₂.1, intExt_transfer hVU hId]
    have heuv : e₁ (u, v) = e₂ (u, v) := by
      rw [← hT₁.2, ← hT₂.2, intExt_transfer hVU hIe]
    obtain ⟨P, s, t, hgeoP, htr, hdiam, hN, hLu, hLv⟩ := hgeo
    obtain ⟨hcP, hPs, hPt, hlenP, hfinP⟩ := hgeoP
    have htrU : ∀ τ ∈ Icc s t, P τ ∈ U := fun τ hτ =>
      hYU (shortCarrier_subset_carrier hr (by linarith) (htr τ hτ))
    obtain ⟨hcP₁, hlenP₁⟩ := curve_len_transfer_eq hId' hcP htrU (by rw [hlenP]; exact hfinP.ne)
    have hgeo₁ : OptimalConstants.Ratios.Geodesic d₁ P s t u v :=
      ⟨hcP₁, hPs, hPt, by rw [hlenP₁, hlenP, hduv], by rw [hduv]; exact hfinP⟩
    have hloop : ∀ x ∈ TwoScale.S36Events.eventMiddle z r, TwoScale.S36Events.EndpointLoopAt d₂ r a θ u v x →
        TwoScale.S36Events.EndpointLoopAt d₁ r a θ u v x := by
      intro x hxM hL δ hδ0 hδa
      obtain ⟨B, hBc, hBi, hBo, hBmax⟩ := hL δ hδ0 hδa
      refine ⟨B, hBc, hBi, hBo, ?_⟩
      have h1a : 0 < 1 - (a : ℝ) := by linarith
      have h1a' : 1 - (a : ℝ) < q := by linarith
      have hδq : δ ≤ q := by nlinarith
      have hsqδ : Real.sqrt δ ≤ Real.sqrt q := Real.sqrt_le_sqrt hδq
      have hBoR : B.outerRadius ≤ (r : ℝ) / 5 := by rw [hBo]; nlinarith
      have hBsub := (small_annulus_subset hr hxM hBc hBoR).trans hYU
      have hρ : 0 < δ * r := mul_pos hδ0 hr
      have hcb : Metric.closedBall x (δ * r) ⊆ U :=
        (closedBall_point_subset hr hxM (by nlinarith)).trans hYU
      rw [pointSphere_transfer hBd₁ hBd₂ hLd₁ hLd₂ hId hρ hcb, around_transfer hId hBsub, hduv]
      exact hBmax
    have hE := h5 u v hu hv huv ⟨A, hAc, hAi, hAo, by rw [hareq, hmeq]; exact hAsh⟩
      ⟨P, s, t, hgeo₁, htr, hdiam, by rw [hduv]; exact hN, hloop u huM hLu, hloop v hvM hLv⟩
    rw [← heuv, ← hduv]
    exact hE

end SupercriticalLQGUniqueness.Uniqueness.TwoScale.S36
