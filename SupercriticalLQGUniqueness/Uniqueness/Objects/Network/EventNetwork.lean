import SupercriticalLQGUniqueness.Uniqueness.Objects.CorrectedEvent.EventPredicate




 





set_option autoImplicit false
noncomputable section
open Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Network
open SupercriticalLQGUniqueness.Uniqueness.Objects.CorrectedEvent

 

theorem paid_separator_of_around_lt (D : LSCMetric) (w : ℂ)
    (a b : ℝ) (L : ℝ≥0∞) (h : around D w a b < L) :
    ∃ (P : ℝ → ℂ) (t u : ℝ), D.IsCurve P t u ∧
      P '' Icc t u ⊆ ann w a b ∧
      LQGMetric.Disconnects (P '' Icc t u) (sphere w a) (sphere w b) ∧
      D.len P t u < L := by
  simpa only [around, iInf_lt_iff, exists_prop] using h


 

theorem event_paid_separator {C : Constants} {T : TubeData}
    {hData : DataMatch C T} {F : ℂ → LQGMetric.DistC → Prop}
    {D D' : LQGMetric.DistC → LSCMetric} {g : LQGMetric.DistC}
    (h : correctedEvent C T hData F D D' g)
    {x : ℂ} (hx : x ∈ T.netSites) :
    ∃ (P : ℝ → ℂ) (t u : ℝ), (D g).IsCurve P t u ∧
      P '' Icc t u ⊆ ann x T.netRadius (2*T.netRadius) ∧
      P '' Icc t u ⊆ tubeSet T ∧
      LQGMetric.Disconnects (P '' Icc t u)
        (sphere x T.netRadius) (sphere x (2*T.netRadius)) ∧
      (D g).len P t u <
        ENNReal.ofReal (C.A_internal / (2*T.netSites.card)) *
          normalizer C g C.r 0 := by
  obtain ⟨P, t, u, hP, hAnn, hSep, hLen⟩ :=
    paid_separator_of_around_lt (D g) x T.netRadius (2*T.netRadius) _
      (event_network_test h hx)
  exact ⟨P, t, u, hP, hAnn,
    hAnn.trans (network_annulus_inside_tube hData hx), hSep, hLen⟩


 


theorem separator_union_of_ball_union {ι : Type*} (S : Set ι)
    (c : ι → ℂ) (ρ : ℝ) (K : ι → Set ℂ) (E F : Set ℂ)
    (hBalls : LQGMetric.Disconnects
      (⋃ i ∈ S, ball (c i) ρ) E F)
    (hOuter : ∀ i ∈ S, F ⊆ (ball (c i) (2*ρ))ᶜ)
    (hLocal : ∀ i ∈ S,
      LQGMetric.Disconnects (K i) (sphere (c i) ρ)
        (sphere (c i) (2*ρ)))
    (hρ : 0 ≤ ρ) :
    LQGMetric.Disconnects (⋃ i ∈ S, K i) E F := by
  intro x y γ hx hy
  obtain ⟨p, hpγ, hpB⟩ := hBalls x y γ hx hy
  simp only [mem_iUnion] at hpB
  obtain ⟨i, hi, hpi⟩ := hpB
  have hpClosed : p ∈ closedBall (c i) ρ := mem_closedBall.mpr (mem_ball.mp hpi).le
  have hyOuter : y ∈ (ball (c i) (2*ρ))ᶜ := hOuter i hi hy
  have hPath : IsPathConnected (range γ) := by
    simpa only [Path.extend_range] using
      (isPathConnected_range γ.continuous_extend)
  have hpJoin : JoinedIn (range γ) p y :=
    hPath.joinedIn p hpγ y ⟨1, by simp⟩
  obtain ⟨q, hqPath, hqK⟩ :=
    (LQGMetric.Disconnects.closedBall_compl_ball (by linarith)
      (hLocal i hi)) p y hpJoin.somePath hpClosed hyOuter
  obtain ⟨v, rfl⟩ := hqPath
  exact ⟨_, hpJoin.somePath_mem v,
    mem_iUnion_of_mem i (mem_iUnion_of_mem hi hqK)⟩


 


theorem event_paid_trace_barrier {C : Constants} {T : TubeData}
    {hData : DataMatch C T} {F : ℂ → LQGMetric.DistC → Prop}
    {D D' : LQGMetric.DistC → LSCMetric} {g : LQGMetric.DistC}
    (h : correctedEvent C T hData F D D' g)
    (hU : tubeSet T ⊆ ball 0 (2.5*C.r)) :
    ∃ (P : T.netSites → ℝ → ℂ) (t u : T.netSites → ℝ),
      (∀ x : T.netSites,
        (D g).IsCurve (P x) (t x) (u x) ∧
        (P x) '' Icc (t x) (u x) ⊆
          ann (x : ℂ) T.netRadius (2*T.netRadius) ∧
        (P x) '' Icc (t x) (u x) ⊆ tubeSet T ∧
        LQGMetric.Disconnects ((P x) '' Icc (t x) (u x))
          (sphere (x : ℂ) T.netRadius)
          (sphere (x : ℂ) (2*T.netRadius)) ∧
        (D g).len (P x) (t x) (u x) <
          ENNReal.ofReal (C.A_internal / (2*T.netSites.card)) *
            normalizer C g C.r 0) ∧
      LQGMetric.Disconnects
        (⋃ x : T.netSites, (P x) '' Icc (t x) (u x))
        (closedBall 0 (1.5*C.r)) (ball 0 (2.5*C.r))ᶜ ∧
      (∀ y ∈ closure (tubeSet T),
        ∃ p ∈ ⋃ x : T.netSites, (P x) '' Icc (t x) (u x),
          dist y p < C.A_set*C.r) := by
  classical
  have hPaths : ∀ x : T.netSites,
      ∃ (P : ℝ → ℂ) (t u : ℝ), (D g).IsCurve P t u ∧
        P '' Icc t u ⊆ ann (x : ℂ) T.netRadius (2*T.netRadius) ∧
        P '' Icc t u ⊆ tubeSet T ∧
        LQGMetric.Disconnects (P '' Icc t u)
          (sphere (x : ℂ) T.netRadius)
          (sphere (x : ℂ) (2*T.netRadius)) ∧
        (D g).len P t u <
          ENNReal.ofReal (C.A_internal / (2*T.netSites.card)) *
            normalizer C g C.r 0 := fun x => event_paid_separator h x.property
  choose P t u hCurve hAnn hTube hSep hLen using hPaths
  refine ⟨P, t, u, (fun x => ⟨hCurve x, hAnn x, hTube x, hSep x, hLen x⟩), ?_, ?_⟩
  have hM1 : ∀ x ∈ T.netSites,
      closedBall x (2*T.netRadius) ⊆ tubeSet T := by
    unfold DataMatch at hData
    tauto
  have hM3 : LQGMetric.Disconnects
      (⋃ x ∈ T.netSites, ball x T.netRadius)
      (closedBall 0 (1.5*C.r)) (ball 0 (2.5*C.r))ᶜ := by
    unfold DataMatch at hData
    tauto
  have hBalls : LQGMetric.Disconnects
      (⋃ x : T.netSites, ball (x : ℂ) T.netRadius)
      (closedBall 0 (1.5*C.r)) (ball 0 (2.5*C.r))ᶜ := by
    simpa only [Set.iUnion_subtype] using hM3
  have hOuter : ∀ x : T.netSites,
      (ball 0 (2.5*C.r))ᶜ ⊆ (ball (x : ℂ) (2*T.netRadius))ᶜ := by
    intro x z hz hzBall
    exact hz (hU (hM1 x x.property (mem_closedBall.mpr (mem_ball.mp hzBall).le)))
  simpa only [Set.biUnion_univ] using
    (separator_union_of_ball_union (S := Set.univ)
      (c := fun x : T.netSites => (x : ℂ))
      T.netRadius
      (fun x : T.netSites => (P x) '' Icc (t x) (u x))
      (closedBall 0 (1.5*C.r)) (ball 0 (2.5*C.r))ᶜ
      (by simpa only [Set.biUnion_univ] using hBalls)
      (fun x _ => hOuter x)
      (fun x _ => hSep x)
      (le_of_lt (by
        unfold DataMatch at hData
        tauto)))
  intro y hy
  have hM4 : ∀ y ∈ closure (tubeSet T),
      ∃ x ∈ T.netSites, dist y x ≤ C.A_set*C.r/2 := by
    unfold DataMatch at hData
    tauto
  obtain ⟨x, hx, hnear⟩ := hM4 y hy
  let xs : T.netSites := ⟨x, hx⟩
  have ht : t xs ∈ Icc (t xs) (u xs) := left_mem_Icc.mpr (hCurve xs).1
  have hpAnn : P xs (t xs) ∈ ann x T.netRadius (2*T.netRadius) :=
    hAnn xs ⟨t xs, ht, rfl⟩
  have hr : T.netRadius ≤ C.A_set*C.r/4 := by
    unfold DataMatch at hData
    tauto
  refine ⟨P xs (t xs), mem_iUnion_of_mem xs ⟨t xs, ht, rfl⟩, ?_⟩
  have htri : dist y (P xs (t xs)) ≤ dist y x + dist x (P xs (t xs)) :=
    dist_triangle y x (P xs (t xs))
  have hOuter : dist x (P xs (t xs)) < 2*T.netRadius := by
    change T.netRadius < dist (P xs (t xs)) x ∧
      dist (P xs (t xs)) x < 2*T.netRadius at hpAnn
    rw [dist_comm]
    exact hpAnn.2
  linarith


 

theorem barrier_round_boundaries {K : Set ℂ} {r : ℝ} (hr : 0 < r)
    (h : LQGMetric.Disconnects K
      (closedBall 0 (1.5*r)) (ball 0 (2.5*r))ᶜ) :
    LQGMetric.Disconnects K (sphere 0 r) (sphere 0 (3*r)) ∧
      LQGMetric.Disconnects K (sphere 0 r) (sphere 0 (4*r)) := by
  have hin : sphere (0:ℂ) r ⊆ closedBall 0 (1.5*r) := by
    intro x hx
    rw [mem_sphere] at hx
    exact mem_closedBall.mpr (by rw [hx]; linarith)
  have hout3 : sphere (0:ℂ) (3*r) ⊆ (ball 0 (2.5*r))ᶜ := by
    intro x hx hball
    rw [mem_sphere] at hx
    exact (not_lt_of_ge (by linarith : 2.5*r ≤ 3*r))
      (by simpa only [mem_ball, hx] using hball)
  have hout4 : sphere (0:ℂ) (4*r) ⊆ (ball 0 (2.5*r))ᶜ := by
    intro x hx hball
    rw [mem_sphere] at hx
    exact (not_lt_of_ge (by linarith : 2.5*r ≤ 4*r))
      (by simpa only [mem_ball, hx] using hball)
  exact ⟨h.mono Subset.rfl hin hout3, h.mono Subset.rfl hin hout4⟩


end SupercriticalLQGUniqueness.Uniqueness.Objects.Network
