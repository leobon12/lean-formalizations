import SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions.Sep
import SupercriticalLQGUniqueness.Uniqueness.Objects.Network.EventNetworkLink




 




















set_option autoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions

 

 
theorem chain_bound (Db : LSCMetric) (sites : Finset ℂ) (K : ℂ → Set ℂ) (cost : ℂ → ℝ≥0∞)
    (R : ℂ → ℂ → Prop) (hR : ∀ x y, R x y → y ∈ sites ∧ (K x ∩ K y).Nonempty)
    (hintra : ∀ x ∈ sites, ∀ p ∈ K x, ∀ q ∈ K x, Db (p, q) ≤ cost x)
    {x₀ : ℂ} (hx₀ : x₀ ∈ sites) {p : ℂ} (hp : p ∈ K x₀) {y : ℂ}
    (hy : Relation.ReflTransGen R x₀ y) {q : ℂ} (hq : q ∈ K y) :
    Db (p, q) ≤ ∑ z ∈ sites, cost z := by
  classical
  have key : ∀ y', Relation.ReflTransGen R x₀ y' → ∃ S : Finset ℂ, S ⊆ sites ∧ y' ∈ S ∧
      ∀ z ∈ S, ∀ q ∈ K z, Db (p, q) ≤ ∑ w ∈ S, cost w := by
    intro y' hy'
    induction hy' with
    | refl =>
      refine ⟨{x₀}, by simpa using hx₀, Finset.mem_singleton_self _, fun z hz q hq => ?_⟩
      rw [Finset.mem_singleton.mp hz] at hq
      rw [Finset.sum_singleton]
      exact hintra x₀ hx₀ p hp q hq
    | @tail b c _ hbc ih =>
      obtain ⟨S, hS, hbS, hcost⟩ := ih
      obtain ⟨hc, m, hmb, hmc⟩ := hR b c hbc
      by_cases hcS : c ∈ S
      · exact ⟨S, hS, hcS, hcost⟩
      · refine ⟨insert c S, Finset.insert_subset hc hS, Finset.mem_insert_self c S, ?_⟩
        intro z hz q hq
        rw [Finset.sum_insert hcS]
        rcases Finset.mem_insert.mp hz with rfl | hzS
        · calc Db (p, q) ≤ Db (p, m) + Db (m, q) := Db.isExtMetric.2.2.2 p m q
            _ ≤ ∑ w ∈ S, cost w + cost z := add_le_add (hcost b hbS m hmb) (hintra z hc m hmc q hq)
            _ = cost z + ∑ w ∈ S, cost w := add_comm _ _
        · exact (hcost z hzS q hq).trans le_add_self
  obtain ⟨S, hS, hyS, hcost⟩ := key y hy
  exact (hcost y hyS q hq).trans (Finset.sum_le_sum_of_subset hS)

 
theorem chain_joined (sites : Finset ℂ) (K : ℂ → Set ℂ) (R : ℂ → ℂ → Prop)
    (hR : ∀ x y, R x y → y ∈ sites ∧ (K x ∩ K y).Nonempty)
    (hpc : ∀ x ∈ sites, IsPathConnected (K x))
    {x₀ : ℂ} (hx₀ : x₀ ∈ sites) {p : ℂ} (hp : p ∈ K x₀) {y : ℂ}
    (hy : Relation.ReflTransGen R x₀ y) : ∀ q ∈ K y, JoinedIn (⋃ x ∈ sites, K x) p q := by
  induction hy with
  | refl =>
    intro q hq
    exact ((hpc x₀ hx₀).joinedIn p hp q hq).mono (subset_biUnion_of_mem (u := K) hx₀)
  | @tail b c _ hbc ih =>
    intro q hq
    obtain ⟨hc, m, hmb, hmc⟩ := hR b c hbc
    exact (ih m hmb).trans (((hpc c hc).joinedIn m hmc q hq).mono
      (subset_biUnion_of_mem (u := K) hc))

 

 
structure NetData (C : Objects.CorrectedEvent.Constants) (T : Objects.CorrectedEvent.TubeData) (D : LSCMetric) (Ne : ℝ≥0∞)
    (π : ℂ → ℝ → ℂ) (ts us : ℂ → ℝ) : Prop where
  curve : ∀ x ∈ T.netSites, D.IsCurve (π x) (ts x) (us x)
  ann : ∀ x ∈ T.netSites, π x '' Icc (ts x) (us x) ⊆ Objects.CorrectedEvent.ann x T.netRadius (2 * T.netRadius)
  tube : ∀ x ∈ T.netSites, π x '' Icc (ts x) (us x) ⊆ Objects.CorrectedEvent.tubeSet T
  len : ∀ x ∈ T.netSites,
    D.len (π x) (ts x) (us x) < ENNReal.ofReal (C.A_internal / (2 * T.netSites.card)) * Ne
  barrier : LQGMetric.Disconnects (⋃ x ∈ T.netSites, π x '' Icc (ts x) (us x))
    (closedBall 0 (1.5 * C.r)) (ball 0 (2.5 * C.r))ᶜ
  dense : ∀ y ∈ closure (Objects.CorrectedEvent.tubeSet T), ∃ x ∈ T.netSites, ∃ p ∈ π x '' Icc (ts x) (us x),
    dist y p < C.A_set * C.r
  contact : ∀ x y, x ∈ T.netSites → y ∈ T.netSites → T.netRadius < dist x y →
    dist x y < 2 * T.netRadius → (π x '' Icc (ts x) (us x) ∩ π y '' Icc (ts y) (us y)).Nonempty
  conn : ∀ x ∈ T.netSites, ∀ y ∈ T.netSites,
    Relation.ReflTransGen (fun u v : ℂ => u ∈ T.netSites ∧ v ∈ T.netSites ∧
      T.netRadius < dist u v ∧ dist u v < 2 * T.netRadius) x y
  nonempty : T.netSites.Nonempty

 
theorem dataMatch_net {C : Objects.CorrectedEvent.Constants} {T : Objects.CorrectedEvent.TubeData} (hData : Objects.CorrectedEvent.DataMatch C T) :
    0 < T.netRadius ∧ T.netRadius ≤ C.A_set * C.r / 4 ∧ T.netSites.Nonempty ∧
    (∀ x ∈ T.netSites, closedBall x (2 * T.netRadius) ⊆ Objects.CorrectedEvent.tubeSet T) ∧
    (∀ x ∈ T.netSites, ∀ y ∈ T.netSites,
      Relation.ReflTransGen (fun u v : ℂ => u ∈ T.netSites ∧ v ∈ T.netSites ∧
        T.netRadius < dist u v ∧ dist u v < 2 * T.netRadius) x y) ∧
    LQGMetric.Disconnects (⋃ x ∈ T.netSites, ball x T.netRadius)
      (closedBall 0 (1.5 * C.r)) (ball 0 (2.5 * C.r))ᶜ ∧
    (∀ y ∈ closure (Objects.CorrectedEvent.tubeSet T), ∃ x ∈ T.netSites, dist y x ≤ C.A_set * C.r / 2) := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, h1, h2, h3, h4, h5, h6, h7, _⟩ := hData
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

 
theorem event_network {C : Objects.CorrectedEvent.Constants} {T : Objects.CorrectedEvent.TubeData} {hData : Objects.CorrectedEvent.DataMatch C T}
    {F : ℂ → LQGMetric.DistC → Prop} {D D' : LQGMetric.DistC → LSCMetric} {g : LQGMetric.DistC}
    (hev : Objects.CorrectedEvent.correctedEvent C T hData F D D' g)
    (hU : Objects.CorrectedEvent.tubeSet T ⊆ ball 0 (2.5 * C.r)) :
    ∃ (π : ℂ → ℝ → ℂ) (ts us : ℂ → ℝ),
      NetData C T (D g) (Objects.CorrectedEvent.normalizer C g C.r 0) π ts us := by
  classical
  obtain ⟨hρ, hρle, hne, hM1, hM2, hM3, hM4⟩ := dataMatch_net hData
  have hsel : ∀ x : ℂ, ∃ (P : ℝ → ℂ) (t u : ℝ), x ∈ T.netSites →
      (D g).IsCurve P t u ∧ P '' Icc t u ⊆ Objects.CorrectedEvent.ann x T.netRadius (2 * T.netRadius) ∧
        P '' Icc t u ⊆ Objects.CorrectedEvent.tubeSet T ∧
        LQGMetric.Disconnects (P '' Icc t u) (sphere x T.netRadius) (sphere x (2 * T.netRadius)) ∧
        (D g).len P t u < ENNReal.ofReal (C.A_internal / (2 * T.netSites.card)) *
          Objects.CorrectedEvent.normalizer C g C.r 0 := by
    intro x
    by_cases hx : x ∈ T.netSites
    · obtain ⟨P, t, u, h1, h2, h3, h4, h5⟩ := Objects.Network.event_paid_separator hev hx
      exact ⟨P, t, u, fun _ => ⟨h1, h2, h3, h4, h5⟩⟩
    · exact ⟨fun _ => 0, 0, 0, fun h => absurd h hx⟩
  choose π ts us hπ using hsel
  have hcont : ∀ y ∈ T.netSites, ContinuousOn (π y) (Icc (ts y) (us y)) := by
    intro y hy
    refine (hπ y hy).1.continuousOn_of_mapsTo (isCompact_closedBall y (2 * T.netRadius)) ?_
    intro t ht
    exact mem_closedBall.mpr ((hπ y hy).2.1 ⟨t, ht, rfl⟩).2.le
  refine ⟨π, ts, us, ⟨fun x hx => (hπ x hx).1, fun x hx => (hπ x hx).2.1,
    fun x hx => (hπ x hx).2.2.1, fun x hx => (hπ x hx).2.2.2.2, ?_, ?_, ?_, hM2, hne⟩⟩
  · 
    have hOuter : ∀ i ∈ (T.netSites : Set ℂ),
        (ball (0 : ℂ) (2.5 * C.r))ᶜ ⊆ (ball (id i) (2 * T.netRadius))ᶜ := by
      intro i hi z hz hzB
      exact hz (hU (hM1 i hi (mem_closedBall.mpr (mem_ball.mp hzB).le)))
    have := Objects.Network.separator_union_of_ball_union (S := (T.netSites : Set ℂ)) (c := id) T.netRadius
      (fun x => π x '' Icc (ts x) (us x)) (closedBall 0 (1.5 * C.r)) (ball 0 (2.5 * C.r))ᶜ
      (by simpa only [id, Finset.mem_coe] using hM3) hOuter
      (fun i hi => (hπ i hi).2.2.2.1) hρ.le
    simpa only [Finset.mem_coe] using this
  · 
    intro y hy
    obtain ⟨x, hx, hnear⟩ := hM4 y hy
    have hcurve := (hπ x hx).1
    have ht : ts x ∈ Icc (ts x) (us x) := left_mem_Icc.mpr hcurve.1
    have hpAnn := (hπ x hx).2.1 ⟨ts x, ht, rfl⟩
    refine ⟨x, hx, π x (ts x), ⟨ts x, ht, rfl⟩, ?_⟩
    have htri := dist_triangle y x (π x (ts x))
    have hO : dist x (π x (ts x)) < 2 * T.netRadius := by
      rw [dist_comm]; exact hpAnn.2
    linarith
  · 
    intro x y hx hy hxy1 hxy2
    exact Objects.Network.paid_separators_meet (D g) hρ hxy1.le hxy2.le (hπ y hy).1 (hcont y hy)
      (hπ y hy).2.1 (hπ x hx).2.2.2.1 (hπ y hy).2.2.2.1

namespace NetData

variable {C : Objects.CorrectedEvent.Constants} {T : Objects.CorrectedEvent.TubeData} {D : LSCMetric} {Ne : ℝ≥0∞}
  {π : ℂ → ℝ → ℂ} {ts us : ℂ → ℝ}

 
def Γ (π : ℂ → ℝ → ℂ) (ts us : ℂ → ℝ) (T : Objects.CorrectedEvent.TubeData) : Set ℂ :=
  ⋃ x ∈ T.netSites, π x '' Icc (ts x) (us x)

theorem mem_Γ {x : ℂ} (hx : x ∈ T.netSites) {p : ℂ} (hp : p ∈ π x '' Icc (ts x) (us x)) :
    p ∈ Γ π ts us T := mem_biUnion hx hp

 
theorem joined (net : NetData C T D Ne π ts us) {p q : ℂ} (hp : p ∈ Γ π ts us T)
    (hq : q ∈ Γ π ts us T) : JoinedIn (Γ π ts us T) p q := by
  obtain ⟨x, hx, hpx⟩ := mem_iUnion₂.mp hp
  obtain ⟨y, hy, hqy⟩ := mem_iUnion₂.mp hq
  refine chain_joined T.netSites (fun x => π x '' Icc (ts x) (us x)) _ ?_ ?_ hx hpx
    (net.conn x hx y hy) q hqy
  · intro a b hab
    exact ⟨hab.2.1, net.contact a b hab.1 hab.2.1 hab.2.2.1 hab.2.2.2⟩
  · intro a ha
    have hc : ContinuousOn (π a) (Icc (ts a) (us a)) :=
      (net.curve a ha).continuousOn_of_mapsTo (isCompact_closedBall a (2 * T.netRadius))
        (fun t ht => mem_closedBall.mpr ((net.ann a ha ⟨t, ht, rfl⟩).2.le))
    exact ((convex_Icc (ts a) (us a)).isPathConnected
      (nonempty_Icc.mpr (net.curve a ha).1)).image' hc

end NetData

end SupercriticalLQGUniqueness.Uniqueness.Objects.Excursions
