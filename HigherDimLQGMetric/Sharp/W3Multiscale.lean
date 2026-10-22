import HigherDimLQGMetric.Sharp.W3Geom
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-!
# Multiscale chaining for internal diameters

The finite-graph lemma controls the number of level-zero links by the
cardinality of the initial grid. The metric paths at finer scales form a
summable chain.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set Metric
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

/-- Transfer a point along a finite graph walk when one edge costs at most
`2B`. The point stays in the set associated to its current vertex. -/
private theorem w3_walk_transfer {V X : Type*} (G : SimpleGraph V)
    (M : V → Set X) (δ : X → X → ℝ≥0∞) (B : ℝ≥0∞)
    (hself : ∀ (v : V) (x : X), x ∈ M v → δ x x = 0)
    (htri : ∀ x y z, δ x z ≤ δ x y + δ y z)
    (hedge : ∀ {u v : V}, G.Adj u v → ∀ x ∈ M u,
      ∃ y ∈ M v, δ x y ≤ 2 * B)
    {u v : V} (p : G.Walk u v) (x : X) (hx : x ∈ M u) :
    ∃ y ∈ M v, δ x y ≤ (2 * (p.length : ℝ≥0∞)) * B := by
  induction p generalizing x with
  | nil =>
      refine ⟨x, hx, ?_⟩
      simp only [SimpleGraph.Walk.length_nil, Nat.cast_zero, mul_zero, zero_mul,
        hself _ _ hx]
      exact le_rfl
  | @cons u v w hadj p ih =>
      obtain ⟨y, hy, hxy⟩ := hedge hadj x hx
      obtain ⟨z, hz, hyz⟩ := ih y hy
      refine ⟨z, hz, ?_⟩
      calc
        δ x z ≤ δ x y + δ y z := htri x y z
        _ ≤ 2 * B + (2 * (p.length : ℝ≥0∞)) * B := add_le_add hxy hyz
        _ = (2 * ((SimpleGraph.Walk.cons hadj p).length : ℝ≥0∞)) * B := by
          simp only [SimpleGraph.Walk.length_cons]
          push_cast
          ring

/-- A connected component of a finite graph has diameter bounded by the
number of vertices when edges transfer points at cost `2B`. -/
private theorem w3_finite_graph_bound {V X : Type*} [Fintype V]
    (G : SimpleGraph V) (M : V → Set X) (δ : X → X → ℝ≥0∞) (B : ℝ≥0∞)
    (hself : ∀ (v : V) (x : X), x ∈ M v → δ x x = 0)
    (htri : ∀ x y z, δ x z ≤ δ x y + δ y z)
    (hedge : ∀ {u v : V}, G.Adj u v → ∀ x ∈ M u,
      ∃ y ∈ M v, δ x y ≤ 2 * B)
    (hwithin : ∀ (v : V) (x : X), x ∈ M v → ∀ (y : X), y ∈ M v → δ x y ≤ B)
    {u v : V} (hreach : G.Reachable u v)
    {x y : X} (hx : x ∈ M u) (hy : y ∈ M v) :
    δ x y ≤ (2 * (Fintype.card V : ℝ≥0∞) + 1) * B := by
  classical
  obtain ⟨walk⟩ := hreach
  let p := walk.toPath
  obtain ⟨z, hz, hxz⟩ := w3_walk_transfer G M δ B hself htri hedge p.1 x hx
  have hzy := hwithin v z hz y hy
  have hlen : p.1.length < Fintype.card V := p.2.length_lt
  calc
    δ x y ≤ δ x z + δ z y := htri x z y
    _ ≤ (2 * (p.1.length : ℝ≥0∞)) * B + B := add_le_add hxz hzy
    _ = (2 * (p.1.length : ℝ≥0∞) + 1) * B := by ring
    _ ≤ (2 * (Fintype.card V : ℝ≥0∞) + 1) * B := by
      gcongr

private def w3GridGraph (G : Finset (Rd d)) (ρ : ℝ) :
    SimpleGraph {w : Rd d // w ∈ G} where
  Adj v w := v ≠ w ∧ dist v.1 w.1 < ρ / 16
  symm := by
    constructor
    intro v w h
    exact ⟨h.1.symm, by simpa only [dist_comm] using h.2⟩
  loopless := by
    constructor
    intro v h
    exact h.1 rfl

set_option maxHeartbeats 800000

/-- The level-zero grid points selected for two points of a connected set lie
in the same component of the nearby-point graph. -/
private theorem w3_grid_reachable {K : Set (Rd d)} (hKc : IsConnected K)
    {G : Finset (Rd d)} {ρ : ℝ} (hρ : 0 < ρ)
    (hcover : ∀ z ∈ K, ∃ w ∈ G, ‖z - w‖ ≤ ρ / 64)
    {x y : Rd d} (hx : x ∈ K) (hy : y ∈ K) :
    ∃ C : Rd d → {w : Rd d // w ∈ G},
      (∀ z ∈ K, ‖z - (C z).1‖ ≤ ρ / 64) ∧
      (w3GridGraph G ρ).Reachable (C x) (C y) := by
  classical
  obtain ⟨w₀, hw₀, _⟩ := hcover x hx
  let fallback : {w : Rd d // w ∈ G} := ⟨w₀, hw₀⟩
  let C : Rd d → {w : Rd d // w ∈ G} := fun z =>
    if hz : z ∈ K then ⟨Classical.choose (hcover z hz),
      (Classical.choose_spec (hcover z hz)).1⟩ else fallback
  have hnear : ∀ z ∈ K, ‖z - (C z).1‖ ≤ ρ / 64 := by
    intro z hz
    change ‖z - (if hz' : z ∈ K then
      ⟨Classical.choose (hcover z hz'), (Classical.choose_spec (hcover z hz')).1⟩
      else fallback : {w : Rd d // w ∈ G}).1‖ ≤ ρ / 64
    rw [dite_eq_left hz]
    exact (Classical.choose_spec (hcover z hz)).2
  have hmap : ∀ u v : Rd d,
      (u ∈ K ∧ v ∈ K ∧ dist u v < ρ / 64) →
        (w3GridGraph G ρ).Reachable (C u) (C v) := by
    intro u v ⟨hu, hv, huv⟩
    have hu' := hnear u hu
    have hv' := hnear v hv
    have hd₁ : dist (C u).1 u ≤ ρ / 64 := by
      rw [dist_eq_norm, norm_sub_rev]
      exact hu'
    have hd₂ : dist v (C v).1 ≤ ρ / 64 := by
      rw [dist_eq_norm]
      exact hv'
    have hdist : dist (C u).1 (C v).1 < ρ / 16 := by
      have ht₁ := dist_triangle (C u).1 u (C v).1
      have ht₂ := dist_triangle u v (C v).1
      linarith only [ht₁, ht₂, hd₁, hd₂, huv, hρ]
    by_cases heq : C u = C v
    · rw [heq]
    · exact SimpleGraph.Adj.reachable ⟨heq, hdist⟩
  have hchain := connected_epsilon_chain hKc (show 0 < ρ / 64 by positivity) hx hy
  have hreach : (w3GridGraph G ρ).Reachable (C x) (C y) := by
    induction hchain with
    | refl => exact SimpleGraph.Reachable.refl _
    | tail _ hedge ih => exact (ih hedge.1).trans (hmap _ _ hedge)
  exact ⟨C, hnear, hreach⟩

/-- A selected near-optimal crossing path at one grid point. -/
private structure W3AcrossPath (D : ContMetric d) (w : Rd d) (r b : ℝ) where
  P : ℝ → Rd d
  cont : ContinuousOn P (Icc 0 1)
  start : P 0 ∈ Metric.sphere w (r / 8)
  finish : P 1 ∈ Metric.sphere w r
  inside : MapsTo P (Icc 0 1) (ann w (r / 16) (2 * r))
  cost : D.len P 0 1 ≤ ENNReal.ofReal b

private theorem w3_across_path_exists (D : ContMetric d) {w : Rd d}
    {r β η : ℝ} (hβ : 0 ≤ β) (hη : 0 < η)
    (hcross : setDistIn D (ann w (r / 16) (2 * r))
      (Metric.sphere w (r / 8)) (Metric.sphere w r) ≤ ENNReal.ofReal β) :
    Nonempty (W3AcrossPath D w r (β + η)) := by
  obtain ⟨P, hPc, hP0, hP1, hPin, hlen⟩ := w3_short_across_path D hη hcross
  refine ⟨⟨P, hPc, hP0, hP1, hPin, ?_⟩⟩
  rwa [ENNReal.ofReal_add hβ hη.le]

private theorem W3AcrossPath.internal_le (D : ContMetric d)
    {U : Set (Rd d)} {w : Rd d} {r b : ℝ}
    (p : W3AcrossPath D w r b)
    (hU : ann w (r / 16) (2 * r) ⊆ U)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    D.internal U (p.P s) (p.P t) ≤ ENNReal.ofReal b :=
  (w3_internal_le_path_len D p.cont (fun _ hu => hU (p.inside hu)) hs ht).trans p.cost

private theorem w3_ann_subset_of_ball {U : Set (Rd d)} {w : Rd d} {r : ℝ}
    (hball : Metric.closedBall w (2 * r) ⊆ U) :
    ann w (r / 16) (2 * r) ⊆ U := by
  intro x hx
  apply hball
  rw [Metric.mem_closedBall, dist_eq_norm]
  exact hx.2.le

/-- Level-zero cost between arbitrary points on two selected across paths. -/
private theorem w3_level0_bound (D : ContMetric d) {U : Set (Rd d)}
    {G : Finset (Rd d)} {r β η : ℝ} (hr : 0 < r) (hβ : 0 ≤ β) (hη : 0 < η)
    (hball : ∀ w ∈ G, Metric.closedBall w (2 * r) ⊆ U)
    (haround : ∀ w ∈ G,
      aroundDist D w (3 * r / 16) (3 * r / 8) ≤ ENNReal.ofReal β)
    (paths : ∀ v : {w : Rd d // w ∈ G}, W3AcrossPath D v.1 r (β + η))
    {v w : {w : Rd d // w ∈ G}}
    (hreach : (w3GridGraph G r).Reachable v w)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (ht : t ∈ Icc (0 : ℝ) 1) :
    D.internal U ((paths v).P s) ((paths w).P t) ≤
      (2 * (G.card : ℝ≥0∞) + 1) * ENNReal.ofReal (β + η) := by
  classical
  let M : {w : Rd d // w ∈ G} → Set (Rd d) := fun u => (paths u).P '' Icc 0 1
  have hsub : ∀ u : {w : Rd d // w ∈ G},
      ann u.1 (r / 16) (2 * r) ⊆ U := fun u => w3_ann_subset_of_ball (hball u.1 u.2)
  have hM : ∀ u : {w : Rd d // w ∈ G}, M u ⊆ U := by
    rintro u x ⟨a, ha, rfl⟩
    exact hsub u ((paths u).inside ha)
  have hself : ∀ (u : {w : Rd d // w ∈ G}) (x : Rd d),
      x ∈ M u → D.internal U x x = 0 := by
    intro u x hx
    exact D.internal_self (hM u hx)
  have hwithin : ∀ (u : {w : Rd d // w ∈ G}) (x : Rd d),
      x ∈ M u → ∀ (y : Rd d), y ∈ M u →
        D.internal U x y ≤ ENNReal.ofReal (β + η) := by
    rintro u x ⟨a, ha, rfl⟩ y ⟨b, hb, rfl⟩
    exact (paths u).internal_le D (hsub u) ha hb
  have hedge : ∀ {u v : {w : Rd d // w ∈ G}},
      (w3GridGraph G r).Adj u v → ∀ x ∈ M u,
        ∃ y ∈ M v, D.internal U x y ≤ 2 * ENNReal.ofReal (β + η) := by
    intro u v huv x hx
    have hdist : ‖u.1 - v.1‖ ≤ r / 16 := by
      exact (by simpa only [dist_eq_norm] using huv.2.le)
    obtain ⟨a, ha, b, hb, hab⟩ := w3_link_nearby_across D hr hη
      (by linarith only [hr]) le_rfl hdist (hball u.1 u.2)
      (haround u.1 u.2) (paths u).cont (paths v).cont
      (paths u).start (paths u).finish (paths v).start (paths v).finish
    let y := (paths v).P b
    refine ⟨y, ⟨b, hb, rfl⟩, ?_⟩
    have hxlink : D.internal U x ((paths u).P a) ≤ ENNReal.ofReal (β + η) :=
      hwithin u x hx _ ⟨a, ha, rfl⟩
    have hlink : D.internal U ((paths u).P a) y ≤ ENNReal.ofReal (β + η) := by
      simpa only [ENNReal.ofReal_add hβ hη.le] using hab
    calc
      D.internal U x y ≤ D.internal U x ((paths u).P a) +
          D.internal U ((paths u).P a) y := D.internal_triangle U _ _ _
      _ ≤ ENNReal.ofReal (β + η) + ENNReal.ofReal (β + η) :=
          add_le_add hxlink hlink
      _ = 2 * ENNReal.ofReal (β + η) := by ring
  have hgraph := w3_finite_graph_bound (w3GridGraph G r) M
    (fun x y => D.internal U x y) (ENNReal.ofReal (β + η))
    hself (D.internal_triangle U) hedge hwithin hreach
    (x := (paths v).P s) (y := (paths w).P t)
    ⟨s, hs, rfl⟩ ⟨t, ht, rfl⟩
  simpa only [Fintype.card_coe] using hgraph

/-- A summable chain reaches its limit at cost at most twice the sum of the
successive level budgets. -/
private theorem w3_chain_limit {X : Type*} [TopologicalSpace X]
    (δ : X → X → ℝ≥0∞)
    (htri : ∀ x y z, δ x z ≤ δ x y + δ y z)
    (a : ℕ → X) (z : X)
    (hself : δ (a 0) (a 0) = 0)
    (hcont : ContinuousAt (fun p : X × X => δ p.1 p.2) (a 0, z))
    (ha : Filter.Tendsto a Filter.atTop (nhds z))
    (B : ℕ → ℝ≥0∞) (hBfin : (∑' n, B n) ≠ ⊤)
    (hB0 : Filter.Tendsto B Filter.atTop (nhds 0))
    (hstep : ∀ n, δ (a n) (a (n + 1)) ≤ B n + B (n + 1)) :
    δ (a 0) z ≤ 2 * ∑' n, B n := by
  have hchain : ∀ n, δ (a 0) (a n) ≤
      2 * (∑ i ∈ Finset.range n, B i) + B n := by
    intro n
    induction n with
    | zero =>
        simp only [Finset.range_zero, Finset.sum_empty, mul_zero, zero_add]
        rw [hself]
        exact bot_le
    | succ n ih =>
        calc
          δ (a 0) (a (n + 1)) ≤ δ (a 0) (a n) + δ (a n) (a (n + 1)) :=
            htri _ _ _
          _ ≤ (2 * (∑ i ∈ Finset.range n, B i) + B n) +
              (B n + B (n + 1)) := add_le_add ih (hstep n)
          _ = 2 * (∑ i ∈ Finset.range (n + 1), B i) + B (n + 1) := by
            rw [Finset.sum_range_succ]
            ring
  have hbound : ∀ n, δ (a 0) (a n) ≤ 2 * (∑' i, B i) + B n := by
    intro n
    have hsumle : (∑ i ∈ Finset.range n, B i) ≤ ∑' i, B i :=
      ENNReal.sum_le_tsum (Finset.range n)
    have hmul : (2 : ℝ≥0∞) * (∑ i ∈ Finset.range n, B i) ≤
        2 * (∑' i, B i) := mul_le_mul_of_nonneg_left hsumle (by norm_num)
    exact (hchain n).trans (add_le_add hmul le_rfl)
  have hlimδ : Filter.Tendsto (fun n => δ (a 0) (a n)) Filter.atTop
      (nhds (δ (a 0) z)) := by
    exact hcont.tendsto.comp (tendsto_const_nhds.prodMk_nhds ha)
  have hlimB : Filter.Tendsto (fun n => 2 * (∑' i, B i) + B n)
      Filter.atTop (nhds (2 * ∑' i, B i)) := by
    have h2 : 2 * (∑' i, B i) ≠ ⊤ := by
      exact ENNReal.mul_ne_top (by norm_num) hBfin
    simpa only [add_zero] using (tendsto_const_nhds.add hB0)
  exact le_of_tendsto_of_tendsto hlimδ hlimB (Filter.Eventually.of_forall hbound)

/-- Descending through the selected grids reaches a point of `K` at twice the
summed budget. The first endpoint lies on the level-zero path. -/
private theorem w3_descend (D : ContMetric d) (hDl : D.IsLength)
    {U : Set (Rd d)} (hU : IsOpen U)
    (ρ : ℕ → ℝ) (hρ0 : 0 < ρ 0) (hρ : ∀ n, ρ n = ρ 0 / 2 ^ n)
    (G : ℕ → Finset (Rd d))
    (hGU : ∀ n, ∀ w ∈ G n, Metric.closedBall w (2 * ρ n) ⊆ U)
    (β η : ℕ → ℝ) (hβ0 : ∀ n, 0 ≤ β n) (hη : ∀ n, 0 < η n)
    (haround : ∀ n, ∀ w ∈ G n,
      aroundDist D w (3 * ρ n / 16) (3 * ρ n / 8) ≤ ENNReal.ofReal (β n))
    (paths : ∀ n, ∀ w : {w : Rd d // w ∈ G n},
      W3AcrossPath D w.1 (ρ n) (β n + η n))
    {z : Rd d} (hzU : z ∈ U)
    (w : ∀ n, {w : Rd d // w ∈ G n})
    (hnear : ∀ n, ‖z - (w n).1‖ ≤ ρ n / 64)
    (hBfin : (∑' n, ENNReal.ofReal (β n + η n)) ≠ ⊤)
    (hB0 : Filter.Tendsto (fun n => ENNReal.ofReal (β n + η n))
      Filter.atTop (nhds 0)) :
    ∃ s ∈ Icc (0 : ℝ) 1,
      D.internal U ((paths 0 (w 0)).P s) z ≤
        2 * ∑' n, ENNReal.ofReal (β n + η n) := by
  classical
  let B : ℕ → ℝ≥0∞ := fun n => ENNReal.ofReal (β n + η n)
  let p (n : ℕ) := paths n (w n)
  have hρpos : ∀ n, 0 < ρ n := by
    intro n
    rw [hρ n]
    positivity
  have hρsucc : ∀ n, ρ (n + 1) = ρ n / 2 := by
    intro n
    rw [hρ (n + 1), hρ n, pow_succ]
    ring
  have hdist : ∀ n, ‖(w n).1 - (w (n + 1)).1‖ ≤ ρ n / 16 := by
    intro n
    have h₁ := hnear n
    have h₂ := hnear (n + 1)
    rw [hρsucc n] at h₂
    have htri := norm_add_le ((w n).1 - z) (z - (w (n + 1)).1)
    have he : ((w n).1 - z) + (z - (w (n + 1)).1) =
        (w n).1 - (w (n + 1)).1 := by abel
    rw [he, norm_sub_rev (w n).1 z] at htri
    nlinarith only [h₁, h₂, htri, hρpos n]
  have hlink : ∀ n, ∃ s ∈ Icc (0 : ℝ) 1, ∃ t ∈ Icc (0 : ℝ) 1,
      D.internal U ((p n).P s) ((p (n + 1)).P t) ≤ B n := by
    intro n
    have h := w3_link_nearby_across D (hρpos n) (hη n)
      (show ρ n / 2 ≤ ρ (n + 1) by rw [hρsucc n])
      (show ρ (n + 1) ≤ ρ n by rw [hρsucc n]; linarith only [hρpos n])
      (hdist n) (hGU n (w n).1 (w n).2)
      (haround n (w n).1 (w n).2)
      (p n).cont (p (n + 1)).cont
      (p n).start (p n).finish (p (n + 1)).start (p (n + 1)).finish
    simpa only [B, ENNReal.ofReal_add (hβ0 n) (hη n).le] using h
  choose s hs t ht hst using hlink
  let a : ℕ → Rd d := fun n => (p n).P (s n)
  have haU : ∀ n, a n ∈ U := by
    intro n
    exact w3_ann_subset_of_ball (hGU n (w n).1 (w n).2) ((p n).inside (hs n))
  have hstep : ∀ n, D.internal U (a n) (a (n + 1)) ≤ B n + B (n + 1) := by
    intro n
    have htail : D.internal U ((p (n + 1)).P (t n)) (a (n + 1)) ≤ B (n + 1) :=
      (p (n + 1)).internal_le D
        (w3_ann_subset_of_ball (hGU (n + 1) (w (n + 1)).1 (w (n + 1)).2))
        (ht n) (hs (n + 1))
    exact (D.internal_triangle U (a n) ((p (n + 1)).P (t n)) (a (n + 1))).trans
      (add_le_add (hst n) htail)
  have hrho_lim : Filter.Tendsto ρ Filter.atTop (nhds 0) := by
    have hbase : Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n)
        Filter.atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have he : ρ = fun n => ρ 0 * (1 / 2 : ℝ) ^ n := by
      funext n
      rw [hρ n]
      simp only [div_eq_mul_inv, one_mul, inv_pow]
    rw [he]
    simpa using (hbase.const_mul (ρ 0))
  have hanear : ∀ n, dist (a n) z ≤ 3 * ρ n := by
    intro n
    have hp := (p n).inside (hs n)
    have hpdist : dist (a n) (w n).1 < 2 * ρ n := by
      simpa only [a, dist_eq_norm] using hp.2
    have hw : dist (w n).1 z ≤ ρ n / 64 := by
      rw [dist_eq_norm, norm_sub_rev]
      exact hnear n
    have htri := dist_triangle (a n) (w n).1 z
    linarith only [hpdist, hw, htri, hρpos n]
  have halim : Filter.Tendsto a Filter.atTop (nhds z) := by
    apply tendsto_iff_dist_tendsto_zero.2
    exact squeeze_zero (fun n => dist_nonneg) hanear (by
      simpa using hrho_lim.const_mul (3 : ℝ))
  have hcont : ContinuousAt (fun q : Rd d × Rd d => D.internal U q.1 q.2) (a 0, z) :=
    ((D.continuousOn_internal hDl hU) (a 0, z) ⟨haU 0, hzU⟩).continuousAt
      ((hU.prod hU).mem_nhds ⟨haU 0, hzU⟩)
  refine ⟨s 0, hs 0, ?_⟩
  exact w3_chain_limit (fun x y => D.internal U x y) (D.internal_triangle U)
    a z (D.internal_self (haU 0)) hcont halim B hBfin hB0 hstep

/-- Finite ENNReal sum and vanishing terms for a nonnegative summable real
budget. -/
private theorem w3_budget_finite {b : ℕ → ℝ} (hb : Summable b)
    (hbn : ∀ n, 0 ≤ b n) :
    (∑' n, ENNReal.ofReal (b n)) = ENNReal.ofReal (∑' n, b n) ∧
      (∑' n, ENNReal.ofReal (b n)) ≠ ⊤ ∧
      Filter.Tendsto (fun n => ENNReal.ofReal (b n)) Filter.atTop (nhds 0) := by
  have he := ENNReal.ofReal_tsum_of_nonneg hbn hb
  refine ⟨he.symm, ?_, ?_⟩
  · rw [← he]
    exact ENNReal.ofReal_ne_top
  · have hlim : Filter.Tendsto b Filter.atTop (nhds 0) := hb.tendsto_atTop_zero
    simpa only [ENNReal.ofReal_zero, Function.comp_def] using
      (ENNReal.continuous_ofReal.tendsto 0).comp hlim

/-- Corrected Lemma MC: multiscale across paths linked by around distances.
The grid approximation radius is `ρ n / 64` (ruling M18). -/
theorem internalDiam_le_of_multiscale (hd : 2 ≤ d) (D : ContMetric d)
    (hDl : D.IsLength) {U K : Set (Rd d)} (hU : IsOpen U)
    (_hK : IsCompact K) (hKc : IsConnected K)
    (ρ : ℕ → ℝ) (hρ0 : 0 < ρ 0) (hρ : ∀ n, ρ n = ρ 0 / 2 ^ n)
    (G : ℕ → Finset (Rd d))
    (hGK : ∀ n, ∀ z ∈ K, ∃ w ∈ G n, ‖z - w‖ ≤ ρ n / 64)
    (hGU : ∀ n, ∀ w ∈ G n, Metric.closedBall w (2 * ρ n) ⊆ U)
    (β : ℕ → ℝ) (hβ0 : ∀ n, 0 ≤ β n) (hβ : Summable β)
    (hacross : ∀ n, ∀ w ∈ G n,
      setDistIn D (ann w (ρ n / 16) (2 * ρ n))
        (Metric.sphere w (ρ n / 8)) (Metric.sphere w (ρ n)) ≤
          ENNReal.ofReal (β n))
    (haround : ∀ n, ∀ w ∈ G n,
      aroundDist D w (3 * ρ n / 16) (3 * ρ n / 8) ≤
        ENNReal.ofReal (β n)) :
    ⨆ (x ∈ K) (y ∈ K), D.internal U x y ≤
      ENNReal.ofReal ((5 + 2 * (G 0).card) * ∑' n, β n) := by
  classical
  have : 2 ≤ d := hd
  have hzU : ∀ z ∈ K, z ∈ U := by
    intro z hz
    obtain ⟨w, hw, hzw⟩ := hGK 0 z hz
    apply hGU 0 w hw
    rw [Metric.mem_closedBall, dist_eq_norm]
    exact hzw.trans (by linarith only [hρ0])
  have hβsum0 : 0 ≤ ∑' n, β n := tsum_nonneg hβ0
  refine iSup_le fun x => iSup_le fun hx => iSup_le fun y => iSup_le fun hy => ?_
  let N : ℝ := 5 + 2 * (G 0).card
  have hN : 0 < N := by
    have hcard : (0 : ℝ) ≤ (G 0).card := Nat.cast_nonneg _
    dsimp [N]
    linarith only [hcard]
  refine ENNReal.le_of_forall_pos_le_add fun ζ hζ _ => ?_
  let ε : ℝ := ζ / (2 * N)
  have hε : 0 < ε := div_pos (NNReal.coe_pos.mpr hζ) (mul_pos two_pos hN)
  let η : ℕ → ℝ := fun n => ε * (1 / 2 : ℝ) ^ n
  have hη : ∀ n, 0 < η n := by
    intro n
    exact mul_pos hε (pow_pos (by norm_num) _)
  have hηsum : Summable η := (summable_geometric_two).mul_left ε
  have hηtsum : (∑' n, η n) = 2 * ε := by
    dsimp [η]
    rw [tsum_mul_left, tsum_geometric_two]
    ring
  let b : ℕ → ℝ := fun n => β n + η n
  have hb : Summable b := hβ.add hηsum
  have hb0 : ∀ n, 0 ≤ b n := fun n => add_nonneg (hβ0 n) (hη n).le
  have hbtsum : (∑' n, b n) = (∑' n, β n) + 2 * ε := by
    change (tsum fun n : ℕ => β n + η n) = _
    rw [hβ.tsum_add hηsum, hηtsum]
  obtain ⟨hBsum, hBfin, hB0⟩ := w3_budget_finite hb hb0
  let paths : ∀ n, ∀ w : {w : Rd d // w ∈ G n},
      W3AcrossPath D w.1 (ρ n) (b n) := fun n w =>
    Classical.choice (w3_across_path_exists D (hβ0 n) (hη n)
      (hacross n w.1 w.2))
  obtain ⟨C, hCnear, hreach⟩ := w3_grid_reachable hKc hρ0
    (hGK 0) hx hy
  let centers (z : Rd d) (hz : z ∈ K) :
      ∀ n, {w : Rd d // w ∈ G n}
    | 0 => C z
    | n + 1 => ⟨Classical.choose (hGK (n + 1) z hz),
        (Classical.choose_spec (hGK (n + 1) z hz)).1⟩
  have hcenters : ∀ (z : Rd d) (hz : z ∈ K) (n : ℕ),
      ‖z - (centers z hz n).1‖ ≤ ρ n / 64 := by
    intro z hz n
    cases n with
    | zero => exact hCnear z hz
    | succ n => exact (Classical.choose_spec (hGK (n + 1) z hz)).2
  obtain ⟨sx, hsx, hdx⟩ := w3_descend D hDl hU ρ hρ0 hρ G hGU β η
    hβ0 hη haround paths (hzU x hx) (centers x hx)
    (hcenters x hx) hBfin hB0
  obtain ⟨sy, hsy, hdy⟩ := w3_descend D hDl hU ρ hρ0 hρ G hGU β η
    hβ0 hη haround paths (hzU y hy) (centers y hy)
    (hcenters y hy) hBfin hB0
  have hmiddle := w3_level0_bound D hρ0 (hβ0 0) (hη 0)
    (hGU 0) (haround 0) (paths 0) hreach hsx hsy
  have hβsmall : ENNReal.ofReal (b 0) ≤
      (∑' n, ENNReal.ofReal (b n)) := ENNReal.le_tsum (f := fun n => ENNReal.ofReal (b n)) 0
  have hbound : D.internal U x y ≤
      (5 + 2 * (G 0).card : ℝ≥0∞) * (∑' n, ENNReal.ofReal (b n)) := by
    have hleft : D.internal U x ((paths 0 (C x)).P sx) ≤
        2 * (∑' n, ENNReal.ofReal (b n)) := by
      rw [D.internal_comm]
      exact hdx
    have hright : D.internal U ((paths 0 (C y)).P sy) y ≤
        2 * (∑' n, ENNReal.ofReal (b n)) := hdy
    calc
      D.internal U x y ≤ D.internal U x ((paths 0 (C x)).P sx) +
          D.internal U ((paths 0 (C x)).P sx) y := D.internal_triangle U _ _ _
      _ ≤ D.internal U x ((paths 0 (C x)).P sx) +
          (D.internal U ((paths 0 (C x)).P sx) ((paths 0 (C y)).P sy) +
            D.internal U ((paths 0 (C y)).P sy) y) :=
          add_le_add le_rfl (D.internal_triangle U _ _ _)
      _ ≤ 2 * (∑' n, ENNReal.ofReal (b n)) +
          ((2 * (G 0).card + 1 : ℝ≥0∞) * ENNReal.ofReal (b 0) +
            2 * (∑' n, ENNReal.ofReal (b n))) := by
              gcongr
      _ ≤ 2 * (∑' n, ENNReal.ofReal (b n)) +
          ((2 * (G 0).card + 1 : ℝ≥0∞) * (∑' n, ENNReal.ofReal (b n)) +
            2 * (∑' n, ENNReal.ofReal (b n))) := by gcongr
      _ = _ := by ring
  have hcoeff : (5 + 2 * (G 0).card : ℝ≥0∞) = ENNReal.ofReal N := by
    dsimp [N]
    norm_num [ENNReal.ofReal_add, ENNReal.ofReal_mul]
  rw [hBsum, hbtsum, hcoeff, ← ENNReal.ofReal_mul hN.le] at hbound
  have heq : N * ((∑' n, β n) + 2 * ε) = N * (∑' n, β n) + ζ := by
    dsimp [ε]
    field_simp
  rw [heq] at hbound
  calc
    D.internal U x y ≤ ENNReal.ofReal (N * (∑' n, β n) + (ζ : ℝ)) := hbound
    _ = ENNReal.ofReal (N * (∑' n, β n)) + (ζ : ℝ≥0∞) := by
      rw [ENNReal.ofReal_add (mul_nonneg hN.le hβsum0) (NNReal.coe_nonneg ζ),
        ENNReal.ofReal_coe_nnreal]
    _ = _ := by rfl

end HigherDimLQGMetric
