import HigherDimLQGMetric.Routing.Lattice

/-!
# Vertex balls, tubes, central boxes, routing regions and stars ([S] Lemma 4.1′, MA1 A16)

Packet S2a. Source: planning audit `planning/audits/MA1-sections-1-4.md`, Details (a) **A16**,
"Geometry (deterministic)"; blueprint Part A §4 (`blueprint/sections/s4-routing.tex`), Definition
`def:mesh` and Lemma `lem:mesh-geometry`, items (G2), (G3), (G5), (G6).

For `δ > 0` and points `v, w` of `ℝ^d` (a lattice edge `e = {v, w}` has `|v - w| = δ`):

* `vertBall δ v = B(v, δ/4)` (`N_v`);
* `edgeTube δ v w = {x : dist(x, [v, w]) < δ/16}` (`T_e`, as the `δ/16`-thickening of the segment);
* `centralBox δ v w`: the closed cube of side `δ/(40√d)` (half-diagonal `δ/80`) centred at the
  midpoint `m_e` (`Box_e`);
* `routingRegion δ v w = N_v ∪ (T_e ∩ {x : ⟪x - m_e, u_e⟫ > -δ/40})`, `u_e = (v - w)/δ`
  (`Ω_{v,e}` for the orientation `e = (v, w)`; `routingRegion δ w v` is `Ω_{w,e}`,
  `routingRegion_swap`);
* `meshStar δ m = N_v ∪ ⋃_{e ∋ v} T_e` (`Star_v`, `v = δ • m`), the union running over all lattice
  edges at `v` (so it contains the star over the mesh edges or over the spanning-tree edges).

Main facts (lattice edges are pairs of lattice neighbours, `latticeGraph`; distinct edges are
distinct unordered pairs `s(m₁, m₁') ≠ s(m₂, m₂')`):

* (G2) `disjoint_vertBall`, `disjoint_vertBall_edgeTube` (`N_u ∩ T_e = ∅` for `u ∉ e`, stronger than
  needed), `disjoint_edgeTube_of_not_common`, `edgeTube_inter_edgeTube_subset_vertBall`,
  `disjoint_edgeTube_diff` (the `T_e ∖ (N_v ∪ N_w)` are pairwise disjoint).
* (G3) `centralBox_subset_edgeTube_diff`, `disjoint_centralBox_edgeTube` (`Box_e ∩ T_{e'} = ∅`),
  `disjoint_centralBox_vertBall` (`Box_e ∩ N_u = ∅` for every lattice point `u`), and
  `norm_sub_midpoint_le_of_mem_centralBox`, `isCompact_centralBox`, `ball_subset_centralBox`.
* (G5) `isOpen_routingRegion`, `isConnected_routingRegion`, `centralBox_subset_routingRegion`,
  `disjoint_routingRegion_vertBall` (`Ω_{v,e} ∩ N_w = ∅`), `mem_routingRegion_self`.
* (G6) `vertBall_inter_routingRegion_subset`, `edgeTube_inter_routingRegion_subset`,
  `routingRegion_inter_routingRegion_subset`, `disjoint_routingRegion_vertBall_of_ne`,
  `disjoint_routingRegion_centralBox`.
* Stars: `meshStar_subset_ball` (`Star_v ⊆ B(v, 17δ/16)`), `diam_meshStar_le`
  (`diam Star_v ≤ 17δ/8`), `isOpen_meshStar`, and the containments of `N_v`, `T_e`, `Box_e`,
  `Ω_{v,e}` in `Star_v`.

No smallness of `δ` is needed here (only `δ > 0`); the collector and `V̄ ⊆ A_{1,3}` are in
`HigherDimLQGMetric.Routing.Collector`.
-/

set_option autoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set Metric
open HigherDimLFPP (Rd)
open HigherDimLQGMetric.Topology (latticePoint latticeGraph latticeGraph_adj_iff_dist)
open scoped InnerProductSpace
open Routing

variable {d : ℕ}

/-! ### Definitions -/

/-- The vertex ball `N_v = B(v, δ/4)` (A16). -/
def vertBall (δ : ℝ) (v : Rd d) : Set (Rd d) := ball v (δ / 4)

/-- The edge tube `T_e = {x : dist(x, [v, w]) < δ/16}` of `e = {v, w}` (A16), written as the
`δ/16`-thickening of the segment `[v, w]` (`edgeTube_eq_infDist`). -/
def edgeTube (δ : ℝ) (v w : Rd d) : Set (Rd d) := thickening (δ / 16) (segment ℝ v w)

/-- The central box `Box_e` of `e = {v, w}` (A16): the closed cube of side `δ/(40√d)` (half-side
`δ/(80√d)`, half-diagonal `δ/80`) centred at the midpoint `m_e` of `[v, w]`. -/
def centralBox (δ : ℝ) (v w : Rd d) : Set (Rd d) :=
  {x | ∀ i, |x i - midpoint ℝ v w i| ≤ δ / (80 * Real.sqrt d)}

/-- The routing region `Ω_{v,e} = N_v ∪ (T_e ∩ {x : ⟪x - m_e, u_e⟫ > -δ/40})` of the oriented
edge `e = (v, w)`, `u_e = (v - w)/δ` (A16). The region `Ω_{w,e}` of the other endpoint is
`routingRegion δ w v` (`routingRegion_swap`). -/
def routingRegion (δ : ℝ) (v w : Rd d) : Set (Rd d) :=
  vertBall δ v ∪
    (edgeTube δ v w ∩ {x | -(δ / 40) < ⟪x - midpoint ℝ v w, δ⁻¹ • (v - w)⟫_ℝ})

/-- The (geometric enlarged) star `Star_v = N_v ∪ ⋃_{e ∋ v} T_e` of the lattice point
`v = latticePoint δ m` (A16), the union running over all lattice edges `e` at `v`; it contains
the star over the mesh edges and over the edges of any spanning tree. -/
def meshStar (δ : ℝ) (m : Fin d → ℤ) : Set (Rd d) :=
  vertBall δ (latticePoint δ m) ∪
    ⋃ (m' : Fin d → ℤ) (_ : (latticeGraph d).Adj m m'),
      edgeTube δ (latticePoint δ m) (latticePoint δ m')

/-! ### Elementary properties -/

lemma isOpen_vertBall (δ : ℝ) (v : Rd d) : IsOpen (vertBall δ v) := isOpen_ball

lemma mem_vertBall_self {δ : ℝ} (hδ : 0 < δ) (v : Rd d) : v ∈ vertBall δ v :=
  mem_ball_self (by positivity)

lemma isOpen_edgeTube (δ : ℝ) (v w : Rd d) : IsOpen (edgeTube δ v w) := isOpen_thickening

lemma convex_edgeTube (δ : ℝ) (v w : Rd d) : Convex ℝ (edgeTube δ v w) :=
  (convex_segment v w).thickening _

lemma edgeTube_comm (δ : ℝ) (v w : Rd d) : edgeTube δ v w = edgeTube δ w v := by
  rw [edgeTube, edgeTube, segment_symm]

lemma segment_subset_edgeTube {δ : ℝ} (hδ : 0 < δ) (v w : Rd d) :
    segment ℝ v w ⊆ edgeTube δ v w :=
  self_subset_thickening (by positivity) _

lemma mem_edgeTube_left {δ : ℝ} (hδ : 0 < δ) (v w : Rd d) : v ∈ edgeTube δ v w :=
  segment_subset_edgeTube hδ v w (left_mem_segment ℝ v w)

lemma mem_edgeTube_right {δ : ℝ} (hδ : 0 < δ) (v w : Rd d) : w ∈ edgeTube δ v w :=
  segment_subset_edgeTube hδ v w (right_mem_segment ℝ v w)

/-- The tube is the set of points at distance `< δ/16` from the segment. -/
lemma edgeTube_eq_infDist (δ : ℝ) (v w : Rd d) :
    edgeTube δ v w = {x | infDist x (segment ℝ v w) < δ / 16} := by
  ext x
  exact mem_thickening_iff_infDist_lt ⟨v, left_mem_segment ℝ v w⟩

lemma centralBox_comm (δ : ℝ) (v w : Rd d) : centralBox δ v w = centralBox δ w v := by
  rw [centralBox, centralBox, midpoint_comm]

/-- The tube of a lattice edge depends only on the unordered pair of endpoints. -/
lemma edgeTube_eq_of_sym2_eq (δ : ℝ) {a b a' b' : Fin d → ℤ} (h : s(a, b) = s(a', b')) :
    edgeTube δ (latticePoint δ a) (latticePoint δ b) =
      edgeTube δ (latticePoint δ a') (latticePoint δ b') := by
  rw [edgeTube, edgeTube, segment_eq_of_sym2_eq h]

/-- The midpoint of a lattice edge depends only on the unordered pair of endpoints. -/
lemma Routing.midpoint_eq_of_sym2_eq (δ : ℝ) {a b a' b' : Fin d → ℤ} (h : s(a, b) = s(a', b')) :
    midpoint ℝ (latticePoint δ a) (latticePoint δ b) =
      midpoint ℝ (latticePoint δ a') (latticePoint δ b') := by
  rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact midpoint_comm _ _

/-- The box of a lattice edge depends only on the unordered pair of endpoints. -/
lemma centralBox_eq_of_sym2_eq (δ : ℝ) {a b a' b' : Fin d → ℤ} (h : s(a, b) = s(a', b')) :
    centralBox δ (latticePoint δ a) (latticePoint δ b) =
      centralBox δ (latticePoint δ a') (latticePoint δ b') := by
  rw [centralBox, centralBox, midpoint_eq_of_sym2_eq δ h]

/-- Lattice neighbours are at distance `δ`. -/
lemma dist_latticePoint_of_adj {δ : ℝ} (hδ : 0 < δ) {m m' : Fin d → ℤ}
    (h : (latticeGraph d).Adj m m') : dist (latticePoint δ m) (latticePoint δ m') = δ :=
  (latticeGraph_adj_iff_dist hδ m m').1 h

/-- Points of a segment are within the segment's length of its first endpoint. -/
lemma Routing.dist_le_of_mem_segment {v w y : Rd d} (hy : y ∈ segment ℝ v w) :
    dist y v ≤ dist w v :=
  (convex_closedBall v (dist w v)).segment_subset (mem_closedBall_self dist_nonneg)
    (mem_closedBall.2 le_rfl) hy

/-! ### (G2): vertex balls and tubes -/

/-- **(G2)** The vertex balls of distinct lattice points are disjoint. -/
theorem disjoint_vertBall {δ : ℝ} (hδ : 0 < δ) {m m' : Fin d → ℤ} (h : m ≠ m') :
    Disjoint (vertBall δ (latticePoint δ m)) (vertBall δ (latticePoint δ m')) :=
  ball_disjoint_ball (by linarith [le_dist_latticePoint hδ h])

/-- **(G2)** The vertex ball of a lattice point `u` that is not an endpoint of the lattice edge `e`
does not meet the tube `T_e` (this gives `N_u ∩ (T_e ∖ (N_v ∪ N_w)) = ∅`). -/
theorem disjoint_vertBall_edgeTube {δ : ℝ} (hδ : 0 < δ) {u m m' : Fin d → ℤ}
    (hadj : (latticeGraph d).Adj m m') (hu : u ≠ m) (hu' : u ≠ m') :
    Disjoint (vertBall δ (latticePoint δ u))
      (edgeTube δ (latticePoint δ m) (latticePoint δ m')) := by
  rw [Set.disjoint_left]
  intro x hx hxT
  obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.1 hxT
  have h1 := le_dist_latticePoint_segment hδ hadj hu hu' hy
  have h2 : dist x (latticePoint δ u) < δ / 4 := hx
  have h3 := dist_triangle_left (latticePoint δ u) y x
  linarith

/-- **(G2)** Tubes of lattice edges without a common endpoint are disjoint. -/
theorem disjoint_edgeTube_of_not_common {δ : ℝ} (hδ : 0 < δ) {m₁ m₁' m₂ m₂' : Fin d → ℤ}
    (h₁ : (latticeGraph d).Adj m₁ m₁') (h₂ : (latticeGraph d).Adj m₂ m₂')
    (hno : ∀ n, (n = m₁ ∨ n = m₁') → (n = m₂ ∨ n = m₂') → False) :
    Disjoint (edgeTube δ (latticePoint δ m₁) (latticePoint δ m₁'))
      (edgeTube δ (latticePoint δ m₂) (latticePoint δ m₂')) := by
  rw [Set.disjoint_left]
  intro x hx₁ hx₂
  obtain ⟨y₁, hy₁, hxy₁⟩ := mem_thickening_iff.1 hx₁
  obtain ⟨y₂, hy₂, hxy₂⟩ := mem_thickening_iff.1 hx₂
  have h := le_dist_of_mem_latticeSegment hδ (Or.inr h₁) (Or.inr h₂) hno hy₁ hy₂
  have h3 := dist_triangle_left y₁ y₂ x
  linarith

/-- **(G1)/(G2)** Tubes of two distinct lattice edges `[v, w₁]`, `[v, w₂]` at a common vertex
meet only inside `N_v`. -/
theorem edgeTube_inter_edgeTube_subset_vertBall {δ : ℝ} (hδ : 0 ≤ δ) {m m₁ m₂ : Fin d → ℤ}
    (h₁ : (latticeGraph d).Adj m m₁) (h₂ : (latticeGraph d).Adj m m₂) (hne : m₁ ≠ m₂) :
    edgeTube δ (latticePoint δ m) (latticePoint δ m₁) ∩
        edgeTube δ (latticePoint δ m) (latticePoint δ m₂) ⊆ vertBall δ (latticePoint δ m) := by
  rintro x ⟨hx₁, hx₂⟩
  have h := norm_sub_lt_of_mem_thickening_inter (inner_latticePoint_sub_nonpos δ h₁ h₂ hne) hx₁ hx₂
  rw [vertBall, mem_ball, dist_eq_norm]
  linarith

/-- **(G1)/(G2)** Tubes of two distinct lattice edges with a common endpoint `n` meet only inside
`N_n` (unordered form). -/
theorem edgeTube_inter_edgeTube_subset_of_common {δ : ℝ} (hδ : 0 ≤ δ)
    {m₁ m₁' m₂ m₂' n : Fin d → ℤ} (h₁ : (latticeGraph d).Adj m₁ m₁')
    (h₂ : (latticeGraph d).Adj m₂ m₂') (hne : s(m₁, m₁') ≠ s(m₂, m₂'))
    (hn₁ : n = m₁ ∨ n = m₁') (hn₂ : n = m₂ ∨ n = m₂') :
    edgeTube δ (latticePoint δ m₁) (latticePoint δ m₁') ∩
        edgeTube δ (latticePoint δ m₂) (latticePoint δ m₂') ⊆ vertBall δ (latticePoint δ n) := by
  obtain ⟨w₁, w₂, hw₁, hw₂, hw, e₁, e₂⟩ := exists_normal_form_of_common_endpoint h₁ h₂ hne hn₁ hn₂
  rw [edgeTube_eq_of_sym2_eq δ e₁, edgeTube_eq_of_sym2_eq δ e₂]
  exact edgeTube_inter_edgeTube_subset_vertBall hδ hw₁ hw₂ hw

/-- **(G2)** For distinct lattice edges `e, e'`, the sets `T_e ∖ (N_v ∪ N_w)` and
`T_{e'} ∖ (N_{v'} ∪ N_{w'})` are disjoint. -/
theorem disjoint_edgeTube_diff {δ : ℝ} (hδ : 0 < δ) {m₁ m₁' m₂ m₂' : Fin d → ℤ}
    (h₁ : (latticeGraph d).Adj m₁ m₁') (h₂ : (latticeGraph d).Adj m₂ m₂')
    (hne : s(m₁, m₁') ≠ s(m₂, m₂')) :
    Disjoint
      (edgeTube δ (latticePoint δ m₁) (latticePoint δ m₁') \
        (vertBall δ (latticePoint δ m₁) ∪ vertBall δ (latticePoint δ m₁')))
      (edgeTube δ (latticePoint δ m₂) (latticePoint δ m₂') \
        (vertBall δ (latticePoint δ m₂) ∪ vertBall δ (latticePoint δ m₂'))) := by
  rw [Set.disjoint_left]
  rintro x ⟨hx₁, hx₁'⟩ ⟨hx₂, -⟩
  by_cases hc : ∃ n, (n = m₁ ∨ n = m₁') ∧ (n = m₂ ∨ n = m₂')
  · obtain ⟨n, hn₁, hn₂⟩ := hc
    have hxn := edgeTube_inter_edgeTube_subset_of_common hδ.le h₁ h₂ hne hn₁ hn₂ ⟨hx₁, hx₂⟩
    rcases hn₁ with rfl | rfl
    · exact hx₁' (Or.inl hxn)
    · exact hx₁' (Or.inr hxn)
  · exact Set.disjoint_left.1
      (disjoint_edgeTube_of_not_common hδ h₁ h₂ fun n hn₁ hn₂ => hc ⟨n, hn₁, hn₂⟩) hx₁ hx₂

/-! ### (G3): central boxes -/

/-- Points of `Box_e` are within `δ/80` of the midpoint `m_e`. -/
theorem norm_sub_midpoint_le_of_mem_centralBox {δ : ℝ} (hδ : 0 ≤ δ) {v w x : Rd d}
    (hx : x ∈ centralBox δ v w) : ‖x - midpoint ℝ v w‖ ≤ δ / 80 := by
  set s : ℝ := δ / (80 * Real.sqrt d) with hs
  have hsum : ‖x - midpoint ℝ v w‖ ^ 2 ≤ (d : ℝ) * s ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc ∑ i, (x - midpoint ℝ v w) i ^ 2 ≤ ∑ _i : Fin d, s ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          have hi : |x i - midpoint ℝ v w i| ≤ s := hx i
          have h0 : 0 ≤ |x i - midpoint ℝ v w i| := abs_nonneg _
          rw [PiLp.sub_apply, ← sq_abs]
          exact pow_le_pow_left₀ h0 hi 2
      _ = (d : ℝ) * s ^ 2 := by simp
  have hds : (d : ℝ) * s ^ 2 ≤ (δ / 80) ^ 2 := by
    rcases Nat.eq_zero_or_pos d with hd | hd
    · subst hd
      simp only [Nat.cast_zero, zero_mul]
      positivity
    · have hd' : (0 : ℝ) < d := by exact_mod_cast hd
      have hsq : Real.sqrt d ^ 2 = d := Real.sq_sqrt hd'.le
      have hsqrt : 0 < Real.sqrt d := Real.sqrt_pos.2 hd'
      rw [hs, div_pow, mul_pow, hsq]
      field_simp
      rfl
  have h := hsum.trans hds
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 h

lemma midpoint_mem_centralBox {δ : ℝ} (hδ : 0 ≤ δ) (v w : Rd d) :
    midpoint ℝ v w ∈ centralBox δ v w := by
  intro i
  rw [sub_self, abs_zero]
  positivity

/-- The ball of radius `δ/(80√d)` (the half-side) around `m_e` lies in `Box_e`. -/
lemma ball_subset_centralBox (δ : ℝ) (v w : Rd d) :
    ball (midpoint ℝ v w) (δ / (80 * Real.sqrt d)) ⊆ centralBox δ v w := by
  intro x hx i
  exact ((Routing.abs_coord_sub_le_dist x (midpoint ℝ v w) i).trans (mem_ball.1 hx).le)

/-- For `d ≥ 1` and `δ > 0`, `Box_e` has nonempty interior. -/
lemma nonempty_interior_centralBox {δ : ℝ} (hδ : 0 < δ) (hd : 1 ≤ d) (v w : Rd d) :
    (interior (centralBox δ v w)).Nonempty := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have hr : 0 < δ / (80 * Real.sqrt d) := by
    have := Real.sqrt_pos.2 hd'
    positivity
  have hm : midpoint ℝ v w ∈ interior (ball (midpoint ℝ v w) (δ / (80 * Real.sqrt d))) := by
    rw [isOpen_ball.interior_eq]
    exact mem_ball_self hr
  exact ⟨midpoint ℝ v w, interior_mono (ball_subset_centralBox δ v w) hm⟩

lemma isClosed_centralBox (δ : ℝ) (v w : Rd d) : IsClosed (centralBox δ v w) := by
  have : centralBox δ v w =
      ⋂ i : Fin d, {x : Rd d | |x i - midpoint ℝ v w i| ≤ δ / (80 * Real.sqrt d)} := by
    ext x
    simp [centralBox]
  rw [this]
  exact isClosed_iInter fun i => isClosed_le (by fun_prop) continuous_const

lemma centralBox_subset_closedBall {δ : ℝ} (hδ : 0 ≤ δ) (v w : Rd d) :
    centralBox δ v w ⊆ closedBall (midpoint ℝ v w) (δ / 80) := fun _ hx =>
  mem_closedBall.2 (by rw [dist_eq_norm]; exact norm_sub_midpoint_le_of_mem_centralBox hδ hx)

/-- `Box_e` is compact. -/
lemma isCompact_centralBox {δ : ℝ} (hδ : 0 ≤ δ) (v w : Rd d) : IsCompact (centralBox δ v w) :=
  isCompact_of_isClosed_isBounded (isClosed_centralBox δ v w)
    (isBounded_closedBall.subset (centralBox_subset_closedBall hδ v w))

/-- **(G3)** `Box_e ⊆ T_e`. -/
theorem centralBox_subset_edgeTube {δ : ℝ} (hδ : 0 < δ) (v w : Rd d) :
    centralBox δ v w ⊆ edgeTube δ v w := by
  intro x hx
  refine mem_thickening_iff.2 ⟨midpoint ℝ v w, midpoint_mem_segment v w, ?_⟩
  rw [dist_eq_norm]
  have := norm_sub_midpoint_le_of_mem_centralBox hδ.le hx
  linarith

/-- The midpoint is at distance `δ/2` from both endpoints of an edge of length `δ`. -/
lemma Routing.norm_midpoint_sub_left {δ : ℝ} {v w : Rd d} (hvw : dist v w = δ) :
    ‖midpoint ℝ v w - v‖ = δ / 2 := by
  rw [midpoint_sub_left, norm_smul, ← dist_eq_norm, dist_comm, hvw]
  simp only [invOf_eq_inv, norm_inv, Real.norm_ofNat]
  ring

lemma Routing.norm_midpoint_sub_right {δ : ℝ} {v w : Rd d} (hvw : dist v w = δ) :
    ‖midpoint ℝ v w - w‖ = δ / 2 := by
  rw [midpoint_sub_right, norm_smul, ← dist_eq_norm, hvw]
  simp only [invOf_eq_inv, norm_inv, Real.norm_ofNat]
  ring

/-- **(G3)** `Box_e ∩ N_v = ∅` for the first endpoint `v` of `e = {v, w}`, `|v - w| = δ`. -/
theorem disjoint_centralBox_vertBall_left {δ : ℝ} (hδ : 0 < δ) {v w : Rd d}
    (hvw : dist v w = δ) : Disjoint (centralBox δ v w) (vertBall δ v) := by
  rw [Set.disjoint_left]
  intro x hx hxv
  have h1 := norm_sub_midpoint_le_of_mem_centralBox hδ.le hx
  have h2 : ‖x - v‖ < δ / 4 := by rw [← dist_eq_norm]; exact hxv
  have h3 : ‖midpoint ℝ v w - v‖ ≤ ‖x - midpoint ℝ v w‖ + ‖x - v‖ := by
    calc ‖midpoint ℝ v w - v‖ = ‖(x - v) - (x - midpoint ℝ v w)‖ := by congr 1; abel
      _ ≤ ‖x - v‖ + ‖x - midpoint ℝ v w‖ := norm_sub_le _ _
      _ = _ := add_comm _ _
  rw [norm_midpoint_sub_left hvw] at h3
  linarith

/-- **(G3)** `Box_e ∩ N_w = ∅` for the second endpoint `w` of `e = {v, w}`, `|v - w| = δ`. -/
theorem disjoint_centralBox_vertBall_right {δ : ℝ} (hδ : 0 < δ) {v w : Rd d}
    (hvw : dist v w = δ) : Disjoint (centralBox δ v w) (vertBall δ w) := by
  rw [centralBox_comm]
  exact disjoint_centralBox_vertBall_left hδ (by rw [dist_comm]; exact hvw)

/-- **(G3)** `Box_e ⊆ T_e ∖ (N_v ∪ N_w)` for `e = {v, w}`, `|v - w| = δ`. -/
theorem centralBox_subset_edgeTube_diff {δ : ℝ} (hδ : 0 < δ) {v w : Rd d}
    (hvw : dist v w = δ) :
    centralBox δ v w ⊆ edgeTube δ v w \ (vertBall δ v ∪ vertBall δ w) := by
  intro x hx
  refine ⟨centralBox_subset_edgeTube hδ v w hx, ?_⟩
  rintro (h | h)
  · exact Set.disjoint_left.1 (disjoint_centralBox_vertBall_left hδ hvw) hx h
  · exact Set.disjoint_left.1 (disjoint_centralBox_vertBall_right hδ hvw) hx h

/-- **(G3)** The midpoint of a lattice edge `e` is at distance `≥ δ/2` from every point of every
other lattice edge `e'`. -/
theorem le_dist_midpoint_latticeSegment {δ : ℝ} (hδ : 0 < δ) {m₁ m₁' m₂ m₂' : Fin d → ℤ}
    (h₁ : (latticeGraph d).Adj m₁ m₁') (h₂ : (latticeGraph d).Adj m₂ m₂')
    (hne : s(m₁, m₁') ≠ s(m₂, m₂')) {y : Rd d}
    (hy : y ∈ segment ℝ (latticePoint δ m₂) (latticePoint δ m₂')) :
    δ / 2 ≤ dist (midpoint ℝ (latticePoint δ m₁) (latticePoint δ m₁')) y := by
  by_cases hc : ∃ n, (n = m₁ ∨ n = m₁') ∧ (n = m₂ ∨ n = m₂')
  · obtain ⟨n, hn₁, hn₂⟩ := hc
    obtain ⟨w₁, w₂, hw₁, hw₂, hw, e₁, e₂⟩ :=
      exists_normal_form_of_common_endpoint h₁ h₂ hne hn₁ hn₂
    rw [midpoint_eq_of_sym2_eq δ e₁]
    rw [segment_eq_of_sym2_eq e₂] at hy
    have h := norm_sub_midpoint_ge_of_inner_nonpos (inner_latticePoint_sub_nonpos δ hw₁ hw₂ hw) hy
    rw [← dist_eq_norm, dist_comm, dist_latticePoint_of_adj hδ hw₁] at h
    rw [dist_eq_norm]
    exact h
  · have h := le_dist_of_mem_latticeSegment hδ (Or.inr h₁) (Or.inr h₂)
      (fun n hn₁ hn₂ => hc ⟨n, hn₁, hn₂⟩) (midpoint_mem_segment _ _) hy
    linarith

/-- **(G3)** `Box_e ∩ T_{e'} = ∅` for distinct lattice edges `e ≠ e'`. -/
theorem disjoint_centralBox_edgeTube {δ : ℝ} (hδ : 0 < δ) {m₁ m₁' m₂ m₂' : Fin d → ℤ}
    (h₁ : (latticeGraph d).Adj m₁ m₁') (h₂ : (latticeGraph d).Adj m₂ m₂')
    (hne : s(m₁, m₁') ≠ s(m₂, m₂')) :
    Disjoint (centralBox δ (latticePoint δ m₁) (latticePoint δ m₁'))
      (edgeTube δ (latticePoint δ m₂) (latticePoint δ m₂')) := by
  rw [Set.disjoint_left]
  intro x hx hxT
  obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.1 hxT
  have h1 := le_dist_midpoint_latticeSegment hδ h₁ h₂ hne hy
  have h2 := norm_sub_midpoint_le_of_mem_centralBox hδ.le hx
  rw [← dist_eq_norm] at h2
  have h3 := dist_triangle_left (midpoint ℝ (latticePoint δ m₁) (latticePoint δ m₁')) y x
  linarith

/-- **(G3)** `Box_e ∩ N_u = ∅` for every lattice point `u` (endpoint of `e` or not). -/
theorem disjoint_centralBox_vertBall {δ : ℝ} (hδ : 0 < δ) {m m' : Fin d → ℤ}
    (h : (latticeGraph d).Adj m m') (u : Fin d → ℤ) :
    Disjoint (centralBox δ (latticePoint δ m) (latticePoint δ m'))
      (vertBall δ (latticePoint δ u)) := by
  have hdist := dist_latticePoint_of_adj hδ h
  by_cases hu : u = m
  · subst hu
    exact disjoint_centralBox_vertBall_left hδ hdist
  by_cases hu' : u = m'
  · subst hu'
    exact disjoint_centralBox_vertBall_right hδ hdist
  exact Disjoint.mono_left (centralBox_subset_edgeTube hδ _ _)
    (disjoint_vertBall_edgeTube hδ h hu hu').symm

/-- **(G3)** Central boxes of distinct lattice edges are disjoint. -/
theorem disjoint_centralBox_centralBox {δ : ℝ} (hδ : 0 < δ) {m₁ m₁' m₂ m₂' : Fin d → ℤ}
    (h₁ : (latticeGraph d).Adj m₁ m₁') (h₂ : (latticeGraph d).Adj m₂ m₂')
    (hne : s(m₁, m₁') ≠ s(m₂, m₂')) :
    Disjoint (centralBox δ (latticePoint δ m₁) (latticePoint δ m₁'))
      (centralBox δ (latticePoint δ m₂) (latticePoint δ m₂')) :=
  Disjoint.mono_right (centralBox_subset_edgeTube hδ _ _)
    (disjoint_centralBox_edgeTube hδ h₁ h₂ hne)

/-- **(G2)**, literal form: for a lattice point `u` that is not an endpoint of `e = {v, w}`,
`N_u ∩ (T_e ∖ (N_v ∪ N_w)) = ∅`. -/
theorem disjoint_vertBall_edgeTube_diff {δ : ℝ} (hδ : 0 < δ) {u m m' : Fin d → ℤ}
    (hadj : (latticeGraph d).Adj m m') (hu : u ≠ m) (hu' : u ≠ m') :
    Disjoint (vertBall δ (latticePoint δ u))
      (edgeTube δ (latticePoint δ m) (latticePoint δ m') \
        (vertBall δ (latticePoint δ m) ∪ vertBall δ (latticePoint δ m'))) :=
  Disjoint.mono_right sdiff_subset (disjoint_vertBall_edgeTube hδ hadj hu hu')

/-! ### (G5): routing regions -/

lemma isOpen_routingRegion (δ : ℝ) (v w : Rd d) : IsOpen (routingRegion δ v w) :=
  (isOpen_vertBall δ v).union ((isOpen_edgeTube δ v w).inter
    (isOpen_lt continuous_const (by fun_prop)))

lemma vertBall_subset_routingRegion (δ : ℝ) (v w : Rd d) :
    vertBall δ v ⊆ routingRegion δ v w := subset_union_left

lemma mem_routingRegion_self {δ : ℝ} (hδ : 0 < δ) (v w : Rd d) : v ∈ routingRegion δ v w :=
  vertBall_subset_routingRegion δ v w (mem_vertBall_self hδ v)

lemma routingRegion_subset (δ : ℝ) (v w : Rd d) :
    routingRegion δ v w ⊆ vertBall δ v ∪ edgeTube δ v w :=
  union_subset_union_right _ inter_subset_left

/-- The routing region `Ω_{w,e}` of the second endpoint, as in A16:
`Ω_{w,e} = N_w ∪ (T_e ∩ {x : ⟪x - m_e, u_e⟫ < δ/40})`, `u_e = (v - w)/δ`. -/
theorem routingRegion_swap (δ : ℝ) (v w : Rd d) :
    routingRegion δ w v =
      vertBall δ w ∪ (edgeTube δ v w ∩ {x | ⟪x - midpoint ℝ v w, δ⁻¹ • (v - w)⟫_ℝ < δ / 40}) := by
  rw [routingRegion, edgeTube_comm, midpoint_comm]
  congr 2
  ext x
  simp only [mem_ofPred_eq]
  have : ⟪x - midpoint ℝ v w, δ⁻¹ • (w - v)⟫_ℝ = -⟪x - midpoint ℝ v w, δ⁻¹ • (v - w)⟫_ℝ := by
    rw [← inner_neg_right, ← smul_neg, neg_sub]
  rw [this]
  constructor <;> intro h <;> linarith

/-- Inner products against `u_e` relative to the endpoints. -/
lemma Routing.inner_sub_midpoint_unit {δ : ℝ} (hδ : 0 < δ) {v w : Rd d} (hvw : dist v w = δ)
    (x : Rd d) :
    ⟪x - midpoint ℝ v w, δ⁻¹ • (v - w)⟫_ℝ = ⟪x - v, δ⁻¹ • (v - w)⟫_ℝ + δ / 2 ∧
      ⟪x - midpoint ℝ v w, δ⁻¹ • (v - w)⟫_ℝ = ⟪x - w, δ⁻¹ • (v - w)⟫_ℝ - δ / 2 := by
  have hnorm : ‖v - w‖ = δ := by rw [← dist_eq_norm, hvw]
  have hvv : ⟪v - w, v - w⟫_ℝ = δ ^ 2 := by rw [real_inner_self_eq_norm_sq, hnorm]
  have hδ0 : δ ≠ 0 := hδ.ne'
  have e1 : x - midpoint ℝ v w = (x - v) + (v - midpoint ℝ v w) := by abel
  have e2 : x - midpoint ℝ v w = (x - w) + (w - midpoint ℝ v w) := by abel
  rw [left_sub_midpoint] at e1
  rw [right_sub_midpoint] at e2
  have k1 : ⟪⅟(2 : ℝ) • (v - w), δ⁻¹ • (v - w)⟫_ℝ = δ / 2 := by
    rw [real_inner_smul_left, real_inner_smul_right, hvv]
    simp only [invOf_eq_inv]
    field_simp
  have k2 : ⟪⅟(2 : ℝ) • (w - v), δ⁻¹ • (v - w)⟫_ℝ = -(δ / 2) := by
    rw [real_inner_smul_left, real_inner_smul_right, ← neg_sub v w, inner_neg_left, hvv]
    simp only [invOf_eq_inv]
    field_simp
  constructor
  · rw [e1, inner_add_left, k1]
  · rw [e2, inner_add_left, k2]
    ring

lemma Routing.norm_inv_smul_sub_eq_one {δ : ℝ} (hδ : 0 < δ) {v w : Rd d} (hvw : dist v w = δ) :
    ‖δ⁻¹ • (v - w)‖ = 1 := by
  rw [norm_smul, ← dist_eq_norm, hvw, norm_inv, Real.norm_eq_abs, abs_of_pos hδ,
    inv_mul_cancel₀ hδ.ne']

/-- `v` lies in the half-tube of `Ω_{v,e}`. -/
lemma Routing.mem_halfTube_left {δ : ℝ} (hδ : 0 < δ) (v w : Rd d) :
    v ∈ edgeTube δ v w ∩ {x | -(δ / 40) < ⟪x - midpoint ℝ v w, δ⁻¹ • (v - w)⟫_ℝ} := by
  refine ⟨mem_edgeTube_left hδ v w, ?_⟩
  simp only [mem_ofPred_eq]
  rw [left_sub_midpoint, real_inner_smul_left, real_inner_smul_right, real_inner_self_eq_norm_sq]
  have : 0 ≤ ⅟(2 : ℝ) * (δ⁻¹ * ‖v - w‖ ^ 2) := by
    simp only [invOf_eq_inv]
    positivity
  linarith [show 0 < δ / 40 by positivity]

lemma Routing.convex_halfSpace_inner (δ : ℝ) (v w : Rd d) :
    Convex ℝ {x : Rd d | -(δ / 40) < ⟪x - midpoint ℝ v w, δ⁻¹ • (v - w)⟫_ℝ} := by
  have : {x : Rd d | -(δ / 40) < ⟪x - midpoint ℝ v w, δ⁻¹ • (v - w)⟫_ℝ} =
      {x : Rd d | -(δ / 40) + ⟪midpoint ℝ v w, δ⁻¹ • (v - w)⟫_ℝ < ⟪x, δ⁻¹ • (v - w)⟫_ℝ} := by
    ext x
    simp only [mem_ofPred_eq, inner_sub_left]
    constructor <;> intro h <;> linarith
  rw [this]
  exact convex_halfSpace_gt
    ⟨fun x y => inner_add_left x y _, fun c x => by rw [real_inner_smul_left, smul_eq_mul]⟩ _

/-- **(G5)** `Ω_{v,e}` is connected: the union of the convex sets `N_v` and the half-tube, both
containing `v`. -/
theorem isConnected_routingRegion {δ : ℝ} (hδ : 0 < δ) (v w : Rd d) :
    IsConnected (routingRegion δ v w) := by
  refine ⟨⟨v, mem_routingRegion_self hδ v w⟩, ?_⟩
  exact IsPreconnected.union v (mem_vertBall_self hδ v) (mem_halfTube_left hδ v w)
    (convex_ball v _).isPreconnected
    ((convex_edgeTube δ v w).inter (convex_halfSpace_inner δ v w)).isPreconnected

/-- **(G5)** `Box_e ⊆ Ω_{v,e}` for `e = (v, w)`, `|v - w| = δ`. -/
theorem centralBox_subset_routingRegion {δ : ℝ} (hδ : 0 < δ) {v w : Rd d} (hvw : dist v w = δ) :
    centralBox δ v w ⊆ routingRegion δ v w := by
  intro x hx
  refine Or.inr ⟨centralBox_subset_edgeTube hδ v w hx, ?_⟩
  simp only [mem_ofPred_eq]
  have h1 := norm_sub_midpoint_le_of_mem_centralBox hδ.le hx
  have h2 := neg_abs_le ⟪x - midpoint ℝ v w, δ⁻¹ • (v - w)⟫_ℝ
  have h3 := abs_real_inner_le_norm (x - midpoint ℝ v w) (δ⁻¹ • (v - w))
  rw [norm_inv_smul_sub_eq_one hδ hvw, mul_one] at h3
  linarith

/-- **(G5)** `Ω_{v,e} ∩ N_w = ∅` for `e = (v, w)`, `|v - w| = δ`. -/
theorem disjoint_routingRegion_vertBall {δ : ℝ} (hδ : 0 < δ) {v w : Rd d} (hvw : dist v w = δ) :
    Disjoint (routingRegion δ v w) (vertBall δ w) := by
  rw [Set.disjoint_right]
  intro x hxw hx
  have hxw' : ‖x - w‖ < δ / 4 := by rw [← dist_eq_norm]; exact hxw
  rcases hx with hxv | ⟨-, hx⟩
  · -- `N_v ∩ N_w = ∅`
    have hxv' : dist x v < δ / 4 := hxv
    have := dist_triangle_left v w x
    rw [hvw, dist_eq_norm x w] at this
    linarith
  · simp only [mem_ofPred_eq] at hx
    rw [(inner_sub_midpoint_unit hδ hvw x).2] at hx
    have h3 := real_inner_le_norm (x - w) (δ⁻¹ • (v - w))
    rw [norm_inv_smul_sub_eq_one hδ hvw, mul_one] at h3
    linarith

/-- **(G5)**, the second endpoint: `Box_e ⊆ Ω_{w,e}` and `Ω_{w,e} ∩ N_v = ∅`. -/
theorem centralBox_subset_routingRegion_swap {δ : ℝ} (hδ : 0 < δ) {v w : Rd d}
    (hvw : dist v w = δ) : centralBox δ v w ⊆ routingRegion δ w v := by
  rw [centralBox_comm]
  exact centralBox_subset_routingRegion hδ (by rw [dist_comm]; exact hvw)

theorem disjoint_routingRegion_swap_vertBall {δ : ℝ} (hδ : 0 < δ) {v w : Rd d}
    (hvw : dist v w = δ) : Disjoint (routingRegion δ w v) (vertBall δ v) :=
  disjoint_routingRegion_vertBall hδ (by rw [dist_comm]; exact hvw)

/-! ### (G6): separation of routing regions -/

/-- **(G6)** For a lattice edge `e = (m, m')` and any lattice point `u ≠ m`: `N_u ∩ Ω_{m,e} = ∅`. -/
theorem disjoint_vertBall_routingRegion {δ : ℝ} (hδ : 0 < δ) {m m' u : Fin d → ℤ}
    (h : (latticeGraph d).Adj m m') (hu : u ≠ m) :
    Disjoint (vertBall δ (latticePoint δ u))
      (routingRegion δ (latticePoint δ m) (latticePoint δ m')) := by
  by_cases hu' : u = m'
  · subst hu'
    exact (disjoint_routingRegion_vertBall hδ (dist_latticePoint_of_adj hδ h)).symm
  · rw [routingRegion]
    refine Disjoint.union_right (disjoint_vertBall hδ hu) ?_
    exact Disjoint.mono_right inter_subset_left (disjoint_vertBall_edgeTube hδ h hu hu')

/-- **(G6)** For a lattice edge `(a, b)` and a lattice point `m ≠ a`: `Ω_{a,(a,b)} ∩ N_m = ∅`. -/
theorem disjoint_routingRegion_vertBall_of_ne {δ : ℝ} (hδ : 0 < δ) {a b m : Fin d → ℤ}
    (h : (latticeGraph d).Adj a b) (hm : a ≠ m) :
    Disjoint (routingRegion δ (latticePoint δ a) (latticePoint δ b))
      (vertBall δ (latticePoint δ m)) :=
  (disjoint_vertBall_routingRegion hδ h (Ne.symm hm)).symm

/-- **(G6)** `N_u ∩ Ω_{m,e} ⊆ N_m` for every lattice point `u`. -/
theorem vertBall_inter_routingRegion_subset {δ : ℝ} (hδ : 0 < δ) {m m' : Fin d → ℤ}
    (h : (latticeGraph d).Adj m m') (u : Fin d → ℤ) :
    vertBall δ (latticePoint δ u) ∩ routingRegion δ (latticePoint δ m) (latticePoint δ m') ⊆
      vertBall δ (latticePoint δ m) := by
  by_cases hu : u = m
  · subst hu
    exact inter_subset_left
  · intro x hx
    exact absurd hx.2 (Set.disjoint_left.1 (disjoint_vertBall_routingRegion hδ h hu) hx.1)

/-- **(G6)** For distinct lattice edges `e = (m, m')` and `e' = {a, b}`:
`T_{e'} ∩ Ω_{m,e} ⊆ N_m`. -/
theorem edgeTube_inter_routingRegion_subset {δ : ℝ} (hδ : 0 < δ) {m m' a b : Fin d → ℤ}
    (h : (latticeGraph d).Adj m m') (h' : (latticeGraph d).Adj a b) (hne : s(m, m') ≠ s(a, b)) :
    edgeTube δ (latticePoint δ a) (latticePoint δ b) ∩
        routingRegion δ (latticePoint δ m) (latticePoint δ m') ⊆ vertBall δ (latticePoint δ m) := by
  rintro x ⟨hxT, hx⟩
  rcases hx with hxm | ⟨hxT', hxH⟩
  · exact hxm
  by_cases hc : ∃ n, (n = m ∨ n = m') ∧ (n = a ∨ n = b)
  · obtain ⟨n, hn₁, hn₂⟩ := hc
    have hxn := edgeTube_inter_edgeTube_subset_of_common hδ.le h h' hne hn₁ hn₂ ⟨hxT', hxT⟩
    rcases hn₁ with rfl | rfl
    · exact hxn
    · exact absurd (Or.inr ⟨hxT', hxH⟩ : x ∈ routingRegion δ (latticePoint δ m) (latticePoint δ n))
        (Set.disjoint_right.1
          (disjoint_routingRegion_vertBall hδ (dist_latticePoint_of_adj hδ h)) hxn)
  · exact absurd hxT (Set.disjoint_left.1
      (disjoint_edgeTube_of_not_common hδ h h' fun n hn₁ hn₂ => hc ⟨n, hn₁, hn₂⟩) hxT')

/-- **(G6)** For distinct lattice edges `e = (m, m')`, `e' = {a, b}` and an endpoint `u` of `e'`:
`(N_u ∪ T_{e'}) ∩ Ω_{m,e} ⊆ N_m`. -/
theorem vertBall_union_edgeTube_inter_routingRegion_subset {δ : ℝ} (hδ : 0 < δ)
    {m m' a b : Fin d → ℤ} (h : (latticeGraph d).Adj m m') (h' : (latticeGraph d).Adj a b)
    (hne : s(m, m') ≠ s(a, b)) (u : Fin d → ℤ) :
    (vertBall δ (latticePoint δ u) ∪ edgeTube δ (latticePoint δ a) (latticePoint δ b)) ∩
        routingRegion δ (latticePoint δ m) (latticePoint δ m') ⊆ vertBall δ (latticePoint δ m) := by
  rw [union_inter_distrib_right]
  exact union_subset (vertBall_inter_routingRegion_subset hδ h u)
    (edgeTube_inter_routingRegion_subset hδ h h' hne)

/-- **(G6)** For distinct lattice edges `e = (m, m')`, `e' = (a, b)`: `Ω_{a,e'} ∩ Ω_{m,e} ⊆ N_m`
(and `Ω_{a,e'} ∩ N_m = ∅` if `a ≠ m`, `disjoint_routingRegion_vertBall_of_ne`). -/
theorem routingRegion_inter_routingRegion_subset {δ : ℝ} (hδ : 0 < δ) {m m' a b : Fin d → ℤ}
    (h : (latticeGraph d).Adj m m') (h' : (latticeGraph d).Adj a b) (hne : s(m, m') ≠ s(a, b)) :
    routingRegion δ (latticePoint δ a) (latticePoint δ b) ∩
        routingRegion δ (latticePoint δ m) (latticePoint δ m') ⊆ vertBall δ (latticePoint δ m) :=
  (inter_subset_inter_left _ (routingRegion_subset δ _ _)).trans
    (vertBall_union_edgeTube_inter_routingRegion_subset hδ h h' hne a)

/-- **(G6)** For distinct lattice edges `e = (m, m')`, `e' = {a, b}`: `Ω_{m,e} ∩ Box_{e'} = ∅`
(routing regions exclude every other central box). -/
theorem disjoint_routingRegion_centralBox {δ : ℝ} (hδ : 0 < δ) {m m' a b : Fin d → ℤ}
    (h : (latticeGraph d).Adj m m') (h' : (latticeGraph d).Adj a b) (hne : s(m, m') ≠ s(a, b)) :
    Disjoint (routingRegion δ (latticePoint δ m) (latticePoint δ m'))
      (centralBox δ (latticePoint δ a) (latticePoint δ b)) := by
  refine Disjoint.mono_left (routingRegion_subset δ _ _) (Disjoint.union_left ?_ ?_)
  · exact (disjoint_centralBox_vertBall hδ h' m).symm
  · exact (disjoint_centralBox_edgeTube hδ h' h (Ne.symm hne)).symm

/-! ### Stars -/

lemma vertBall_subset_meshStar (δ : ℝ) (m : Fin d → ℤ) :
    vertBall δ (latticePoint δ m) ⊆ meshStar δ m := subset_union_left

lemma edgeTube_subset_meshStar (δ : ℝ) {m m' : Fin d → ℤ} (h : (latticeGraph d).Adj m m') :
    edgeTube δ (latticePoint δ m) (latticePoint δ m') ⊆ meshStar δ m :=
  fun _ hx => Or.inr (mem_iUnion₂.2 ⟨m', h, hx⟩)

lemma edgeTube_subset_meshStar' (δ : ℝ) {m m' : Fin d → ℤ} (h : (latticeGraph d).Adj m m') :
    edgeTube δ (latticePoint δ m) (latticePoint δ m') ⊆ meshStar δ m' := by
  rw [edgeTube_comm]
  exact edgeTube_subset_meshStar δ h.symm

lemma routingRegion_subset_meshStar (δ : ℝ) {m m' : Fin d → ℤ} (h : (latticeGraph d).Adj m m') :
    routingRegion δ (latticePoint δ m) (latticePoint δ m') ⊆ meshStar δ m :=
  (routingRegion_subset δ _ _).trans
    (union_subset (vertBall_subset_meshStar δ m) (edgeTube_subset_meshStar δ h))

lemma centralBox_subset_meshStar {δ : ℝ} (hδ : 0 < δ) {m m' : Fin d → ℤ}
    (h : (latticeGraph d).Adj m m') :
    centralBox δ (latticePoint δ m) (latticePoint δ m') ⊆ meshStar δ m :=
  (centralBox_subset_edgeTube hδ _ _).trans (edgeTube_subset_meshStar δ h)

lemma centralBox_subset_meshStar' {δ : ℝ} (hδ : 0 < δ) {m m' : Fin d → ℤ}
    (h : (latticeGraph d).Adj m m') :
    centralBox δ (latticePoint δ m) (latticePoint δ m') ⊆ meshStar δ m' :=
  (centralBox_subset_edgeTube hδ _ _).trans (edgeTube_subset_meshStar' δ h)

lemma isOpen_meshStar (δ : ℝ) (m : Fin d → ℤ) : IsOpen (meshStar δ m) :=
  (isOpen_vertBall δ _).union (isOpen_iUnion fun _ => isOpen_iUnion fun _ => isOpen_edgeTube δ _ _)

/-- **Star diameter.** `Star_v ⊆ B(v, 17δ/16)`. -/
theorem meshStar_subset_ball {δ : ℝ} (hδ : 0 < δ) (m : Fin d → ℤ) :
    meshStar δ m ⊆ ball (latticePoint δ m) (17 * δ / 16) := by
  rintro x (hx | hx)
  · exact ball_subset_ball (by linarith) hx
  · obtain ⟨m', hm', hx⟩ := mem_iUnion₂.1 hx
    obtain ⟨y, hy, hxy⟩ := mem_thickening_iff.1 hx
    have h1 := dist_le_of_mem_segment hy
    rw [dist_comm (latticePoint δ m') _, dist_latticePoint_of_adj hδ hm'] at h1
    have h2 := dist_triangle x y (latticePoint δ m)
    rw [mem_ball]
    linarith

lemma meshStar_subset_closedBall {δ : ℝ} (hδ : 0 < δ) (m : Fin d → ℤ) :
    meshStar δ m ⊆ closedBall (latticePoint δ m) (17 * δ / 16) :=
  (meshStar_subset_ball hδ m).trans ball_subset_closedBall

/-- **Star diameter.** Any two points of `Star_v` are at distance `< 17δ/8`. -/
theorem dist_lt_of_mem_meshStar {δ : ℝ} (hδ : 0 < δ) {m : Fin d → ℤ} {x y : Rd d}
    (hx : x ∈ meshStar δ m) (hy : y ∈ meshStar δ m) : dist x y < 17 * δ / 8 := by
  have h1 := mem_ball.1 (meshStar_subset_ball hδ m hx)
  have h2 := mem_ball.1 (meshStar_subset_ball hδ m hy)
  have := dist_triangle_right x y (latticePoint δ m)
  linarith

/-- **Star diameter.** `diam Star_v ≤ 17δ/8`. -/
theorem diam_meshStar_le {δ : ℝ} (hδ : 0 < δ) (m : Fin d → ℤ) :
    Metric.diam (meshStar δ m) ≤ 17 * δ / 8 := by
  calc Metric.diam (meshStar δ m) ≤ Metric.diam (ball (latticePoint δ m) (17 * δ / 16)) :=
        Metric.diam_mono (meshStar_subset_ball hδ m) isBounded_ball
    _ ≤ 2 * (17 * δ / 16) := Metric.diam_ball (by positivity)
    _ = 17 * δ / 8 := by ring

end HigherDimLQGMetric
