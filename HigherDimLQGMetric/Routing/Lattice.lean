import HigherDimLQGMetric.Topology.NonSepMesh

/-!
# Lattice edges of the routing mesh ([S] Lemma 4.1′, MA1 A16, blueprint (G1))

Packet S2a. Source: planning audit `planning/audits/MA1-sections-1-4.md`, Details (a) **A16**,
"Geometry (deterministic)", and blueprint Part A §4 (`blueprint/sections/s4-routing.tex`, Lemma
`lem:mesh-geometry`, item (G1)).

The mesh vertices are the lattice points `latticePoint δ m = δ • m`, `m : Fin d → ℤ` (packet M4,
`HigherDimLQGMetric/Topology/NonSepMesh.lean`); a lattice edge is the segment between two lattice
neighbours (`latticeGraph d`). This file proves the elementary facts (G1):

* `exists_common_endpoint_of_dist_lt`: two lattice segments (edges, or degenerate edges = points)
  at distance `< δ` share an endpoint. Proof: coordinatewise, both segments lie in boxes with
  integer (× `δ`) corners; if every pair of coordinate intervals shares an integer, the integer
  point obtained is a lattice point of both boxes, hence an endpoint of both edges
  (`eq_or_eq_of_mem_latticeBox`); otherwise two coordinate intervals with integer endpoints are
  disjoint, hence `δ` apart.
* Corollaries: distinct lattice points are `δ` apart (`le_dist_latticePoint`); a lattice point
  that is not an endpoint of `e` is at distance `≥ δ` from `e` (`le_dist_latticePoint_segment`);
  disjoint edges are `δ` apart (`le_dist_of_mem_latticeSegment`).
* `inner_latticePoint_sub_nonpos`: two distinct lattice edges at a common vertex `v` are
  perpendicular or opposite: `⟪w₁ - v, w₂ - v⟫ ≤ 0`.
* Euclidean geometry at a non-acute corner (`sq_norm_add_sq_norm_le_of_inner_nonpos`):
  `‖y₁ - v‖² + ‖y₂ - v‖² ≤ ‖y₁ - y₂‖²` for `y₁ ∈ [v, w₁]`, `y₂ ∈ [v, w₂]`; hence two
  `r`-thickenings of such segments meet only within `3r` of `v`
  (`norm_sub_lt_of_mem_thickening_inter`), and the midpoint of `[v, w₁]` is at distance
  `≥ ‖w₁ - v‖ / 2` from `[v, w₂]`.
* `inter_segment_latticeSegment`: distinct lattice edges meet only at a common endpoint.

Generic helpers (coordinates, the 1D separation, the Euclidean lemmas at a non-acute corner, the
normal form of two edges with a common endpoint) live in the namespace
`HigherDimLQGMetric.Routing`; the (G1) facts live in `HigherDimLQGMetric`.
-/

set_option autoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set Metric
open HigherDimLFPP (Rd)
open HigherDimLQGMetric.Topology (latticePoint latticeGraph)
open scoped InnerProductSpace

variable {d : ℕ}

namespace Routing

/-! ### Coordinates -/

/-- Coordinates are `1`-Lipschitz on `ℝ^d`. -/
lemma abs_coord_sub_le_dist (x y : Rd d) (i : Fin d) : |x i - y i| ≤ dist x y := by
  have := PiLp.dist_apply_le x y i
  simpa [Real.dist_eq] using this

/-- Coordinates of a lattice point. -/
@[simp] lemma latticePoint_apply (δ : ℝ) (m : Fin d → ℤ) (i : Fin d) :
    latticePoint δ m i = δ * (m i : ℝ) := by
  simp [latticePoint]

/-- A point of a segment has each coordinate between the coordinates of the endpoints. -/
lemma coord_mem_uIcc_of_mem_segment {a b x : Rd d} (hx : x ∈ segment ℝ a b) (i : Fin d) :
    x i ∈ uIcc (a i) (b i) := by
  obtain ⟨s, t, hs, ht, hst, rfl⟩ := hx
  have h : (s • a + t • b) i = s * a i + t * b i := by simp
  rw [h]
  exact segment_subset_uIcc (𝕜 := ℝ) (a i) (b i) ⟨s, t, hs, ht, hst, by simp [smul_eq_mul]⟩

/-- A real between `δ a` and `δ b` lies between `δ min(a,b)` and `δ max(a,b)`. -/
lemma bounds_of_mem_uIcc_mul {δ : ℝ} (hδ : 0 ≤ δ) {a b : ℤ} {s : ℝ}
    (hs : s ∈ uIcc (δ * a) (δ * b)) :
    δ * ((min a b : ℤ) : ℝ) ≤ s ∧ s ≤ δ * ((max a b : ℤ) : ℝ) := by
  have h1 : δ * ((min a b : ℤ) : ℝ) ≤ δ * a :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast min_le_left a b) hδ
  have h2 : δ * ((min a b : ℤ) : ℝ) ≤ δ * b :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast min_le_right a b) hδ
  have h3 : δ * (a : ℝ) ≤ δ * ((max a b : ℤ) : ℝ) :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast le_max_left a b) hδ
  have h4 : δ * (b : ℝ) ≤ δ * ((max a b : ℤ) : ℝ) :=
    mul_le_mul_of_nonneg_left (by exact_mod_cast le_max_right a b) hδ
  rcases Set.mem_uIcc.1 hs with ⟨hs1, hs2⟩ | ⟨hs1, hs2⟩
  · exact ⟨h1.trans hs1, hs2.trans h4⟩
  · exact ⟨h2.trans hs1, hs2.trans h3⟩

/-- **1D separation.** If `s` lies between `δ a, δ b` and `t` between `δ c, δ e` (integers
`a, b, c, e`) and `|s - t| < δ`, the integer intervals `[min(a,b), max(a,b)]` and
`[min(c,e), max(c,e)]` share an integer. -/
lemma exists_int_mem_of_abs_sub_lt {δ : ℝ} (hδ : 0 < δ) {a b c e : ℤ} {s t : ℝ}
    (hs : s ∈ uIcc (δ * a) (δ * b)) (ht : t ∈ uIcc (δ * c) (δ * e)) (hst : |s - t| < δ) :
    ∃ n : ℤ, min a b ≤ n ∧ n ≤ max a b ∧ min c e ≤ n ∧ n ≤ max c e := by
  obtain ⟨hs1, hs2⟩ := bounds_of_mem_uIcc_mul hδ.le hs
  obtain ⟨ht1, ht2⟩ := bounds_of_mem_uIcc_mul hδ.le ht
  obtain ⟨hst1, hst2⟩ := abs_lt.1 hst
  -- the two intervals are not separated by a gap of at least one
  have g1 : min c e ≤ max a b := by
    by_contra h
    have h' : ((max a b : ℤ) : ℝ) + 1 ≤ ((min c e : ℤ) : ℝ) := by
      exact_mod_cast (show max a b + 1 ≤ min c e by omega)
    have : δ * ((max a b : ℤ) : ℝ) + δ ≤ δ * ((min c e : ℤ) : ℝ) := by
      nlinarith
    linarith
  have g2 : min a b ≤ max c e := by
    by_contra h
    have h' : ((max c e : ℤ) : ℝ) + 1 ≤ ((min a b : ℤ) : ℝ) := by
      exact_mod_cast (show max c e + 1 ≤ min a b by omega)
    have : δ * ((max c e : ℤ) : ℝ) + δ ≤ δ * ((min a b : ℤ) : ℝ) := by
      nlinarith
    linarith
  exact ⟨max (min a b) (min c e), le_max_left _ _, by omega, le_max_right _ _, by omega⟩

/-- The integer points of the box spanned by a lattice edge (or a single lattice point) are its
endpoints. -/
lemma eq_or_eq_of_mem_latticeBox {m m' n : Fin d → ℤ} (h : m = m' ∨ (latticeGraph d).Adj m m')
    (hn : ∀ j, min (m j) (m' j) ≤ n j ∧ n j ≤ max (m j) (m' j)) : n = m ∨ n = m' := by
  rcases h with rfl | ⟨i, hi, hj⟩
  · left
    funext j
    have := hn j
    omega
  · by_cases hni : n i = m i
    · left
      funext j
      by_cases hji : j = i
      · subst hji
        exact hni
      · have := hn j
        rw [hj j hji] at this
        omega
    · right
      funext j
      by_cases hji : j = i
      · subst hji
        have := hn j
        omega
      · have := hn j
        rw [hj j hji] at this ⊢
        omega

end Routing

open Routing

/-! ### (G1): separation of lattice edges -/

/-- **(G1), key lemma.** Two lattice segments (each an edge of the lattice or a single lattice
point) containing points at distance `< δ` share an endpoint. -/
theorem exists_common_endpoint_of_dist_lt {δ : ℝ} (hδ : 0 < δ) {m₁ m₁' m₂ m₂' : Fin d → ℤ}
    (h₁ : m₁ = m₁' ∨ (latticeGraph d).Adj m₁ m₁') (h₂ : m₂ = m₂' ∨ (latticeGraph d).Adj m₂ m₂')
    {x y : Rd d} (hx : x ∈ segment ℝ (latticePoint δ m₁) (latticePoint δ m₁'))
    (hy : y ∈ segment ℝ (latticePoint δ m₂) (latticePoint δ m₂')) (hxy : dist x y < δ) :
    ∃ n, (n = m₁ ∨ n = m₁') ∧ (n = m₂ ∨ n = m₂') := by
  have key : ∀ j, ∃ n : ℤ, min (m₁ j) (m₁' j) ≤ n ∧ n ≤ max (m₁ j) (m₁' j) ∧
      min (m₂ j) (m₂' j) ≤ n ∧ n ≤ max (m₂ j) (m₂' j) := by
    intro j
    have hxj := coord_mem_uIcc_of_mem_segment hx j
    have hyj := coord_mem_uIcc_of_mem_segment hy j
    simp only [latticePoint_apply] at hxj hyj
    exact exists_int_mem_of_abs_sub_lt hδ hxj hyj ((abs_coord_sub_le_dist x y j).trans_lt hxy)
  choose n hn using key
  exact ⟨n, eq_or_eq_of_mem_latticeBox h₁ fun j => ⟨(hn j).1, (hn j).2.1⟩,
    eq_or_eq_of_mem_latticeBox h₂ fun j => ⟨(hn j).2.2.1, (hn j).2.2.2⟩⟩

/-- **(G1)** Lattice edges (or lattice points) without a common endpoint are at distance `≥ δ`. -/
theorem le_dist_of_mem_latticeSegment {δ : ℝ} (hδ : 0 < δ) {m₁ m₁' m₂ m₂' : Fin d → ℤ}
    (h₁ : m₁ = m₁' ∨ (latticeGraph d).Adj m₁ m₁') (h₂ : m₂ = m₂' ∨ (latticeGraph d).Adj m₂ m₂')
    (hno : ∀ n, (n = m₁ ∨ n = m₁') → (n = m₂ ∨ n = m₂') → False)
    {x y : Rd d} (hx : x ∈ segment ℝ (latticePoint δ m₁) (latticePoint δ m₁'))
    (hy : y ∈ segment ℝ (latticePoint δ m₂) (latticePoint δ m₂')) : δ ≤ dist x y := by
  by_contra h
  obtain ⟨n, hn₁, hn₂⟩ := exists_common_endpoint_of_dist_lt hδ h₁ h₂ hx hy (not_le.1 h)
  exact hno n hn₁ hn₂

/-- **(G1)** Distinct lattice points are at distance `≥ δ`. -/
theorem le_dist_latticePoint {δ : ℝ} (hδ : 0 < δ) {m m' : Fin d → ℤ} (h : m ≠ m') :
    δ ≤ dist (latticePoint δ m) (latticePoint δ m') :=
  le_dist_of_mem_latticeSegment hδ (Or.inl rfl) (Or.inl rfl)
    (fun n hn hn' => h ((hn.elim id id).symm.trans (hn'.elim id id)))
    (by rw [segment_same]; exact mem_singleton _) (by rw [segment_same]; exact mem_singleton _)

/-- **(G1)** A lattice point that is not an endpoint of a lattice edge is at distance `≥ δ` from
every point of the edge. -/
theorem le_dist_latticePoint_segment {δ : ℝ} (hδ : 0 < δ) {u m m' : Fin d → ℤ}
    (hadj : (latticeGraph d).Adj m m') (hu : u ≠ m) (hu' : u ≠ m') {x : Rd d}
    (hx : x ∈ segment ℝ (latticePoint δ m) (latticePoint δ m')) :
    δ ≤ dist (latticePoint δ u) x :=
  le_dist_of_mem_latticeSegment hδ (Or.inl rfl) (Or.inr hadj)
    (fun n hn hn' => by
      have hnu : n = u := hn.elim id id
      subst hnu
      rcases hn' with h | h
      · exact hu h
      · exact hu' h)
    (by rw [segment_same]; exact mem_singleton _) hx

/-! ### Edges at a common vertex are perpendicular or opposite -/

/-- Two distinct lattice edges `[v, w₁]`, `[v, w₂]` at a common vertex are perpendicular or
opposite: `⟪w₁ - v, w₂ - v⟫ ≤ 0`. -/
theorem inner_latticePoint_sub_nonpos (δ : ℝ) {m m₁ m₂ : Fin d → ℤ}
    (h₁ : (latticeGraph d).Adj m m₁) (h₂ : (latticeGraph d).Adj m m₂) (hne : m₁ ≠ m₂) :
    ⟪latticePoint δ m₁ - latticePoint δ m, latticePoint δ m₂ - latticePoint δ m⟫_ℝ ≤ 0 := by
  obtain ⟨i, hi, hj⟩ := h₁
  obtain ⟨i', hi', hj'⟩ := h₂
  rw [PiLp.inner_apply, Finset.sum_eq_single i]
  · simp only [PiLp.sub_apply, latticePoint_apply, RCLike.inner_apply, conj_trivial]
    have hint : (m₂ i - m i) * (m₁ i - m i) ≤ 0 := by
      by_cases hii : i' = i
      · subst hii
        have hdiff : m₁ i' ≠ m₂ i' := by
          intro heq
          apply hne
          funext j
          by_cases hji : j = i'
          · subst hji
            exact heq
          · rw [hj j hji, hj' j hji]
        rcases hi with h | h <;> rcases hi' with h' | h'
        · exact absurd (h.trans h'.symm) hdiff
        · rw [h, h']; ring_nf; omega
        · rw [h, h']; ring_nf; omega
        · omega
      · rw [hj' i (Ne.symm hii)]
        simp
    have hint' : ((m₂ i : ℝ) - m i) * ((m₁ i : ℝ) - m i) ≤ 0 := by exact_mod_cast hint
    have : (δ * (m₂ i : ℝ) - δ * m i) * (δ * (m₁ i : ℝ) - δ * m i) =
        δ ^ 2 * (((m₂ i : ℝ) - m i) * ((m₁ i : ℝ) - m i)) := by ring
    rw [this]
    exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg δ) hint'
  · intro j _ hji
    simp [hj j hji]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-! ### Euclidean geometry at a non-acute corner -/

section Euclid

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- At a non-acute corner `⟪w₁ - v, w₂ - v⟫ ≤ 0`, points `y₁ ∈ [v, w₁]`, `y₂ ∈ [v, w₂]` satisfy
`‖y₁ - v‖² + ‖y₂ - v‖² ≤ ‖y₁ - y₂‖²`. -/
theorem Routing.sq_norm_add_sq_norm_le_of_inner_nonpos {v w₁ w₂ y₁ y₂ : E}
    (hinner : ⟪w₁ - v, w₂ - v⟫_ℝ ≤ 0) (hy₁ : y₁ ∈ segment ℝ v w₁) (hy₂ : y₂ ∈ segment ℝ v w₂) :
    ‖y₁ - v‖ ^ 2 + ‖y₂ - v‖ ^ 2 ≤ ‖y₁ - y₂‖ ^ 2 := by
  rw [segment_eq_image'] at hy₁ hy₂
  obtain ⟨t₁, ⟨ht₁, -⟩, rfl⟩ := hy₁
  obtain ⟨t₂, ⟨ht₂, -⟩, rfl⟩ := hy₂
  have e1 : v + t₁ • (w₁ - v) - v = t₁ • (w₁ - v) := by abel
  have e2 : v + t₂ • (w₂ - v) - v = t₂ • (w₂ - v) := by abel
  have e3 : v + t₁ • (w₁ - v) - (v + t₂ • (w₂ - v)) = t₁ • (w₁ - v) - t₂ • (w₂ - v) := by abel
  rw [e1, e2, e3, norm_sub_sq_real, real_inner_smul_left, real_inner_smul_right]
  have : t₁ * (t₂ * ⟪w₁ - v, w₂ - v⟫_ℝ) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos ht₁ (mul_nonpos_of_nonneg_of_nonpos ht₂ hinner)
  linarith

/-- At a non-acute corner, `‖y₁ - v‖ ≤ ‖y₁ - y₂‖` for `y₁ ∈ [v, w₁]`, `y₂ ∈ [v, w₂]`. -/
theorem Routing.norm_sub_le_of_inner_nonpos {v w₁ w₂ y₁ y₂ : E}
    (hinner : ⟪w₁ - v, w₂ - v⟫_ℝ ≤ 0) (hy₁ : y₁ ∈ segment ℝ v w₁) (hy₂ : y₂ ∈ segment ℝ v w₂) :
    ‖y₁ - v‖ ≤ ‖y₁ - y₂‖ := by
  have h := sq_norm_add_sq_norm_le_of_inner_nonpos hinner hy₁ hy₂
  have h' : ‖y₁ - v‖ ^ 2 ≤ ‖y₁ - y₂‖ ^ 2 := by nlinarith [sq_nonneg ‖y₂ - v‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h'

/-- At a non-acute corner, two `r`-thickenings of `[v, w₁]` and `[v, w₂]` meet only within `3r`
of `v`. -/
theorem Routing.norm_sub_lt_of_mem_thickening_inter {v w₁ w₂ x : E} {r : ℝ}
    (hinner : ⟪w₁ - v, w₂ - v⟫_ℝ ≤ 0) (h₁ : x ∈ thickening r (segment ℝ v w₁))
    (h₂ : x ∈ thickening r (segment ℝ v w₂)) : ‖x - v‖ < 3 * r := by
  obtain ⟨y₁, hy₁, hxy₁⟩ := mem_thickening_iff.1 h₁
  obtain ⟨y₂, hy₂, hxy₂⟩ := mem_thickening_iff.1 h₂
  rw [dist_eq_norm] at hxy₁ hxy₂
  have h12 : ‖y₁ - y₂‖ < 2 * r := by
    calc ‖y₁ - y₂‖ = ‖(x - y₂) - (x - y₁)‖ := by congr 1; abel
      _ ≤ ‖x - y₂‖ + ‖x - y₁‖ := norm_sub_le _ _
      _ < 2 * r := by linarith
  have hv := norm_sub_le_of_inner_nonpos hinner hy₁ hy₂
  calc ‖x - v‖ = ‖(x - y₁) + (y₁ - v)‖ := by congr 1; abel
    _ ≤ ‖x - y₁‖ + ‖y₁ - v‖ := norm_add_le _ _
    _ < 3 * r := by linarith

/-- At a non-acute corner, the midpoint of `[v, w₁]` is at distance `≥ ‖w₁ - v‖ / 2` from every
point of `[v, w₂]`. -/
theorem Routing.norm_sub_midpoint_ge_of_inner_nonpos {v w₁ w₂ y : E}
    (hinner : ⟪w₁ - v, w₂ - v⟫_ℝ ≤ 0) (hy : y ∈ segment ℝ v w₂) :
    ‖w₁ - v‖ / 2 ≤ ‖midpoint ℝ v w₁ - y‖ := by
  have h := norm_sub_le_of_inner_nonpos hinner (midpoint_mem_segment v w₁) hy
  have hm : ‖midpoint ℝ v w₁ - v‖ = ‖w₁ - v‖ / 2 := by
    rw [midpoint_sub_left, norm_smul]
    simp only [invOf_eq_inv, norm_inv, Real.norm_ofNat]
    ring
  rw [← hm]
  exact h

end Euclid

/-! ### Distinct edges meet only at common endpoints -/

/-- Normal form of two distinct lattice edges with a common endpoint `n`: they are `[n, w₁]` and
`[n, w₂]` with `w₁ ≠ w₂` lattice neighbours of `n`. -/
lemma Routing.exists_normal_form_of_common_endpoint {m₁ m₁' m₂ m₂' n : Fin d → ℤ}
    (h₁ : (latticeGraph d).Adj m₁ m₁') (h₂ : (latticeGraph d).Adj m₂ m₂')
    (hne : s(m₁, m₁') ≠ s(m₂, m₂')) (hn₁ : n = m₁ ∨ n = m₁') (hn₂ : n = m₂ ∨ n = m₂') :
    ∃ w₁ w₂, (latticeGraph d).Adj n w₁ ∧ (latticeGraph d).Adj n w₂ ∧ w₁ ≠ w₂ ∧
      s(m₁, m₁') = s(n, w₁) ∧ s(m₂, m₂') = s(n, w₂) := by
  have key : ∀ {a b : Fin d → ℤ}, (latticeGraph d).Adj a b → (n = a ∨ n = b) →
      ∃ w, (latticeGraph d).Adj n w ∧ s(a, b) = s(n, w) := by
    intro a b hab hn
    rcases hn with rfl | rfl
    · exact ⟨b, hab, rfl⟩
    · exact ⟨a, hab.symm, Sym2.eq_swap⟩
  obtain ⟨w₁, hw₁, e₁⟩ := key h₁ hn₁
  obtain ⟨w₂, hw₂, e₂⟩ := key h₂ hn₂
  refine ⟨w₁, w₂, hw₁, hw₂, fun hw => hne ?_, e₁, e₂⟩
  rw [e₁, e₂, hw]

/-- The segment of a lattice edge depends only on the unordered pair of endpoints. -/
lemma Routing.segment_eq_of_sym2_eq {δ : ℝ} {a b a' b' : Fin d → ℤ} (h : s(a, b) = s(a', b')) :
    segment ℝ (latticePoint δ a) (latticePoint δ b) =
      segment ℝ (latticePoint δ a') (latticePoint δ b') := by
  rcases Sym2.eq_iff.1 h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · exact segment_symm ℝ _ _

/-- **(G1)** Distinct lattice edges meet only at a common endpoint: a common point `x` of the
segments is the lattice point of an endpoint shared by both edges. -/
theorem inter_segment_latticeSegment {δ : ℝ} (hδ : 0 < δ) {m₁ m₁' m₂ m₂' : Fin d → ℤ}
    (h₁ : (latticeGraph d).Adj m₁ m₁') (h₂ : (latticeGraph d).Adj m₂ m₂')
    (hne : s(m₁, m₁') ≠ s(m₂, m₂')) {x : Rd d}
    (hx₁ : x ∈ segment ℝ (latticePoint δ m₁) (latticePoint δ m₁'))
    (hx₂ : x ∈ segment ℝ (latticePoint δ m₂) (latticePoint δ m₂')) :
    ∃ n, (n = m₁ ∨ n = m₁') ∧ (n = m₂ ∨ n = m₂') ∧ x = latticePoint δ n := by
  obtain ⟨n, hn₁, hn₂⟩ := exists_common_endpoint_of_dist_lt hδ (Or.inr h₁) (Or.inr h₂) hx₁ hx₂
    (by rw [dist_self]; exact hδ)
  obtain ⟨w₁, w₂, hw₁, hw₂, hw, e₁, e₂⟩ := exists_normal_form_of_common_endpoint h₁ h₂ hne hn₁ hn₂
  rw [segment_eq_of_sym2_eq e₁] at hx₁
  rw [segment_eq_of_sym2_eq e₂] at hx₂
  have hinner := inner_latticePoint_sub_nonpos δ hw₁ hw₂ hw
  have h := sq_norm_add_sq_norm_le_of_inner_nonpos hinner hx₁ hx₂
  rw [sub_self, norm_zero] at h
  have hx0 : ‖x - latticePoint δ n‖ = 0 := by nlinarith [sq_nonneg ‖x - latticePoint δ n‖]
  exact ⟨n, hn₁, hn₂, sub_eq_zero.1 (norm_eq_zero.1 hx0)⟩

end HigherDimLQGMetric
