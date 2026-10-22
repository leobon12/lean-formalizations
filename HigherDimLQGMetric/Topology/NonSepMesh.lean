import HigherDimLFPP.Frozen.Rd
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# The lattice mesh of the source's Lemma 4.1 (A16, Lemma M)

Packet M4 (optional target). Source: planning audit `planning/audits/MA1-sections-1-4.md`, item 26
and Details (a) **A16** (lattice mesh replacing the simplicial mesh of `∂B₂`, MA0-P7).

`𝒱` = the corners of the closed cubes of the lattice `δℤ^d` that meet `S` (A16: `S = ∂B₂`), `ℰ` =
pairs of corners at lattice distance `δ` (cube edges). Corners are recorded by their lattice
coordinates `m : Fin d → ℤ` (the corner is `δ • m`, `latticePoint δ m`).

* `meshGraph δ S`: the graph `(𝒱, ℰ)`, the nearest-neighbour graph of `ℤ^d` (`latticeGraph`)
  induced on `meshVertices δ S`; `latticeGraph_adj_iff_dist`: lattice neighbours are exactly the
  pairs of lattice points at Euclidean distance `δ`.
* `meshGraph_connected` (**Lemma M**, general form): for `δ > 0` and any nonempty preconnected
  `S ⊆ ℝ^d`, `(𝒱, ℰ)` is connected. `meshGraph_connected_sphere`: the case `S = ∂B(c, ρ)`, `d ≥ 2`.
* `meshVertices_finite`, `meshVertices_sphere_finite`: `𝒱` is finite for bounded `S`;
  `exists_isTree_le_meshGraph_sphere`: a spanning tree `𝒯 ⊆ ℰ` (Mathlib
  `SimpleGraph.Connected.exists_isTree_le`).

**Proof of Lemma M.** For `p ∈ S` let `⌊p/δ⌋` be its floor corner. (a) Any two corners of one cube
meeting `S` are joined inside the cube's 1-skeleton (flip the differing coordinates one at a
time), and all these corners lie in `𝒱`. (b) `⌊p/δ⌋` is a corner of every lattice cube containing
`p`. (c) For `q` near `p` the cube with lower corner `⌊q/δ⌋` contains `p` (coordinatewise: if
`|y - x| < min(⌊x⌋ + 1 - x, x - ⌈x⌉ + 1)` then `⌊y⌋ ≤ x ≤ ⌊y⌋ + 1`), so `⌊p/δ⌋` and `⌊q/δ⌋` are
corners of one cube meeting `S`. Hence "the floor corners are joined in `(𝒱, ℰ)`" is locally true
on `S`, so true for all `p, q ∈ S` (`IsPreconnected.induction₂'`); with (a) and (b) every vertex is
joined to the floor corner of a point of `S`. (This replaces A16's open–closed argument on `S` by
the same argument for an arbitrary preconnected `S`.)
-/

set_option autoImplicit false

noncomputable section

open scoped Topology

namespace HigherDimLQGMetric.Topology

open Set Metric Filter
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- The closed cube `∏ᵢ [kᵢ δ, (kᵢ + 1) δ]` of the lattice `δℤ^d` with lower corner `δ k`. -/
def latticeCube (δ : ℝ) (k : Fin d → ℤ) : Set (Rd d) :=
  {x | ∀ i, (k i : ℝ) * δ ≤ x i ∧ x i ≤ ((k i : ℝ) + 1) * δ}

/-- `m` is (the lattice coordinate of) a corner of the lattice cube with lower corner `k`. -/
def IsCubeCorner (k m : Fin d → ℤ) : Prop := ∀ i, m i = k i ∨ m i = k i + 1

/-- The nearest-neighbour graph of the lattice `ℤ^d`: `m` and `m'` differ in exactly one
coordinate, by one. -/
def latticeGraph (d : ℕ) : SimpleGraph (Fin d → ℤ) where
  Adj m m' := ∃ i, (m' i = m i + 1 ∨ m i = m' i + 1) ∧ ∀ j, j ≠ i → m' j = m j
  symm := ⟨fun _ _ ⟨i, h1, h2⟩ => ⟨i, h1.symm, fun j hj => (h2 j hj).symm⟩⟩
  loopless := ⟨fun _ ⟨_, h1, _⟩ => by omega⟩

/-- A16's vertex set `𝒱`: lattice coordinates of the corners of the closed cubes of `δℤ^d` that
meet `S`. -/
def meshVertices (δ : ℝ) (S : Set (Rd d)) : Set (Fin d → ℤ) :=
  {m | ∃ k, IsCubeCorner k m ∧ (latticeCube δ k ∩ S).Nonempty}

/-- A16's mesh graph `(𝒱, ℰ)`: the lattice nearest-neighbour graph induced on `𝒱`. -/
def meshGraph (δ : ℝ) (S : Set (Rd d)) : SimpleGraph (meshVertices δ S) :=
  (latticeGraph d).induce (meshVertices δ S)

/-- The lattice point `δ • m` of `ℝ^d`. -/
def latticePoint (δ : ℝ) (m : Fin d → ℤ) : Rd d := WithLp.toLp 2 fun i => δ * (m i : ℝ)

/-! ### Edges are the pairs at Euclidean distance `δ` -/

/-- An integer vector has squared norm `1` iff it is `± eᵢ` for some `i`. -/
lemma int_sum_sq_eq_one_iff (n : Fin d → ℤ) :
    ∑ i, n i ^ 2 = 1 ↔ ∃ i, (n i = 1 ∨ n i = -1) ∧ ∀ j, j ≠ i → n j = 0 := by
  classical
  constructor
  · intro h
    obtain ⟨i, hi⟩ : ∃ i, n i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      simp [hcon] at h
    have hsplit := Finset.add_sum_erase Finset.univ (fun j => n j ^ 2) (Finset.mem_univ i)
    have hrest : 0 ≤ ∑ j ∈ Finset.univ.erase i, n j ^ 2 :=
      Finset.sum_nonneg fun j _ => sq_nonneg (n j)
    have hi2 : 1 ≤ n i ^ 2 := by
      have : 0 < n i ^ 2 := by positivity
      omega
    have hi1 : n i ^ 2 = 1 := by omega
    have hrest0 : ∑ j ∈ Finset.univ.erase i, n j ^ 2 = 0 := by omega
    refine ⟨i, ?_, fun j hj => ?_⟩
    · have : n i * n i = 1 := by rw [← sq]; exact hi1
      rcases Int.eq_one_or_neg_one_of_mul_eq_one' this with h | h
      · exact Or.inl h.1
      · exact Or.inr h.1
    · have := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg (n j)).1 hrest0 j
        (Finset.mem_erase.2 ⟨hj, Finset.mem_univ j⟩)
      exact pow_eq_zero_iff (by norm_num) |>.1 this
  · rintro ⟨i, hi, hj⟩
    rw [Finset.sum_eq_single i (fun j _ hji => by rw [hj j hji]; norm_num)
      (fun h => absurd (Finset.mem_univ i) h)]
    rcases hi with h | h <;> rw [h] <;> norm_num

/-- Lattice neighbours are exactly the pairs of lattice points at Euclidean distance `δ`
(A16: "pairs of corners at lattice distance `δ`"). -/
theorem latticeGraph_adj_iff_dist {δ : ℝ} (hδ : 0 < δ) (m m' : Fin d → ℤ) :
    (latticeGraph d).Adj m m' ↔ dist (latticePoint δ m) (latticePoint δ m') = δ := by
  have hdist : dist (latticePoint δ m) (latticePoint δ m') =
      δ * Real.sqrt (((∑ i, (m i - m' i) ^ 2 : ℤ)) : ℝ) := by
    rw [EuclideanSpace.dist_eq]
    simp only [latticePoint, PiLp.toLp_apply, Real.dist_eq]
    have : ∀ i, |δ * (m i : ℝ) - δ * (m' i : ℝ)| ^ 2 = δ ^ 2 * (((m i - m' i) ^ 2 : ℤ) : ℝ) := by
      intro i
      rw [sq_abs]
      push_cast
      ring
    simp only [this, ← Finset.mul_sum]
    rw [Real.sqrt_mul (sq_nonneg δ), Real.sqrt_sq hδ.le]
    push_cast
    rfl
  rw [hdist]
  have key : δ * Real.sqrt (((∑ i, (m i - m' i) ^ 2 : ℤ)) : ℝ) = δ ↔
      ∑ i, (m i - m' i) ^ 2 = 1 := by
    constructor
    · intro h
      have h1 : Real.sqrt (((∑ i, (m i - m' i) ^ 2 : ℤ)) : ℝ) = 1 := by
        have := mul_left_cancel₀ hδ.ne' (h.trans (mul_one δ).symm)
        exact this
      have h2 : (((∑ i, (m i - m' i) ^ 2 : ℤ)) : ℝ) = 1 := by
        rw [Real.sqrt_eq_one] at h1
        exact h1
      exact_mod_cast h2
    · intro h
      rw [h]
      simp
  rw [key, int_sum_sq_eq_one_iff (fun i => m i - m' i)]
  constructor
  · rintro ⟨i, hi, hj⟩
    refine ⟨i, ?_, fun j hji => ?_⟩
    · rcases hi with h | h
      · right; omega
      · left; omega
    · have := hj j hji
      omega
  · rintro ⟨i, hi, hj⟩
    refine ⟨i, ?_, fun j hji => ?_⟩
    · rcases hi with h | h
      · right; omega
      · left; omega
    · have := hj j hji
      omega

/-! ### Cubes and floor corners -/

/-- Two corners of one lattice cube meeting `S` are joined in the mesh graph (inside the cube's
1-skeleton). -/
lemma meshGraph_reachable_of_isCubeCorner {δ : ℝ} {S : Set (Rd d)} {k : Fin d → ℤ}
    (hk : (latticeCube δ k ∩ S).Nonempty) {m m' : Fin d → ℤ} (hm : IsCubeCorner k m)
    (hm' : IsCubeCorner k m') :
    (meshGraph δ S).Reachable ⟨m, k, hm, hk⟩ ⟨m', k, hm', hk⟩ := by
  classical
  suffices H : ∀ n : ℕ, ∀ m : Fin d → ℤ, ∀ hm : IsCubeCorner k m,
      (Finset.univ.filter fun i => m i ≠ m' i).card = n →
        (meshGraph δ S).Reachable ⟨m, k, hm, hk⟩ ⟨m', k, hm', hk⟩ from H _ m hm rfl
  intro n
  induction n with
  | zero =>
    intro m hm hcard
    have hmm : m = m' := by
      funext i
      by_contra hne
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff] at hcard
      exact hcard (Finset.mem_univ i) hne
    subst hmm
    rfl
  | succ n ih =>
    intro m hm hcard
    obtain ⟨i, hi⟩ : ∃ i, m i ≠ m' i := by
      by_contra hcon
      push Not at hcon
      have : (Finset.univ.filter fun i => m i ≠ m' i) = ∅ :=
        Finset.filter_eq_empty_iff.2 fun j _ => not_not.2 (hcon j)
      rw [this, Finset.card_empty] at hcard
      omega
    set m₁ := Function.update m i (m' i) with hm₁def
    have hm₁ : IsCubeCorner k m₁ := by
      intro j
      by_cases hj : j = i
      · subst hj
        simp only [hm₁def, Function.update_self]
        exact hm' j
      · simp only [hm₁def, Function.update_of_ne hj]
        exact hm j
    have hadj : (meshGraph δ S).Adj ⟨m, k, hm, hk⟩ ⟨m₁, k, hm₁, hk⟩ := by
      show (latticeGraph d).Adj m m₁
      refine ⟨i, ?_, fun j hj => ?_⟩
      · simp only [hm₁def, Function.update_self]
        rcases hm i with h | h <;> rcases hm' i with h' | h' <;> omega
      · simp only [hm₁def, Function.update_of_ne hj]
    have hcard₁ : (Finset.univ.filter fun j => m₁ j ≠ m' j).card = n := by
      have : (Finset.univ.filter fun j => m₁ j ≠ m' j) =
          (Finset.univ.filter fun j => m j ≠ m' j).erase i := by
        ext j
        by_cases hj : j = i
        · subst hj
          simp [hm₁def]
        · simp [hm₁def, hj]
      rw [this, Finset.card_erase_of_mem (by simp [hi]), hcard, Nat.add_sub_cancel]
    exact hadj.reachable.trans (ih m₁ hm₁ hcard₁)

/-- The floor corner `⌊x / δ⌋` (coordinatewise) of a point `x`. -/
def floorCorner (δ : ℝ) (x : Rd d) : Fin d → ℤ := fun i => ⌊x i / δ⌋

/-- A point lies in the lattice cube with lower corner its floor corner. -/
lemma mem_latticeCube_floorCorner {δ : ℝ} (hδ : 0 < δ) (x : Rd d) :
    x ∈ latticeCube δ (floorCorner δ x) := by
  intro i
  constructor
  · have := Int.floor_le (x i / δ)
    rwa [le_div_iff₀ hδ] at this
  · have := Int.lt_floor_add_one (x i / δ)
    rw [div_lt_iff₀ hδ] at this
    exact this.le

/-- The floor corner of `x` is a corner of every lattice cube containing `x`. -/
lemma isCubeCorner_floorCorner {δ : ℝ} (hδ : 0 < δ) {k : Fin d → ℤ} {x : Rd d}
    (hx : x ∈ latticeCube δ k) : IsCubeCorner k (floorCorner δ x) := by
  intro i
  obtain ⟨h1, h2⟩ := hx i
  have h1' : (k i : ℝ) ≤ x i / δ := by rwa [le_div_iff₀ hδ]
  have h2' : x i / δ ≤ ((k i + 1 : ℤ) : ℝ) := by push_cast; rwa [div_le_iff₀ hδ]
  have a1 : k i ≤ ⌊x i / δ⌋ := Int.le_floor.2 h1'
  have a2 : ⌊x i / δ⌋ ≤ k i + 1 := by
    have := Int.floor_le_floor h2'
    rwa [Int.floor_intCast] at this
  simp only [floorCorner]
  omega

/-- For `q` close to `p`, the lattice cube with lower corner `⌊q / δ⌋` contains `p`. -/
lemma eventually_mem_latticeCube_floorCorner {δ : ℝ} (hδ : 0 < δ) (p : Rd d) :
    ∀ᶠ q in 𝓝 p, p ∈ latticeCube δ (floorCorner δ q) := by
  have hcoord : ∀ i, ∀ᶠ q in 𝓝 p,
      ((floorCorner δ q i : ℤ) : ℝ) * δ ≤ p i ∧ p i ≤ (((floorCorner δ q i : ℤ) : ℝ) + 1) * δ := by
    intro i
    set x := p i / δ with hx
    set η := min ((⌊x⌋ : ℝ) + 1 - x) (x - ⌈x⌉ + 1) with hη
    have hη0 : 0 < η :=
      lt_min (by linarith [Int.lt_floor_add_one x]) (by linarith [Int.ceil_lt_add_one x])
    have hcont : Continuous fun q : Rd d => q i / δ := by fun_prop
    filter_upwards [hcont.continuousAt.preimage_mem_nhds (ball_mem_nhds x hη0)] with q hq
    rw [mem_preimage, mem_ball, Real.dist_eq, abs_lt] at hq
    set y := q i / δ with hy
    have hη1 : η ≤ (⌊x⌋ : ℝ) + 1 - x := min_le_left _ _
    have hη2 : η ≤ x - ⌈x⌉ + 1 := min_le_right _ _
    -- `⌊y⌋ ≤ ⌊x⌋ ≤ x` and `x ≤ ⌈x⌉ ≤ ⌊y⌋ + 1`
    have b1 : ⌊y⌋ < ⌊x⌋ + 1 := by
      rw [Int.floor_lt]
      push_cast
      linarith
    have b2 : ⌈x⌉ - 1 ≤ ⌊y⌋ := by
      rw [Int.le_floor]
      push_cast
      linarith
    have c1 : (⌊y⌋ : ℝ) ≤ x := by
      have : ⌊y⌋ ≤ ⌊x⌋ := by omega
      have h := Int.floor_le x
      have : (⌊y⌋ : ℝ) ≤ ⌊x⌋ := by exact_mod_cast this
      linarith
    have c2 : x ≤ (⌊y⌋ : ℝ) + 1 := by
      have h := Int.le_ceil x
      have : (⌈x⌉ : ℝ) - 1 ≤ ⌊y⌋ := by exact_mod_cast b2
      linarith
    simp only [floorCorner]
    rw [← hy]
    constructor
    · rw [← le_div_iff₀ hδ]
      exact c1
    · rw [← div_le_iff₀ hδ]
      exact c2
  filter_upwards [eventually_all.2 hcoord] with q hq
  exact hq

/-! ### Lemma M -/

/-- **Lemma M (A16), general form.** For `δ > 0` and a nonempty preconnected `S ⊆ ℝ^d`, the
mesh graph `(𝒱, ℰ)` of the corners of the closed cubes of `δℤ^d` meeting `S` is connected. -/
theorem meshGraph_connected {δ : ℝ} (hδ : 0 < δ) {S : Set (Rd d)} (hS : IsPreconnected S)
    (hne : S.Nonempty) : (meshGraph δ S).Connected := by
  let R : (Fin d → ℤ) → (Fin d → ℤ) → Prop := fun m m' =>
    ∃ (hm : m ∈ meshVertices δ S) (hm' : m' ∈ meshVertices δ S),
      (meshGraph δ S).Reachable ⟨m, hm⟩ ⟨m', hm'⟩
  have hRtrans : ∀ m m' m'', R m m' → R m' m'' → R m m'' :=
    fun _ _ _ ⟨hm, _, h⟩ ⟨_, hm'', h'⟩ => ⟨hm, hm'', h.trans h'⟩
  have hcube : ∀ k, (latticeCube δ k ∩ S).Nonempty → ∀ m m', IsCubeCorner k m →
      IsCubeCorner k m' → R m m' := fun k hk m m' hm hm' =>
    ⟨⟨k, hm, hk⟩, ⟨k, hm', hk⟩, meshGraph_reachable_of_isCubeCorner hk hm hm'⟩
  have hself : ∀ q : Rd d, IsCubeCorner (floorCorner δ q) (floorCorner δ q) :=
    fun _ _ => Or.inl rfl
  -- the floor corners of the points of `S` are pairwise joined
  have hS' : ∀ p ∈ S, ∀ q ∈ S, R (floorCorner δ p) (floorCorner δ q) := by
    intro p hp q hq
    refine hS.induction₂' (fun p q => R (floorCorner δ p) (floorCorner δ q)) ?_
      (fun _ _ _ _ _ _ h₁ h₂ => hRtrans _ _ _ h₁ h₂) hp hq
    intro p _
    filter_upwards [nhdsWithin_le_nhds (eventually_mem_latticeCube_floorCorner hδ p),
      self_mem_nhdsWithin] with q hpq hq
    have hk : (latticeCube δ (floorCorner δ q) ∩ S).Nonempty :=
      ⟨q, mem_latticeCube_floorCorner hδ q, hq⟩
    have h1 : IsCubeCorner (floorCorner δ q) (floorCorner δ p) := isCubeCorner_floorCorner hδ hpq
    exact ⟨hcube _ hk _ _ h1 (hself q), hcube _ hk _ _ (hself q) h1⟩
  obtain ⟨p₀, hp₀⟩ := hne
  -- every vertex is joined to the floor corner of `p₀`
  have hall : ∀ m ∈ meshVertices δ S, R (floorCorner δ p₀) m := by
    rintro m ⟨k, hkm, p, hpk, hpS⟩
    exact hRtrans _ _ _ (hS' p₀ hp₀ p hpS)
      (hcube k ⟨p, hpk, hpS⟩ _ _ (isCubeCorner_floorCorner hδ hpk) hkm)
  have hv₀ : floorCorner δ p₀ ∈ meshVertices δ S :=
    ⟨_, hself p₀, p₀, mem_latticeCube_floorCorner hδ p₀, hp₀⟩
  have : Nonempty (meshVertices δ S) := ⟨⟨_, hv₀⟩⟩
  refine SimpleGraph.Connected.mk fun u v => ?_
  obtain ⟨_, _, hu⟩ := hall u.1 u.2
  obtain ⟨_, _, hv⟩ := hall v.1 v.2
  exact hu.symm.trans hv

/-- **Lemma M (A16)** for the sphere `S = ∂B(c, ρ)`, `ρ ≥ 0`, `d ≥ 2` (A16: `S = ∂B₂`). -/
theorem meshGraph_connected_sphere (hd : 2 ≤ d) {δ : ℝ} (hδ : 0 < δ) (c : Rd d) {ρ : ℝ}
    (hρ : 0 ≤ ρ) : (meshGraph δ (sphere c ρ)).Connected := by
  have hrank : 1 < Module.rank ℝ (Rd d) := by
    rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
    exact_mod_cast hd
  have : Nontrivial (Rd d) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; omega)
  exact meshGraph_connected hδ (isPreconnected_sphere hrank c ρ)
    (NormedSpace.sphere_nonempty.2 hρ)

/-- For bounded `S` the vertex set `𝒱` is finite. -/
theorem meshVertices_finite {δ : ℝ} (hδ : 0 < δ) {S : Set (Rd d)} (hS : Bornology.IsBounded S) :
    (meshVertices δ S).Finite := by
  obtain ⟨R, hR⟩ := hS.subset_closedBall 0
  set K : ℤ := ⌈R / δ⌉ + 1 with hK
  apply (Set.Finite.pi (t := fun _ : Fin d => Icc (-K) K) fun _ => Set.finite_Icc _ _).subset
  rintro m ⟨k, hkm, x, hxk, hxS⟩ i -
  have hxi : |x i| ≤ R := by
    have h1 := PiLp.norm_apply_le x i
    have h2 : ‖x‖ ≤ R := by simpa using hR hxS
    rw [Real.norm_eq_abs] at h1
    exact h1.trans h2
  obtain ⟨h1, h2⟩ := hxk i
  have hk1 : (k i : ℝ) ≤ R / δ := by
    rw [le_div_iff₀ hδ]
    linarith [(abs_le.1 hxi).2]
  have hk2 : -(R / δ) ≤ (k i : ℝ) + 1 := by
    rw [neg_le, le_div_iff₀ hδ]
    linarith [(abs_le.1 hxi).1]
  have a1 : k i ≤ ⌈R / δ⌉ := by
    have := hk1.trans (Int.le_ceil (R / δ))
    exact_mod_cast this
  have a2 : -⌈R / δ⌉ ≤ k i + 1 := by
    have h3 : -((⌈R / δ⌉ : ℤ) : ℝ) ≤ -(R / δ) := neg_le_neg (Int.le_ceil _)
    have := h3.trans hk2
    exact_mod_cast this
  rcases hkm i with h | h <;> constructor <;> omega

/-- For a sphere the vertex set `𝒱` is finite. -/
theorem meshVertices_sphere_finite {δ : ℝ} (hδ : 0 < δ) (c : Rd d) (ρ : ℝ) :
    (meshVertices δ (sphere c ρ)).Finite :=
  meshVertices_finite hδ isBounded_sphere

/-- A16's spanning tree `𝒯 ⊆ ℰ` of the mesh graph of a sphere (`d ≥ 2`). -/
theorem exists_isTree_le_meshGraph_sphere (hd : 2 ≤ d) {δ : ℝ} (hδ : 0 < δ) (c : Rd d) {ρ : ℝ}
    (hρ : 0 ≤ ρ) : ∃ T ≤ meshGraph δ (sphere c ρ), T.IsTree :=
  (meshGraph_connected_sphere hd hδ c hρ).exists_isTree_le

end HigherDimLQGMetric.Topology

end
