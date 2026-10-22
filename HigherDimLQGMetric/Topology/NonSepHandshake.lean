import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Tactic.Ring
import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.ContinuousMap.Basic
import Mathlib.Order.Interval.Set.ProjIcc
import Mathlib.Topology.Order.ProjIcc

/-!
# Codimension-two nonseparation (D-NS), part 1: the handshake lemma on a cylinder (NS-1)

Packet M4 (ruling M9: the Krupski–Valov input [5] of the source's §4 is replaced by the elementary
theorem D-NS). Source: planning audit `planning/audits/MA1-sections-1-4.md`, item 25 and
Details (a) **A15**, step NS-1 (MA1 probe `mvH0_cylinder`).

**Statement (NS-1).** Let `G₁, G₂` be open in a topological space `Y` and `H : [0,1]² → G₁ ∪ G₂`
continuous with `H (0, t) = H (1, t)` (so `H` lives on a cylinder), the top edge mapped into `G₁`
(or into `G₂`), and the bottom edge mapped into `G₁` on `[0, 1/2]` and into `G₂` on `[1/2, 1]`.
Then `H (1/2, 0)` and `H (0, 0)` are joined by a path in `G₁ ∩ G₂`.

**Proof.** Take a Lebesgue number `δ` of the cover `{H⁻¹ G₁, H⁻¹ G₂}` of the compact square and
an even mesh `N = 2M > 1/δ`. Colour every closed grid cell `true` if `H` maps it into `G₁` and
`false` otherwise (then `H` maps it into `G₂`); add a virtual bottom row (colour `true` under
`[0, 1/2]`, `false` under `[1/2, 1]`) and a virtual top row (colour of the top edge). The
colour-change graph `gridGraph` on the grid vertices `(ℤ/N) × {0,…,N}` joins the two endpoints of
every grid edge whose two sides have different colours; `H` maps such an edge into `G₁ ∩ G₂`
(each side certifies one membership). The degree of a vertex is the number of colour changes
around it (`degree_gridGraph`): it is even except at the two bottom vertices where the bottom
colour changes, `(M, 0)` and `(0, 0)` (`odd_degree_gridGraph_iff`). By the handshake lemma
(Mathlib `SimpleGraph.exists_ne_odd_degree_of_exists_odd_degree`, applied to the connected
component of `(M, 0)`), the two are joined in the graph (`gridGraph_reachable`), and the image of a
graph path is a path in `G₁ ∩ G₂` (`joinedIn_inter_of_cylinder`).

## Main statements

* `HigherDimLQGMetric.Topology.gridGraph_reachable`: the combinatorial handshake on the cylinder
  grid (any colouring with constant top colour and bottom colour changing exactly at two
  columns).
* `HigherDimLQGMetric.Topology.joinedIn_inter_of_cylinder`: NS-1 with the top edge in `G₁` or
  in `G₂` (`colourSet G₁ G₂ b₀`).
* `HigherDimLQGMetric.Topology.mvH0_cylinder`: NS-1 in the exact shape of the MA1 probe.
-/

set_option autoImplicit false

noncomputable section

namespace HigherDimLQGMetric.Topology

open Finset

/-! ### The colour-change graph of the cylinder grid (combinatorial handshake) -/

section GridGraph

variable {N : ℕ} [NeZero N]

/-- Horizontal grid edge from `u` to `w = u + (1, 0)` (indices of the first coordinate mod `N`),
separating the cells `(u.1, u.2 - 1)` (below) and `(u.1, u.2)` (above), whose colours differ. -/
def GridH (c : Fin N → ℤ → Bool) (u w : Fin N × Fin (N + 1)) : Prop :=
  u.2 = w.2 ∧ w.1 = u.1 + 1 ∧ c u.1 ((u.2.val : ℤ) - 1) ≠ c u.1 (u.2.val : ℤ)

/-- Vertical grid edge from `u` to `w = u + (0, 1)`, separating the cells `(u.1 - 1, u.2)` (left)
and `(u.1, u.2)` (right), whose colours differ. -/
def GridV (c : Fin N → ℤ → Bool) (u w : Fin N × Fin (N + 1)) : Prop :=
  u.1 = w.1 ∧ w.2.val = u.2.val + 1 ∧ c (u.1 - 1) (u.2.val : ℤ) ≠ c u.1 (u.2.val : ℤ)

instance (c : Fin N → ℤ → Bool) (u w : Fin N × Fin (N + 1)) : Decidable (GridH c u w) := by
  unfold GridH; infer_instance

instance (c : Fin N → ℤ → Bool) (u w : Fin N × Fin (N + 1)) : Decidable (GridV c u w) := by
  unfold GridV; infer_instance

/-- The colour-change graph of a colouring `c` of the cells of the cylinder grid
`(ℤ/N) × [0, N]`: two grid vertices are adjacent when they span a grid edge whose two sides
have different colours.  Cells are indexed by their lower-left corner; heights `-1` and `N`
are the virtual boundary cells. -/
def gridGraph (c : Fin N → ℤ → Bool) : SimpleGraph (Fin N × Fin (N + 1)) where
  Adj u w := u ≠ w ∧ (GridH c u w ∨ GridH c w u ∨ GridV c u w ∨ GridV c w u)
  symm := ⟨fun u w h => ⟨h.1.symm, by rcases h.2 with h | h | h | h <;> tauto⟩⟩
  loopless := ⟨fun u h => h.1 rfl⟩

instance (c : Fin N → ℤ → Bool) : DecidableRel (gridGraph c).Adj := fun u w => by
  unfold gridGraph; infer_instance

lemma fin_add_one_ne (hN : 2 < N) (i : Fin N) : i + 1 ≠ i := by
  intro h
  have h1 : (1 : Fin N) = 0 := by
    have := congrArg (fun x => x - i) h
    simpa using this
  have := congrArg Fin.val h1
  rw [Fin.val_one', Fin.val_zero, Nat.mod_eq_of_lt (by omega)] at this
  omega

lemma fin_add_two_ne (hN : 2 < N) (i : Fin N) : i + 1 + 1 ≠ i := by
  intro h
  have h1 : (1 : Fin N) + 1 = 0 := by
    have := congrArg (· - i) h
    rwa [add_assoc, add_sub_cancel_left, sub_self] at this
  have := congrArg Fin.val h1
  rw [Fin.val_add, Fin.val_one', Fin.val_zero, Nat.mod_eq_of_lt (by omega : 1 < N),
    Nat.mod_eq_of_lt (by omega : 1 + 1 < N)] at this
  omega

lemma card_filter_eq_ite {α : Type*} [Fintype α] [DecidableEq α] (P : α → Prop)
    [DecidablePred P] (w₀ : α) (C : Prop) [Decidable C] (h : ∀ w, P w ↔ w = w₀ ∧ C) :
    #{w | P w} = if C then 1 else 0 := by
  split_ifs with hC
  · rw [Finset.card_eq_one]
    refine ⟨w₀, ?_⟩
    ext w
    simp [h, hC]
  · rw [Finset.card_eq_zero]
    ext w
    simp [h, hC]

lemma card_filter_eq_zero_of {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P]
    (h : ∀ w, ¬ P w) : #{w | P w} = 0 := by
  rw [Finset.card_eq_zero]
  ext w
  simp [h]

variable (c : Fin N → ℤ → Bool)

/-- Number of horizontal graph edges from `v` to the right (`0` or `1`). -/
lemma card_gridH_right (v : Fin N × Fin (N + 1)) :
    #{w | GridH c v w} = if c v.1 ((v.2.val : ℤ) - 1) ≠ c v.1 (v.2.val : ℤ) then 1 else 0 := by
  apply card_filter_eq_ite _ (v.1 + 1, v.2)
  intro w
  unfold GridH
  constructor
  · rintro ⟨h2, h1, hc⟩
    exact ⟨Prod.ext h1 h2.symm, hc⟩
  · rintro ⟨rfl, hc⟩
    exact ⟨rfl, rfl, hc⟩

/-- Number of horizontal graph edges from `v` to the left (`0` or `1`). -/
lemma card_gridH_left (v : Fin N × Fin (N + 1)) :
    #{w | GridH c w v} =
      if c (v.1 - 1) ((v.2.val : ℤ) - 1) ≠ c (v.1 - 1) (v.2.val : ℤ) then 1 else 0 := by
  apply card_filter_eq_ite _ (v.1 - 1, v.2)
  intro w
  unfold GridH
  constructor
  · rintro ⟨h2, h1, hc⟩
    have h1' : w.1 = v.1 - 1 := eq_sub_of_add_eq h1.symm
    refine ⟨Prod.ext h1' h2, ?_⟩
    rw [← h1', ← h2]
    exact hc
  · rintro ⟨rfl, hc⟩
    exact ⟨rfl, by simp, hc⟩

/-- Number of vertical graph edges from `v` upwards (`0` or `1`). -/
lemma card_gridV_up (v : Fin N × Fin (N + 1)) :
    #{w | GridV c v w} =
      if v.2.val < N ∧ c (v.1 - 1) (v.2.val : ℤ) ≠ c v.1 (v.2.val : ℤ) then 1 else 0 := by
  by_cases hv : v.2.val < N
  · apply card_filter_eq_ite _ (v.1, ⟨v.2.val + 1, by omega⟩)
    intro w
    unfold GridV
    constructor
    · rintro ⟨h1, h2, hc⟩
      exact ⟨Prod.ext h1.symm (Fin.ext h2), hv, hc⟩
    · rintro ⟨rfl, -, hc⟩
      exact ⟨rfl, rfl, hc⟩
  · simp only [hv, false_and, ↓reduceIte]
    apply card_filter_eq_zero_of
    rintro w ⟨-, h2, -⟩
    have := w.2.isLt
    omega

/-- Number of vertical graph edges from `v` downwards (`0` or `1`). -/
lemma card_gridV_down (v : Fin N × Fin (N + 1)) :
    #{w | GridV c w v} =
      if 0 < v.2.val ∧ c (v.1 - 1) ((v.2.val : ℤ) - 1) ≠ c v.1 ((v.2.val : ℤ) - 1)
      then 1 else 0 := by
  by_cases hv : 0 < v.2.val
  · apply card_filter_eq_ite _ (v.1, ⟨v.2.val - 1, by omega⟩)
    intro w
    unfold GridV
    constructor
    · rintro ⟨h1, h2, hc⟩
      refine ⟨Prod.ext h1 (Fin.ext (by simp only; omega)), hv, ?_⟩
      have : ((w.2.val : ℕ) : ℤ) = (v.2.val : ℤ) - 1 := by omega
      rw [this, h1] at hc
      exact hc
    · rintro ⟨rfl, -, hc⟩
      refine ⟨rfl, by simp only; omega, ?_⟩
      have : (((v.2.val - 1 : ℕ)) : ℤ) = (v.2.val : ℤ) - 1 := by omega
      simp only [this]
      exact hc
  · simp only [hv, false_and, ↓reduceIte]
    apply card_filter_eq_zero_of
    rintro w ⟨-, h2, -⟩
    omega

/-- The degree of a grid vertex is the number of colour changes around it. -/
lemma degree_gridGraph (hN : 2 < N) (v : Fin N × Fin (N + 1)) :
    (gridGraph c).degree v =
      (if c v.1 ((v.2.val : ℤ) - 1) ≠ c v.1 (v.2.val : ℤ) then 1 else 0) +
      (if c (v.1 - 1) ((v.2.val : ℤ) - 1) ≠ c (v.1 - 1) (v.2.val : ℤ) then 1 else 0) +
      (if v.2.val < N ∧ c (v.1 - 1) (v.2.val : ℤ) ≠ c v.1 (v.2.val : ℤ) then 1 else 0) +
      (if 0 < v.2.val ∧ c (v.1 - 1) ((v.2.val : ℤ) - 1) ≠ c v.1 ((v.2.val : ℤ) - 1)
        then 1 else 0) := by
  rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
  have hadj : ∀ w, (gridGraph c).Adj v w ↔
      ((GridH c v w ∨ GridH c w v) ∨ GridV c v w) ∨ GridV c w v := by
    intro w
    simp only [gridGraph, or_assoc]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      rintro rfl
      rcases h with h | h | h | h
      · exact fin_add_one_ne hN v.1 h.2.1.symm
      · exact fin_add_one_ne hN v.1 h.2.1.symm
      · exact absurd h.2.1 (by omega)
      · exact absurd h.2.1 (by omega)
  rw [Finset.filter_congr (fun w _ => hadj w)]
  rw [Finset.filter_or, card_union_of_disjoint (Finset.disjoint_filter.2 ?_), Finset.filter_or,
    card_union_of_disjoint (Finset.disjoint_filter.2 ?_), Finset.filter_or,
    card_union_of_disjoint (Finset.disjoint_filter.2 ?_), card_gridH_right, card_gridH_left,
    card_gridV_up, card_gridV_down]
  · rintro w - ⟨-, h1, -⟩ ⟨-, h1', -⟩
    rw [h1] at h1'
    exact fin_add_two_ne hN v.1 h1'.symm
  · rintro w - (⟨h2, -, -⟩ | ⟨h2, -, -⟩) ⟨-, h3, -⟩
    · rw [← h2] at h3; omega
    · rw [h2] at h3; omega
  · rintro w - ((⟨h2, -, -⟩ | ⟨h2, -, -⟩) | ⟨-, h3, -⟩) ⟨-, h4, -⟩
    · rw [← h2] at h4; omega
    · rw [h2] at h4; omega
    · omega

private lemma bool_cycle (a b e f : Bool) :
    ¬ Odd ((if b ≠ e then 1 else 0) + (if a ≠ f then 1 else 0) + (if f ≠ e then 1 else 0) +
      (if a ≠ b then 1 else 0) : ℕ) := by
  revert a b e f; decide

private lemma bool_open (a b e f : Bool) :
    Odd ((if b ≠ e then 1 else 0) + (if a ≠ f then 1 else 0) + (if f ≠ e then 1 else 0) : ℕ) ↔
      a ≠ b := by
  revert a b e f; decide

private lemma bool_top (a b t : Bool) :
    ¬ Odd ((if b ≠ t then 1 else 0) + (if a ≠ t then 1 else 0) + (if a ≠ b then 1 else 0) : ℕ) := by
  revert a b t; decide

/-- Parity of the degrees: with a constant top colour, a vertex has odd degree exactly when it
lies on the bottom row and the two virtual bottom cells adjacent to it have different colours. -/
lemma odd_degree_gridGraph_iff (hN : 2 < N) (b₀ : Bool) (htop : ∀ i, c i (N : ℤ) = b₀)
    (v : Fin N × Fin (N + 1)) :
    Odd ((gridGraph c).degree v) ↔ v.2.val = 0 ∧ c (v.1 - 1) (-1) ≠ c v.1 (-1) := by
  rw [degree_gridGraph c hN v]
  rcases Nat.eq_zero_or_pos v.2.val with h0 | hpos
  · have hN0 : 0 < N := by omega
    simp only [h0, hN0, true_and, lt_irrefl, false_and, ↓reduceIte, Nat.cast_zero, zero_sub,
      add_zero]
    exact bool_open _ _ _ _
  · have hne : v.2.val ≠ 0 := by omega
    simp only [hne, false_and, iff_false, hpos, true_and]
    by_cases hN' : v.2.val < N
    · simp only [hN', true_and]
      exact bool_cycle _ _ _ _
    · have hvN : v.2.val = N := by have := v.2.isLt; omega
      simp only [hvN, htop, lt_irrefl, false_and, ↓reduceIte, add_zero]
      exact bool_top _ _ _

/-- **Handshake on the cylinder grid.** If the top colour is constant and the bottom colour
changes exactly at the columns `i₀, i₁`, then the bottom vertices `(i₀, 0)` and
`(i₁, 0)` are joined in the colour-change graph. -/
theorem gridGraph_reachable (hN : 2 < N) (b₀ : Bool) (htop : ∀ i, c i (N : ℤ) = b₀)
    (i₀ i₁ : Fin N)
    (hbot : ∀ i, c (i - 1) (-1) ≠ c i (-1) ↔ (i = i₀ ∨ i = i₁)) :
    (gridGraph c).Reachable (i₀, 0) (i₁, 0) := by
  classical
  set G := gridGraph c with hG
  let S : Set (Fin N × Fin (N + 1)) := {w | G.Reachable (i₀, 0) w}
  have hS : ∀ u : S, G.neighborSet u ⊆ S := by
    intro u w hw
    exact u.2.trans (SimpleGraph.Adj.reachable hw)
  have hodd : ∀ u : S, Odd ((G.induce S).degree u) ↔ Odd (G.degree u) := by
    intro u
    rw [SimpleGraph.degree_induce_of_neighborSet_subset (hS u)]
  have hv₀ : Odd ((G.induce S).degree ⟨(i₀, 0), SimpleGraph.Reachable.refl _⟩) := by
    rw [hodd, odd_degree_gridGraph_iff c hN b₀ htop]
    exact ⟨rfl, (hbot i₀).2 (Or.inl rfl)⟩
  obtain ⟨w, hw, hwodd⟩ :=
    (G.induce S).exists_ne_odd_degree_of_exists_odd_degree _ hv₀
  rw [hodd, odd_degree_gridGraph_iff c hN b₀ htop] at hwodd
  have hw1 : (w : Fin N × Fin (N + 1)).1 = i₁ := by
    rcases (hbot _).1 hwodd.2 with h | h
    · exact absurd (Subtype.ext (Prod.ext h (Fin.ext hwodd.1))) hw
    · exact h
  have hw2 : (w : Fin N × Fin (N + 1)) = (i₁, 0) := Prod.ext hw1 (Fin.ext hwodd.1)
  have := w.2
  rw [hw2] at this
  exact this

end GridGraph

/-! ### Cells of the unit square, their colours and edge certificates -/

open Set unitInterval

/-- The point `1/2` of the unit interval. -/
def halfI : I := ⟨1 / 2, by norm_num, by norm_num⟩

/-- Clamp of a real number into the unit interval. -/
def clampI (x : ℝ) : I := Set.projIcc 0 1 zero_le_one x

lemma coe_clampI {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : (clampI x : ℝ) = x := by
  simp only [clampI, Set.projIcc_of_mem _ ⟨h0, h1⟩]

lemma continuous_clampI : Continuous clampI := continuous_projIcc (h := zero_le_one)

lemma clampI_coe (t : I) : clampI t = t := Subtype.ext (coe_clampI t.2.1 t.2.2)

lemma clampI_zero : clampI 0 = 0 := Subtype.ext (coe_clampI le_rfl zero_le_one)

lemma clampI_one : clampI 1 = 1 := Subtype.ext (coe_clampI zero_le_one le_rfl)

/-- The set `G₁` or `G₂` selected by a colour (`true ↦ G₁`, `false ↦ G₂`). -/
def colourSet {Y : Type*} (G₁ G₂ : Set Y) : Bool → Set Y
  | true => G₁
  | false => G₂

lemma mem_inter_of_colourSet {Y : Type*} {G₁ G₂ : Set Y} {b b' : Bool} (h : b ≠ b') {y : Y}
    (hb : y ∈ colourSet G₁ G₂ b) (hb' : y ∈ colourSet G₁ G₂ b') : y ∈ G₁ ∩ G₂ := by
  cases b <;> cases b' <;> simp_all [colourSet]

lemma isOpen_colourSet {Y : Type*} [TopologicalSpace Y] {G₁ G₂ : Set Y} (h₁ : IsOpen G₁)
    (h₂ : IsOpen G₂) (b : Bool) : IsOpen (colourSet G₁ G₂ b) := by
  cases b
  · exact h₂
  · exact h₁

/-- The closed grid cell `[i/N, (i+1)/N] × [max(j,0)/N, min(j+1,N)/N]` of the unit square; for
`j = -1` and `j = N` it degenerates to a bottom or a top edge. -/
def gridCell (N i : ℕ) (j : ℤ) : Set (I × I) :=
  {q | (i : ℝ) / N ≤ q.1 ∧ (q.1 : ℝ) ≤ ((i : ℝ) + 1) / N ∧
    ((max j 0 : ℤ) : ℝ) / N ≤ q.2 ∧ (q.2 : ℝ) ≤ ((min (j + 1) N : ℤ) : ℝ) / N}

section Colour

variable {Y : Type*} [TopologicalSpace Y]

open Classical in
/-- The colouring of the extended grid cells: virtual bottom cells (`j < 0`) are coloured `true`
(meaning `G₁`) on the left half `i < M` and `false` (meaning `G₂`) on the right half; virtual
top cells (`j ≥ N`) get the colour `b₀`; a real cell gets `true` iff `H` maps it into `G₁`. -/
noncomputable def gridColour (H : C(I × I, Y)) (G₁ : Set Y) (N M : ℕ) (b₀ : Bool) (i : ℕ)
    (j : ℤ) : Bool :=
  if j < 0 then decide (i < M) else if (N : ℤ) ≤ j then b₀ else
    decide (∀ q ∈ gridCell N i j, H q ∈ G₁)

variable {G₁ G₂ : Set Y} (H : C(I × I, Y)) {N M : ℕ} (b₀ : Bool)

/-- Each extended grid cell is mapped by `H` into the set selected by its colour. -/
lemma mem_colourSet_gridColour (hNM : N = 2 * M) (hM : 0 < M)
    (hL : ∀ s : I, (s : ℝ) ≤ 1 / 2 → H (s, 0) ∈ G₁)
    (hR : ∀ s : I, 1 / 2 ≤ (s : ℝ) → H (s, 0) ∈ G₂)
    (htop : ∀ s, H (s, 1) ∈ colourSet G₁ G₂ b₀)
    {δ : ℝ} (hδ : 1 / (N : ℝ) < δ)
    (hleb : ∀ q : I × I, ∃ b, Metric.ball q δ ⊆ H ⁻¹' colourSet G₁ G₂ b)
    {i : ℕ} (hi : i < N) {j : ℤ} (hj0 : -1 ≤ j) (hjN : j ≤ N) {q : I × I}
    (hq : q ∈ gridCell N i j) : H q ∈ colourSet G₁ G₂ (gridColour H G₁ N M b₀ i j) := by
  classical
  have hNpos : (0 : ℝ) < N := by rw [hNM]; push_cast; positivity
  obtain ⟨hq1, hq2, hq3, hq4⟩ := hq
  unfold gridColour
  split_ifs with hneg hNj
  · -- bottom virtual cell: `q.2 = 0`
    have hj : j = -1 := by omega
    subst hj
    have hq20 : (q.2 : ℝ) = 0 := by
      have : (q.2 : ℝ) ≤ 0 := by simpa using hq4
      exact le_antisymm this q.2.2.1
    have hq2' : q.2 = 0 := Subtype.ext hq20
    have hqe : q = (q.1, 0) := Prod.ext rfl hq2'
    rw [hqe]
    by_cases hiM : i < M
    · rw [decide_eq_true hiM]
      apply hL
      calc (q.1 : ℝ) ≤ ((i : ℝ) + 1) / N := hq2
        _ ≤ (M : ℝ) / N := by
          gcongr
          exact_mod_cast hiM
        _ = 1 / 2 := by rw [hNM]; push_cast; field_simp
    · rw [decide_eq_false hiM]
      apply hR
      calc (1 : ℝ) / 2 = (M : ℝ) / N := by rw [hNM]; push_cast; field_simp
        _ ≤ (i : ℝ) / N := by
          gcongr
          exact_mod_cast not_lt.1 hiM
        _ ≤ q.1 := hq1
  · -- top virtual cell: `q.2 = 1`
    have hj : j = N := le_antisymm hjN hNj
    subst hj
    have hq21 : (q.2 : ℝ) = 1 := by
      have h1 : (1 : ℝ) ≤ q.2 := by
        have : ((max (N : ℤ) 0 : ℤ) : ℝ) = N := by
          rw [max_eq_left (by positivity)]; push_cast; ring
        rw [this, div_self hNpos.ne'] at hq3
        exact hq3
      exact le_antisymm q.2.2.2 h1
    have hqe : q = (q.1, 1) := Prod.ext rfl (Subtype.ext hq21)
    rw [hqe]
    exact htop _
  · -- real cell
    have hj0' : 0 ≤ j := by omega
    have hjN' : j < N := by omega
    by_cases hall : ∀ q ∈ gridCell N i j, H q ∈ G₁
    · rw [decide_eq_true hall]
      exact hall q ⟨hq1, hq2, hq3, hq4⟩
    · rw [decide_eq_false hall]
      -- the cell lies in the `δ`-ball around its lower-left corner
      set q₀ : I × I := (clampI ((i : ℝ) / N), clampI ((j : ℝ) / N)) with hq₀
      obtain ⟨b, hb⟩ := hleb q₀
      have hi0 : (0 : ℝ) ≤ (i : ℝ) / N := by positivity
      have hi1 : (i : ℝ) / N ≤ 1 := by
        rw [div_le_one hNpos]; exact_mod_cast hi.le
      have hj0r : (0 : ℝ) ≤ (j : ℝ) / N := by
        have : (0 : ℝ) ≤ j := by exact_mod_cast hj0'
        positivity
      have hj1 : (j : ℝ) / N ≤ 1 := by
        rw [div_le_one hNpos]; exact_mod_cast hjN'.le
      have hmax : ((max j 0 : ℤ) : ℝ) = j := by rw [max_eq_left hj0']
      have hmin : ((min (j + 1) N : ℤ) : ℝ) = j + 1 := by
        rw [min_eq_left (by omega)]; push_cast; ring
      have hsub : gridCell N i j ⊆ Metric.ball q₀ δ := by
        rintro q' ⟨h1, h2, h3, h4⟩
        rw [hmax] at h3
        rw [hmin] at h4
        rw [Metric.mem_ball, Prod.dist_eq, max_lt_iff]
        have hNinv : (1 : ℝ) / N < δ := hδ
        constructor
        · rw [Subtype.dist_eq, hq₀, coe_clampI hi0 hi1, Real.dist_eq, abs_lt]
          constructor
          · have : (i : ℝ) / N ≤ q'.1 := h1
            linarith [div_pos one_pos hNpos]
          · have : (q'.1 : ℝ) ≤ (i : ℝ) / N + 1 / N := by rw [← add_div]; exact h2
            linarith
        · rw [Subtype.dist_eq, hq₀, coe_clampI hj0r hj1, Real.dist_eq, abs_lt]
          constructor
          · have : (j : ℝ) / N ≤ q'.2 := h3
            linarith [div_pos one_pos hNpos]
          · have : (q'.2 : ℝ) ≤ (j : ℝ) / N + 1 / N := by rw [← add_div]; exact h4
            linarith
      cases b with
      | true =>
        exact absurd (fun q' hq' => hb (hsub hq')) hall
      | false =>
        exact hb (hsub ⟨hq1, hq2, hq3, hq4⟩)

end Colour

section Edges

variable {Y : Type*} [TopologicalSpace Y] {G₁ G₂ : Set Y} (H : C(I × I, Y)) {N : ℕ}

/-- A point of `[i/N, (i+1)/N] × [j/N, (j+1)/N]`, `j < N`, lies in the real cell `(i, j)`. -/
lemma mem_gridCell_real {i : ℕ} {q : I × I} (h1 : (i : ℝ) / N ≤ q.1)
    (h2 : (q.1 : ℝ) ≤ ((i : ℝ) + 1) / N) {j : ℕ} (hj : j < N) (h3 : (j : ℝ) / N ≤ q.2)
    (h4 : (q.2 : ℝ) ≤ ((j : ℝ) + 1) / N) : q ∈ gridCell N i (j : ℤ) := by
  refine ⟨h1, h2, ?_, ?_⟩
  · rw [max_eq_left (by positivity)]
    push_cast
    exact h3
  · rw [min_eq_left (by omega)]
    push_cast
    exact h4

/-- A point of the horizontal grid edge at height `j/N`, `j ≤ N`, lies in the cells `(i, j)` and
`(i, j - 1)` (virtual for `j = 0` and `j = N`). -/
lemma mem_gridCell_row {i : ℕ} {q : I × I} (h1 : (i : ℝ) / N ≤ q.1)
    (h2 : (q.1 : ℝ) ≤ ((i : ℝ) + 1) / N) {j : ℕ} (hj : j ≤ N) (h3 : (q.2 : ℝ) = (j : ℝ) / N) :
    q ∈ gridCell N i (j : ℤ) ∧ q ∈ gridCell N i ((j : ℤ) - 1) := by
  have hN0 : (0 : ℝ) ≤ N := by positivity
  refine ⟨⟨h1, h2, ?_, ?_⟩, ⟨h1, h2, ?_, ?_⟩⟩
  · rw [max_eq_left (by positivity), h3]
    push_cast
    exact le_rfl
  · rw [h3]
    apply div_le_div_of_nonneg_right _ hN0
    have : (j : ℤ) ≤ min ((j : ℤ) + 1) N := le_min (by omega) (by exact_mod_cast hj)
    exact_mod_cast this
  · rw [h3]
    apply div_le_div_of_nonneg_right _ hN0
    have : (max ((j : ℤ) - 1) 0 : ℤ) ≤ j := max_le (by omega) (by omega)
    exact_mod_cast this
  · rw [h3, sub_add_cancel, min_eq_left (by exact_mod_cast hj)]
    push_cast
    exact le_rfl

variable (col : ℕ → ℤ → Bool)

/-- A horizontal grid edge whose two sides have different colours is mapped into `G₁ ∩ G₂`. -/
lemma joinedIn_hEdge (hN : 0 < N)
    (hcert : ∀ i < N, ∀ j : ℤ, -1 ≤ j → j ≤ N → ∀ q ∈ gridCell N i j,
      H q ∈ colourSet G₁ G₂ (col i j))
    {i : ℕ} (hi : i < N) {j : ℕ} (hj : j ≤ N) (hc : col i ((j : ℤ) - 1) ≠ col i j) :
    JoinedIn (G₁ ∩ G₂) (H (clampI ((i : ℝ) / N), clampI ((j : ℝ) / N)))
      (H (clampI (((i : ℝ) + 1) / N), clampI ((j : ℝ) / N))) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  refine JoinedIn.ofLine
    (f := fun τ : ℝ => H (clampI (((i : ℝ) + τ) / N), clampI ((j : ℝ) / N))) ?_ ?_ ?_ ?_
  · exact (H.continuous.comp ((continuous_clampI.comp
      ((continuous_const.add continuous_id).div_const _)).prodMk continuous_const)).continuousOn
  · simp only [add_zero]
  · simp only
  · rintro _ ⟨τ, hτ, rfl⟩
    have hτ0 : (0 : ℝ) ≤ τ := hτ.1
    have hτ1 : τ ≤ 1 := hτ.2
    have hiN : (i : ℝ) + 1 ≤ N := by exact_mod_cast hi
    have hjN : (j : ℝ) ≤ N := by exact_mod_cast hj
    have hx0 : (0 : ℝ) ≤ ((i : ℝ) + τ) / N := by positivity
    have hx1 : ((i : ℝ) + τ) / N ≤ 1 := by rw [div_le_one hNpos]; linarith
    have hy0 : (0 : ℝ) ≤ (j : ℝ) / N := by positivity
    have hy1 : (j : ℝ) / N ≤ 1 := by rw [div_le_one hNpos]; linarith
    have hrow := mem_gridCell_row (N := N) (i := i)
      (q := (clampI (((i : ℝ) + τ) / N), clampI ((j : ℝ) / N)))
      (by simp only [coe_clampI hx0 hx1]; gcongr; linarith)
      (by simp only [coe_clampI hx0 hx1]; gcongr)
      hj (by simp only [coe_clampI hy0 hy1])
    have hj1 : (-1 : ℤ) ≤ (j : ℤ) - 1 := by omega
    exact mem_inter_of_colourSet hc (hcert i hi _ hj1 (by omega) _ hrow.2)
      (hcert i hi _ (by omega) (by exact_mod_cast hj) _ hrow.1)

/-- A vertical grid edge whose two sides have different colours is mapped into `G₁ ∩ G₂`
(the left neighbour of column `0` is column `N - 1`, glued along `H (0, t) = H (1, t)`). -/
lemma joinedIn_vEdge (hN : 0 < N)
    (hcert : ∀ i < N, ∀ j : ℤ, -1 ≤ j → j ≤ N → ∀ q ∈ gridCell N i j,
      H q ∈ colourSet G₁ G₂ (col i j))
    (hside : ∀ t, H (0, t) = H (1, t))
    {i : ℕ} (hi : i < N) {j : ℕ} (hj : j < N)
    (hc : col (if i = 0 then N - 1 else i - 1) j ≠ col i j) :
    JoinedIn (G₁ ∩ G₂) (H (clampI ((i : ℝ) / N), clampI ((j : ℝ) / N)))
      (H (clampI ((i : ℝ) / N), clampI (((j : ℝ) + 1) / N))) := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  refine JoinedIn.ofLine
    (f := fun τ : ℝ => H (clampI ((i : ℝ) / N), clampI (((j : ℝ) + τ) / N))) ?_ ?_ ?_ ?_
  · exact (H.continuous.comp (continuous_const.prodMk (continuous_clampI.comp
      ((continuous_const.add continuous_id).div_const _)))).continuousOn
  · simp only [add_zero]
  · simp only
  · rintro _ ⟨τ, hτ, rfl⟩
    have hτ0 : (0 : ℝ) ≤ τ := hτ.1
    have hτ1 : τ ≤ 1 := hτ.2
    have hiN : (i : ℝ) + 1 ≤ N := by exact_mod_cast hi
    have hjN : (j : ℝ) + 1 ≤ N := by exact_mod_cast hj
    have hx0 : (0 : ℝ) ≤ (i : ℝ) / N := by positivity
    have hx1 : (i : ℝ) / N ≤ 1 := by rw [div_le_one hNpos]; linarith
    have hy0 : (0 : ℝ) ≤ ((j : ℝ) + τ) / N := by positivity
    have hy1 : ((j : ℝ) + τ) / N ≤ 1 := by rw [div_le_one hNpos]; linarith
    set t := clampI (((j : ℝ) + τ) / N) with ht
    have ht3 : (j : ℝ) / N ≤ t := by rw [ht, coe_clampI hy0 hy1]; gcongr; linarith
    have ht4 : (t : ℝ) ≤ ((j : ℝ) + 1) / N := by rw [ht, coe_clampI hy0 hy1]; gcongr
    have hright : H (clampI ((i : ℝ) / N), t) ∈ colourSet G₁ G₂ (col i j) :=
      hcert i hi _ (by omega) (by exact_mod_cast hj.le) _
        (mem_gridCell_real (by rw [coe_clampI hx0 hx1]) (by rw [coe_clampI hx0 hx1]; gcongr; linarith)
          hj ht3 ht4)
    have hleft : H (clampI ((i : ℝ) / N), t) ∈
        colourSet G₁ G₂ (col (if i = 0 then N - 1 else i - 1) j) := by
      by_cases hi0 : i = 0
      · subst hi0
        simp only [↓reduceIte, Nat.cast_zero, zero_div, clampI_zero]
        rw [hside t]
        have hN1 : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega)]; push_cast; ring
        refine hcert (N - 1) (by omega) _ (by omega) (by exact_mod_cast hj.le) _
          (mem_gridCell_real ?_ ?_ hj ht3 ht4)
        · rw [hN1]
          show ((N : ℝ) - 1) / N ≤ ((1 : I) : ℝ)
          rw [Set.Icc.coe_one, div_le_one hNpos]; linarith
        · rw [hN1]
          show ((1 : I) : ℝ) ≤ ((N : ℝ) - 1 + 1) / N
          rw [Set.Icc.coe_one, sub_add_cancel, div_self hNpos.ne']
      · simp only [hi0, ↓reduceIte]
        have hi1 : ((i - 1 : ℕ) : ℝ) = (i : ℝ) - 1 := by
          rw [Nat.cast_sub (by omega)]; push_cast; ring
        refine hcert (i - 1) (by omega) _ (by omega) (by exact_mod_cast hj.le) _
          (mem_gridCell_real ?_ ?_ hj ht3 ht4)
        · rw [hi1, coe_clampI hx0 hx1]; gcongr; linarith
        · rw [hi1, coe_clampI hx0 hx1, sub_add_cancel]
    have hne : col (if i = 0 then N - 1 else i - 1) j ≠ col i j := hc
    exact mem_inter_of_colourSet hne hleft hright

end Edges


/-! ### Assembly: NS-1 -/

section Assembly

/-- `i - 1` in `Fin N` (cyclic predecessor). -/
lemma fin_sub_one_val {N : ℕ} [NeZero N] (hN : 1 < N) (i : Fin N) :
    (i - 1).val = if i.val = 0 then N - 1 else i.val - 1 := by
  rw [Fin.sub_def]
  simp only
  rw [Fin.val_one', Nat.mod_eq_of_lt hN]
  split_ifs with h
  · rw [h, add_zero, Nat.mod_eq_of_lt (by omega)]
  · rw [show N - 1 + i.val = (i.val - 1) + N by omega, Nat.add_mod_right,
      Nat.mod_eq_of_lt (by omega)]

/-- `i + 1` in `Fin N` (cyclic successor). -/
lemma fin_add_one_val {N : ℕ} [NeZero N] (hN : 1 < N) (i : Fin N) :
    (i + 1).val = if i.val + 1 = N then 0 else i.val + 1 := by
  rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt hN]
  split_ifs with h
  · rw [h, Nat.mod_self]
  · exact Nat.mod_eq_of_lt (by omega)

lemma clampI_half : clampI (1 / 2) = halfI :=
  Subtype.ext (coe_clampI (by norm_num) (by norm_num))

/-- **NS-1 (handshake on a cylinder).** Let `G₁, G₂` be open in `Y` and `H : [0,1]² → G₁ ∪ G₂`
continuous with `H (0, t) = H (1, t)` (a cylinder), the top edge mapped into `G₁` (`b₀ = true`) or
into `G₂` (`b₀ = false`), and the bottom edge mapped into `G₁` on `[0, 1/2]` and into `G₂` on
`[1/2, 1]`. Then `H (1/2, 0)` and `H (0, 0)` are joined by a path in `G₁ ∩ G₂`. -/
theorem joinedIn_inter_of_cylinder {Y : Type*} [TopologicalSpace Y] {G₁ G₂ : Set Y}
    (h₁ : IsOpen G₁) (h₂ : IsOpen G₂) (H : C(I × I, Y)) (hH : ∀ q, H q ∈ G₁ ∪ G₂)
    (hside : ∀ t, H (0, t) = H (1, t)) (b₀ : Bool)
    (htop : ∀ s, H (s, 1) ∈ colourSet G₁ G₂ b₀)
    (hL : ∀ s : I, (s : ℝ) ≤ 1 / 2 → H (s, 0) ∈ G₁)
    (hR : ∀ s : I, 1 / 2 ≤ (s : ℝ) → H (s, 0) ∈ G₂) :
    JoinedIn (G₁ ∩ G₂) (H (halfI, 0)) (H (0, 0)) := by
  -- a Lebesgue number of the cover `{H⁻¹ G₁, H⁻¹ G₂}` of the compact square
  obtain ⟨δ, hδ, hleb⟩ := lebesgue_number_lemma_of_metric (s := (univ : Set (I × I)))
    (c := fun b => H ⁻¹' colourSet G₁ G₂ b) isCompact_univ
    (fun b => (isOpen_colourSet h₁ h₂ b).preimage H.continuous)
    (fun q _ => by
      rcases hH q with h | h
      · exact mem_iUnion.2 ⟨true, h⟩
      · exact mem_iUnion.2 ⟨false, h⟩)
  -- the mesh `1 / N`, `N = 2 M`, `M ≥ 2`
  obtain ⟨M₀, hM₀⟩ := exists_nat_gt (1 / δ)
  set M := M₀ + 2 with hM
  set N := 2 * M with hNM
  have : NeZero N := ⟨by omega⟩
  have hN : 2 < N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hδN : 1 / (N : ℝ) < δ := by
    rw [one_div_lt hNpos hδ]
    calc 1 / δ < M₀ := hM₀
      _ ≤ (N : ℝ) := by rw [hNM, hM]; push_cast; linarith
  have hcert : ∀ i < N, ∀ j : ℤ, -1 ≤ j → j ≤ N → ∀ q ∈ gridCell N i j,
      H q ∈ colourSet G₁ G₂ (gridColour H G₁ N M b₀ i j) :=
    fun i hi j hj0 hjN q hq => mem_colourSet_gridColour H b₀ hNM (by omega) hL hR htop hδN
      (fun q => hleb q (mem_univ q)) hi hj0 hjN hq
  -- the colour-change graph
  let c : Fin N → ℤ → Bool := fun i j => gridColour H G₁ N M b₀ i.val j
  let vpt : Fin N × Fin (N + 1) → I × I :=
    fun v => (clampI ((v.1.val : ℝ) / N), clampI ((v.2.val : ℝ) / N))
  have hwrap : ∀ (i : Fin N) (y : I),
      H (clampI (((i.val : ℝ) + 1) / N), y) = H (clampI (((i + 1 : Fin N).val : ℝ) / N), y) := by
    intro i y
    rw [fin_add_one_val (by omega) i]
    split_ifs with h
    · have : ((i.val : ℝ) + 1) = N := by exact_mod_cast h
      rw [this, div_self hNpos.ne', clampI_one, Nat.cast_zero, zero_div, clampI_zero, hside]
    · push_cast
      rfl
  have hhor : ∀ u w : Fin N × Fin (N + 1), GridH c u w →
      JoinedIn (G₁ ∩ G₂) (H (vpt u)) (H (vpt w)) := by
    rintro u w ⟨h2, h1, hc⟩
    have := joinedIn_hEdge H (fun i j => gridColour H G₁ N M b₀ i j) (by omega) hcert
      u.1.isLt (Nat.lt_succ_iff.1 u.2.isLt) hc
    rw [hwrap] at this
    simp only [vpt, h1, ← h2]
    exact this
  have hver : ∀ u w : Fin N × Fin (N + 1), GridV c u w →
      JoinedIn (G₁ ∩ G₂) (H (vpt u)) (H (vpt w)) := by
    rintro u w ⟨h1, h2, hc⟩
    have hj : u.2.val < N := by have := w.2.isLt; omega
    have hc' : gridColour H G₁ N M b₀ (if u.1.val = 0 then N - 1 else u.1.val - 1) u.2.val ≠
        gridColour H G₁ N M b₀ u.1.val u.2.val := by
      rw [← fin_sub_one_val (by omega) u.1]
      exact hc
    have := joinedIn_vEdge H (fun i j => gridColour H G₁ N M b₀ i j) (by omega) hcert hside
      u.1.isLt hj hc'
    have hw2 : ((w.2.val : ℕ) : ℝ) = (u.2.val : ℝ) + 1 := by exact_mod_cast h2
    simp only [vpt, ← h1, hw2]
    exact this
  have hadj : ∀ u w, (gridGraph c).Adj u w → JoinedIn (G₁ ∩ G₂) (H (vpt u)) (H (vpt w)) := by
    rintro u w ⟨-, h | h | h | h⟩
    · exact hhor u w h
    · exact (hhor w u h).symm
    · exact hver u w h
    · exact (hver w u h).symm
  -- the two odd vertices
  have hMN : M < N := by omega
  have htop' : ∀ i, c i (N : ℤ) = b₀ := by
    intro i
    simp only [c, gridColour, show ¬ ((N : ℤ) < 0) by omega, le_refl, ↓reduceIte]
  have hbot : ∀ i : Fin N, c (i - 1) (-1) ≠ c i (-1) ↔ (i = ⟨M, hMN⟩ ∨ i = 0) := by
    intro i
    simp only [c, gridColour, show (-1 : ℤ) < 0 by norm_num, ↓reduceIte]
    rw [fin_sub_one_val (by omega) i]
    constructor
    · intro h
      split_ifs at h with h0
      · exact Or.inr (Fin.ext h0)
      · left
        apply Fin.ext
        simp only
        by_contra hne
        apply h
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · simp only [show i.val - 1 < M by omega, hlt, decide_true]
        · simp only [show ¬ (i.val - 1 < M) by omega, show ¬ (i.val < M) by omega,
            decide_false]
    · rintro (h | h)
      · subst h
        simp only [show M ≠ 0 by omega, ↓reduceIte, show M - 1 < M by omega, lt_irrefl,
          decide_true, decide_false]
        decide
      · subst h
        simp only [Fin.val_zero, ↓reduceIte, show ¬ (N - 1 < M) by omega,
          show (0 : ℕ) < M by omega, decide_true, decide_false]
        decide
  have hreach : (gridGraph c).Reachable (⟨M, hMN⟩, 0) (0, 0) :=
    gridGraph_reachable c hN b₀ htop' ⟨M, hMN⟩ 0 hbot
  have hstart : H (vpt (⟨M, hMN⟩, 0)) = H (halfI, 0) := by
    have hM0 : (M : ℝ) ≠ 0 := by rw [hM]; positivity
    have : (M : ℝ) / N = 1 / 2 := by rw [hNM]; push_cast; field_simp
    simp only [vpt, this, Fin.val_zero, Nat.cast_zero, zero_div, clampI_zero, clampI_half]
  have hend : H (vpt (0, 0)) = H (0, 0) := by
    simp only [vpt, Fin.val_zero, Nat.cast_zero, zero_div, clampI_zero]
  have hmem : H (vpt (⟨M, hMN⟩, 0)) ∈ G₁ ∩ G₂ := by
    rw [hstart]
    exact ⟨hL halfI (by simp [halfI]), hR halfI (by simp [halfI])⟩
  have key : ∀ w, Relation.ReflTransGen (gridGraph c).Adj (⟨M, hMN⟩, 0) w →
      JoinedIn (G₁ ∩ G₂) (H (vpt (⟨M, hMN⟩, 0))) (H (vpt w)) := by
    intro w hw
    induction hw with
    | refl => exact JoinedIn.refl hmem
    | tail _ hab ih => exact ih.trans (hadj _ _ hab)
  have := key _ ((SimpleGraph.reachable_iff_reflTransGen _ _).1 hreach)
  rw [hstart, hend] at this
  exact this

/-- **NS-1**, in the shape of the MA1 probe `mvH0_cylinder` (top edge in `G₁`). -/
theorem mvH0_cylinder {Y : Type*} [TopologicalSpace Y] {G₁ G₂ : Set Y} (h₁ : IsOpen G₁)
    (h₂ : IsOpen G₂) (H : C(I × I, Y)) (hH : ∀ q, H q ∈ G₁ ∪ G₂)
    (hside : ∀ t, H (0, t) = H (1, t)) (htop : ∀ s, H (s, 1) ∈ G₁)
    (hL : ∀ s : I, (s : ℝ) ≤ 1 / 2 → H (s, 0) ∈ G₁)
    (hR : ∀ s : I, 1 / 2 ≤ (s : ℝ) → H (s, 0) ∈ G₂) :
    ∃ γ : Path (H (halfI, 0)) (H (0, 0)), ∀ t, γ t ∈ G₁ ∩ G₂ :=
  joinedIn_inter_of_cylinder h₁ h₂ H hH hside true htop hL hR

end Assembly

end HigherDimLQGMetric.Topology

end
