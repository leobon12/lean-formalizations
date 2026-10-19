import HigherDimLFPP.Upper.TreeJensen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Algebra.Order.Chebyshev

/-!
# Lemma 4.2: geometry of good nodes (`GoodNodeGeometry`) and the converse facts of HA3 D4

Source: `source/higher-dimensional-lfpp-limit.pdf`, §4.1, Lemma 4.2 and identity (4.8), with the
explicit constant `c₀ = 1/500` and the explicit good family `G_K` of HA3 D4 (fixes F2, F5;
`planning/audits/HA3-section-4.md`); ruling H7.

2D source: `LQGDimension/LFPP/RecordVarianceAux2.lean` (`forward_of_excess`, `excess_facts`, the
vertex estimates behind `coupled_poly`) and `LQGDimension/LFPP/RecordsAux1.lean`
(`edges_range_map`, `polyLen_range_map`, `sum_map_range_eq`), rewritten with inner products of
`Rd d` instead of `Complex.normSq`.  The exact count of `K` children of a good node is new
(HA3 D4: it follows from `R_u ≤ S_u < K r + r/4` and the chord bounds of the children).

* `goodNodeGeometry : GoodNodeGeometry d` — a node with `a_u ≤ 1/500/K` has exactly `K` children,
  and its child polygon lies in `G_K(x_u, y_u)` with threshold `a₀ = 1/500/K`.
* The converse facts for any polygon `z ∈ G_K(x, y)` given by its vertex list, with
  `a = log(len z/|y - x|)`: `goodFamily_vertex_close` (HA3 D4 (c), `|z_i - x - (i/K)(y-x)| ≤
  2 |y - x| √a`, for `a₀ ≤ 1`) and `goodFamily_lastEdge` (D4 (d), last edge `≥ |y - x|/K`).
  The growth and coupling facts D4 (a), (b) are in `HigherDimLFPP.Upper.PolygonMeasure`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped RealInnerProductSpace

namespace HigherDimLFPP.Upper

/-! ## Polygons given by vertex lists and vertex functions -/

section Lists

variable {d : ℕ}

theorem sum_map_range_eq {β : Type*} [AddCommMonoid β] (g : ℕ → β) (m : ℕ) :
    ((List.range m).map g).sum = ∑ i ∈ Finset.range m, g i := by
  induction m with
  | zero => simp
  | succ m ih => simp [List.range_succ, Finset.sum_range_succ, ih]

theorem edges_range_map (f : ℕ → Rd d) (m : ℕ) :
    edges ((List.range (m + 1)).map f) = (List.range m).map (fun i => (f i, f (i + 1))) := by
  unfold edges
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getElem_zip, List.getElem_tail]

theorem polyLen_range_map (f : ℕ → Rd d) (m : ℕ) :
    polyLen ((List.range (m + 1)).map f) = ∑ i ∈ Finset.range m, ‖f (i + 1) - f i‖ := by
  rw [polyLen, edges_range_map, List.map_map, sum_map_range_eq]
  rfl

/-- A vertex list of length `m + 1` is the image of `range (m + 1)` under its vertex function. -/
theorem eq_range_map_getD {z : List (Rd d)} {m : ℕ} (hz : z.length = m + 1) :
    z = (List.range (m + 1)).map (fun i => z.getD i 0) := by
  apply List.ext_getElem
  · simp [hz]
  · intro i h1 h2
    simp [List.getD_eq_getElem?_getD, h1]

theorem head?_range_map (f : ℕ → Rd d) (m : ℕ) :
    ((List.range (m + 1)).map f).head? = some (f 0) := by
  simp [List.head?_range]

theorem getLast?_range_map (f : ℕ → Rd d) (m : ℕ) :
    ((List.range (m + 1)).map f).getLast? = some (f m) := by
  simp [List.getLast?_range]

/-- The edges of `(range (m + 1)).map f` but the last are the first `m - 1` edges. -/
theorem mem_dropLast_edges {f : ℕ → Rd d} {m : ℕ} {e : Rd d × Rd d}
    (he : e ∈ (edges ((List.range (m + 1)).map f)).dropLast) :
    ∃ i, i + 1 < m ∧ e = (f i, f (i + 1)) := by
  rw [edges_range_map] at he
  rcases m with _ | m
  · simp at he
  · rw [List.range_succ, List.map_append, List.map_singleton, List.dropLast_concat] at he
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 he
    exact ⟨i, by simpa using hi, rfl⟩

/-- The last edge of `(range (m + 1)).map f`, `m ≥ 1`. -/
theorem getLast?_edges {f : ℕ → Rd d} {m : ℕ} (hm : 1 ≤ m) :
    (edges ((List.range (m + 1)).map f)).getLast? = some (f (m - 1), f m) := by
  rw [edges_range_map]
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  rw [List.range_succ, List.map_append, List.map_singleton, List.getLast?_concat]
  simp

end Lists

section Polygon

variable {d : ℕ}

/-- The length `Σ_{j<m} |V (j+1) - V j|` of the polygon with vertices `V 0, …, V m`. -/
def plen (V : ℕ → Rd d) (m : ℕ) : ℝ := ∑ j ∈ Finset.range m, ‖V (j + 1) - V j‖

theorem norm_sub_le_plen (V : ℕ → Rd d) (m : ℕ) : ‖V m - V 0‖ ≤ plen V m := by
  rw [← Finset.sum_range_sub V m]
  exact norm_sum_le _ _

/-- The excess term `ℓ_j R - ⟨D_j, v⟩` of edge `j` (`D_j = V (j+1) - V j`, `v = V m - V 0`,
`ℓ_j = |D_j|`, `R = |v|`); `ℓ_j |t_j - e|² = 2 (ℓ_j R - ⟨D_j, v⟩)/R` in the notation of (4.8). -/
def exTerm (V : ℕ → Rd d) (m j : ℕ) : ℝ :=
  ‖V (j + 1) - V j‖ * ‖V m - V 0‖ - ⟪V (j + 1) - V j, V m - V 0⟫

theorem exTerm_nonneg (V : ℕ → Rd d) (m j : ℕ) : 0 ≤ exTerm V m j :=
  sub_nonneg.2 (real_inner_le_norm _ _)

/-- **Identity (4.8)**, unnormalized: `Σ_j (ℓ_j R - ⟨D_j, v⟩) = R (S - R)`. -/
theorem sum_exTerm (V : ℕ → Rd d) (m : ℕ) :
    ∑ j ∈ Finset.range m, exTerm V m j = ‖V m - V 0‖ * (plen V m - ‖V m - V 0‖) := by
  unfold exTerm plen
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, ← sum_inner, Finset.sum_range_sub V m,
    real_inner_self_eq_norm_sq]
  ring

theorem exTerm_le (V : ℕ → Rd d) {m i : ℕ} (hi : i < m) :
    exTerm V m i ≤ ‖V m - V 0‖ * (plen V m - ‖V m - V 0‖) := by
  rw [← sum_exTerm]
  exact Finset.single_le_sum (fun j _ => exTerm_nonneg V m j) (Finset.mem_range.2 hi)

/-- **Forward edges** (proof of Lemma 4.2): if the excess `S - R` is at most `(1 - c)` times
every edge length, every edge makes `⟨D_i, v⟩ ≥ c ℓ_i R`. -/
theorem forward_of_excess {V : ℕ → Rd d} {m : ℕ} {c : ℝ}
    (h : ∀ i < m, plen V m - ‖V m - V 0‖ ≤ (1 - c) * ‖V (i + 1) - V i‖) :
    ∀ i < m, c * ‖V (i + 1) - V i‖ * ‖V m - V 0‖ ≤ ⟪V (i + 1) - V i, V m - V 0⟫ := by
  intro i hi
  have h1 := exTerm_le V hi
  have h2 := mul_le_mul_of_nonneg_left (h i hi) (norm_nonneg (V m - V 0))
  unfold exTerm at h1
  nlinarith

end Polygon

/-! ## Numerical constants -/

/-- `cos (1/10) ≤ 1 - 49/10000`. -/
theorem cos_tenth_le : Real.cos (1 / 10) ≤ 1 - 49 / 10000 := by
  have h := Real.cos_bound (x := 1 / 10) (by rw [abs_of_pos (by norm_num)]; norm_num)
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 10)] at h
  have h' := (abs_le.1 h).2
  norm_num at h'
  linarith

/-- `cos (1/10) ≥ 2/3`. -/
theorem two_thirds_le_cos_tenth : 2 / 3 ≤ Real.cos (1 / 10) := by
  have := Real.one_sub_sq_div_two_le_cos (x := 1 / 10)
  norm_num at this
  linarith

/-- `e^x ≤ 1 + x + x²` for `0 ≤ x ≤ 1`. -/
theorem exp_le_one_add_add_sq {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Real.exp x ≤ 1 + x + x ^ 2 := by
  have h := Real.abs_exp_sub_one_sub_id_le (x := x) (by rw [abs_of_nonneg h0]; exact h1)
  have := (abs_le.1 h).2
  linarith

/-- `e^a - 1 ≤ 2 a` for `0 ≤ a ≤ 1`. -/
theorem exp_sub_one_le_two_mul {a : ℝ} (h0 : 0 ≤ a) (h1 : a ≤ 1) : Real.exp a - 1 ≤ 2 * a := by
  have := exp_le_one_add_add_sq h0 h1
  nlinarith

/-! ## Lemma 4.2: good nodes -/

section GoodNode

variable {d : ℕ} {T : CutTree} {γ : ℝ → Rd d} {K : ℕ} {ε ρ₀ : ℝ}

open TreeJensen

/-- The child polygon in vertex-function form: `Q_u = (γ(τ_0), …, γ(τ_p))` with the child times
`τ_i = ctime u i`. -/
theorem childPoly_eq (u : List ℕ) :
    T.childPoly γ u = (List.range (T.nch u + 1)).map (fun i => γ (ctime T u i)) := by
  rw [CutTree.childPoly, List.range_succ, List.map_append, List.map_singleton, ctime_nch]
  congr 1
  refine List.map_congr_left fun i hi => ?_
  rw [CutTree.x, t₀_child (List.mem_range.1 hi)]

/-- The edge vectors of the child polygon are the child chords. -/
theorem ctime_edge (hT : T.WF γ K ε ρ₀) {u : List ℕ} (hu : u ∈ T.nodes) {i : ℕ}
    (hi : i < T.nch u) :
    γ (ctime T u (i + 1)) - γ (ctime T u i) = T.y γ (u ++ [i]) - T.x γ (u ++ [i]) := by
  rw [CutTree.x, CutTree.y, t₀_child hi, t₁_child hT hu hi]

theorem ctime_edge_norm (hT : T.WF γ K ε ρ₀) {u : List ℕ} (hu : u ∈ T.nodes) {i : ℕ}
    (hi : i < T.nch u) : ‖γ (ctime T u (i + 1)) - γ (ctime T u i)‖ = T.R γ (u ++ [i]) := by
  rw [ctime_edge hT hu hi]; rfl

theorem plen_ctime (hT : T.WF γ K ε ρ₀) {u : List ℕ} (hu : u ∈ T.nodes) :
    plen (fun i => γ (ctime T u i)) (T.nch u) = T.S γ u :=
  Finset.sum_congr rfl fun _ hi => ctime_edge_norm hT hu (Finset.mem_range.1 hi)

theorem ctime_chord (hT : T.WF γ K ε ρ₀) {u : List ℕ} (hu : u ∈ T.nodes) (hn : 0 < T.nch u) :
    γ (ctime T u (T.nch u)) - γ (ctime T u 0) = T.y γ u - T.x γ u := by
  rw [ctime_nch, ctime_zero hT hu hn]; rfl

/-- **Exact count** (HA3 D4, good node, steps 2–5): an internal node with
`a_u ≤ 1/500/K` has exactly `K` children; moreover `S_u - R_u ≤ (x + x²) R_u` with
`x = 1/500/K`. -/
theorem goodNode_count (hT : T.WF γ K ε ρ₀) (hK : 1 ≤ K) (hε : 0 < ε) {u : List ℕ}
    (hu : u ∈ T.nodes) (hn : 0 < T.nch u) (hA : T.A γ u ≤ 1 / 500 / K) :
    T.nch u = K ∧
      T.S γ u - T.R γ u ≤ (1 / 500 / K + (1 / 500 / K) ^ 2) * T.R γ u := by
  set R := T.R γ u with hRdef
  set S := T.S γ u with hSdef
  set x0 : ℝ := 1 / 500 / K with hx0
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := by linarith
  have hR : 0 < R := hε.trans ((hT.internal_iff u hu).1 hn)
  have hRS : R ≤ S := R_le_S hT hu hn
  have hS : 0 < S := hR.trans_le hRS
  have hx0pos : 0 < x0 := by positivity
  have hx0le : x0 ≤ 1 / 500 := by
    rw [hx0, div_le_div_iff₀ hKpos (by norm_num)]; linarith
  have hKx0 : (K : ℝ) * x0 = 1 / 500 := by rw [hx0]; field_simp
  -- `S ≤ e^{x0} R ≤ (1 + x0 + x0²) R`
  have hSR : S / R ≤ Real.exp x0 := (Real.log_le_iff_le_exp (div_pos hS hR)).1 hA
  have hexp := exp_le_one_add_add_sq hx0pos.le (by linarith)
  have hSle : S ≤ (1 + x0 + x0 ^ 2) * R := by
    rw [div_le_iff₀ hR] at hSR
    nlinarith
  refine ⟨?_, by nlinarith⟩
  -- the chord sum of the children
  set p := T.nch u with hpdef
  set r := R / K with hrdef
  have hr : 0 < r := div_pos hR hKpos
  have hRr : R = K * r := by rw [hrdef]; field_simp
  obtain ⟨q, hq⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
  have hreg : ∀ i ∈ Finset.range q, T.R γ (u ++ [i]) = r := fun i hi =>
    hT.regular u hu i (by rw [Finset.mem_range] at hi; omega)
  have hlast := hT.scale u hu q (by omega)
  have hSsum : S = q * r + T.R γ (u ++ [q]) := by
    rw [hSdef, CutTree.S, ← hpdef, hq, Finset.sum_range_succ, Finset.sum_congr rfl hreg,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hl1 : r / 2 ≤ T.R γ (u ++ [q]) := by
    have := hlast.1; rw [← hRdef] at this
    calc r / 2 = R / (2 * K) := by rw [hrdef]; ring
      _ ≤ _ := this
  have hl2 : T.R γ (u ++ [q]) ≤ 3 * r / 2 := by
    have := hlast.2; rw [← hRdef] at this
    calc T.R γ (u ++ [q]) ≤ 3 * R / (2 * K) := this
      _ = 3 * r / 2 := by rw [hrdef]; ring
  -- `p ≤ K`
  have hup : ((q : ℝ) + 1/2) * r ≤ (K + 1 / 500 + x0 / 500) * r := by
    have e : (1 + x0 + x0 ^ 2) * R = (K + 1 / 500 + x0 / 500) * r := by
      rw [hRr]
      have : (K : ℝ) * x0 ^ 2 = x0 / 500 := by rw [sq, ← mul_assoc, hKx0]; ring
      linear_combination r * hKx0 + r * this
    nlinarith
  have hup' : (q : ℝ) + 1 / 2 ≤ K + 1 / 500 + x0 / 500 := le_of_mul_le_mul_right hup hr
  -- `K ≤ p`
  have hlow : (K : ℝ) * r ≤ ((q : ℝ) + 3 / 2) * r := by nlinarith
  have hlow' : (K : ℝ) ≤ (q : ℝ) + 3 / 2 := le_of_mul_le_mul_right hlow hr
  have h1 : (q : ℝ) < K := by linarith
  have h2 : (K : ℝ) < (q : ℝ) + 2 := by linarith
  have h1' : q < K := by exact_mod_cast h1
  have h2' : K < q + 2 := by exact_mod_cast h2
  omega

/-- **Lemma 4.2** for a well-formed tree (HA3 D4, good node), in the generic form: an internal node
with `a_u ≤ 1/500/K` has exactly `K` children and its child polygon lies in
`G_K(x_u, y_u)` with threshold `1/500/K`. -/
theorem goodNode_of_wf (hT : T.WF γ K ε ρ₀) (hK : 1 ≤ K) (hε : 0 < ε) {u : List ℕ}
    (hu : u ∈ T.nodes) (hn : 0 < T.nch u) (hA : T.A γ u ≤ 1 / 500 / K) :
    T.nch u = K ∧ T.childPoly γ u ∈ goodFamily K (1 / 500 / K) (T.x γ u) (T.y γ u) := by
  obtain ⟨hp, hexc⟩ := goodNode_count hT hK hε hu hn hA
  refine ⟨hp, ?_⟩
  set V : ℕ → Rd d := fun i => γ (ctime T u i) with hV
  set R := T.R γ u with hRdef
  set x0 : ℝ := 1 / 500 / K with hx0
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := by linarith
  have hR : 0 < R := hε.trans ((hT.internal_iff u hu).1 hn)
  have hx0pos : 0 < x0 := by positivity
  have hx0le : x0 ≤ 1 / 500 := by
    rw [hx0, div_le_div_iff₀ hKpos (by norm_num)]; linarith
  have hKx0 : (K : ℝ) * x0 = 1 / 500 := by rw [hx0]; field_simp
  have hz : T.childPoly γ u = (List.range (K + 1)).map V := by
    rw [childPoly_eq u, hp]
  have hV0 : V 0 = T.x γ u := by simp only [hV]; rw [ctime_zero hT hu hn]; rfl
  have hVK : V K = T.y γ u := by simp only [hV]; rw [← hp, ctime_nch]; rfl
  have hchord : V K - V 0 = T.y γ u - T.x γ u := by rw [hV0, hVK]
  have hedge : ∀ i < K, ‖V (i + 1) - V i‖ = T.R γ (u ++ [i]) := fun i hi =>
    ctime_edge_norm hT hu (by omega)
  have hplen : plen V K = T.S γ u := by
    have := plen_ctime hT hu; rw [hp] at this; exact this
  -- forward edges, with `c = cos (1/10)`
  have hfwd : ∀ i < K, Real.cos (1 / 10) * ‖V (i + 1) - V i‖ * ‖V K - V 0‖ ≤
      ⟪V (i + 1) - V i, V K - V 0⟫ := by
    refine forward_of_excess fun i hi => ?_
    rw [hplen, hchord]
    have hsc := (hT.scale u hu i (by omega)).1
    rw [← hRdef] at hsc
    have hcos := cos_tenth_le
    have hK2 : (K : ℝ) * (x0 + x0 ^ 2) ≤ 49 / 20000 := by
      have : (K : ℝ) * x0 ^ 2 = x0 / 500 := by rw [sq, ← mul_assoc, hKx0]; ring
      nlinarith
    -- `S - R ≤ (x0 + x0²) R ≤ (49/10000) R/(2K) ≤ (1 - cos) ℓ_i`
    have e1 : (x0 + x0 ^ 2) * R ≤ 49 / 10000 * (R / (2 * K)) := by
      rw [show 49 / 10000 * (R / (2 * K)) = 49 / 20000 / K * R by ring]
      refine mul_le_mul_of_nonneg_right ?_ hR.le
      rw [le_div_iff₀ hKpos]; linarith
    have e2 : 49 / 10000 * (R / (2 * K)) ≤ (1 - Real.cos (1 / 10)) * T.R γ (u ++ [i]) := by
      have h0 : 0 ≤ R / (2 * K) := by positivity
      have := mul_le_mul_of_nonneg_left hsc (show (0 : ℝ) ≤ 49 / 10000 by norm_num)
      nlinarith
    rw [hedge i hi]
    change T.S γ u - R ≤ _
    linarith
  rw [hz]
  refine ⟨by simp, by rw [head?_range_map, hV0], by rw [getLast?_range_map, hVK], ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨i, hi, rfl⟩ := mem_dropLast_edges he
    show ‖V (i + 1) - V i‖ = ‖T.y γ u - T.x γ u‖ / K
    rw [hedge i (by omega)]
    exact hT.regular u hu i (by omega)
  · intro e he
    rw [edges_range_map] at he
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 he
    rw [← hchord]
    exact hfwd i (List.mem_range.1 hi)
  · rw [polyLen_range_map]
    change plen V K ≤ _
    rw [hplen]
    have hSR : T.S γ u / R ≤ Real.exp x0 := (Real.log_le_iff_le_exp
      (div_pos (hR.trans_le (R_le_S hT hu hn)) hR)).1 hA
    rw [div_le_iff₀ hR] at hSR
    exact hSR

end GoodNode

/-- **Lemma 4.2** with `c₀ = 1/500` (HA3 D4, F5): a good node has exactly `K` children and its
child polygon lies in the explicit good family `G_K` with threshold `a₀ = c₀ / K`. -/
theorem goodNodeGeometry (d : ℕ) [NeZero d] : GoodNodeGeometry d := by
  intro γ _hγ K hK ε hε T hT u hu hn hA
  exact goodNode_of_wf hT (by omega) hε.1 hu hn hA

/-! ## Converse facts for polygons in `G_K` (HA3 D4 (c), (d)) -/

section Converse

variable {d : ℕ} {K : ℕ} {a₀ : ℝ} {x y : Rd d} {z : List (Rd d)}

/-- The defining properties of `G_K(x, y)` for a polygon given by a vertex function. -/
theorem goodFamily_map_props {V : ℕ → Rd d}
    (hz : (List.range (K + 1)).map V ∈ goodFamily K a₀ x y) :
    V 0 = x ∧ V K = y ∧ (∀ i, i + 1 < K → ‖V (i + 1) - V i‖ = ‖y - x‖ / K) ∧
      (∀ i < K, Real.cos (1 / 10) * ‖V (i + 1) - V i‖ * ‖y - x‖ ≤ ⟪V (i + 1) - V i, y - x⟫) ∧
      plen V K ≤ Real.exp a₀ * ‖y - x‖ := by
  obtain ⟨-, hhead, hlast, hdrop, hfwd, hpoly⟩ := hz
  rw [head?_range_map] at hhead
  rw [getLast?_range_map] at hlast
  refine ⟨Option.some.inj hhead, Option.some.inj hlast, ?_, ?_, ?_⟩
  · intro i hi
    have hmem : (V i, V (i + 1)) ∈ (edges ((List.range (K + 1)).map V)).dropLast := by
      rw [edges_range_map]
      obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
      rw [List.range_succ, List.map_append, List.map_singleton, List.dropLast_concat]
      exact List.mem_map.2 ⟨i, List.mem_range.2 (by omega), rfl⟩
    exact hdrop (V i, V (i + 1)) hmem
  · intro i hi
    have hmem : (V i, V (i + 1)) ∈ edges ((List.range (K + 1)).map V) := by
      rw [edges_range_map]
      exact List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩
    exact hfwd (V i, V (i + 1)) hmem
  · rw [polyLen_range_map] at hpoly
    exact hpoly

/-- The vertex function of a polygon in `G_K(x, y)` and the defining properties of `G_K` in
vertex-function form. -/
theorem goodFamily_vertex (hz : z ∈ goodFamily K a₀ x y) :
    ∃ V : ℕ → Rd d, z = (List.range (K + 1)).map V ∧ V 0 = x ∧ V K = y ∧
      (∀ i, i + 1 < K → ‖V (i + 1) - V i‖ = ‖y - x‖ / K) ∧
      (∀ i < K, Real.cos (1 / 10) * ‖V (i + 1) - V i‖ * ‖y - x‖ ≤ ⟪V (i + 1) - V i, y - x⟫) ∧
      plen V K ≤ Real.exp a₀ * ‖y - x‖ := by
  have hzV := eq_range_map_getD hz.1
  rw [hzV] at hz
  exact ⟨_, hzV, goodFamily_map_props hz⟩

/-- **HA3 D4 (d)**: the last edge of a polygon in `G_K(x, y)`, `x ≠ y`, has length at least
`|y - x| / K`. -/
theorem goodFamily_lastEdge (hz : z ∈ goodFamily K a₀ x y) (hxy : x ≠ y) :
    ∀ e ∈ (edges z).getLast?, ‖y - x‖ / K ≤ ‖e.2 - e.1‖ := by
  obtain ⟨V, hzV, hV0, hVK, hreg, -, -⟩ := goodFamily_vertex hz
  set v := y - x with hv
  have hR : 0 < ‖v‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hxy))
  have hK : 1 ≤ K := by
    by_contra h
    have hK0 : K = 0 := by omega
    rw [hK0] at hVK
    exact hxy (hV0.symm.trans hVK)
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  intro e he
  rw [hzV, getLast?_edges hK] at he
  obtain rfl := Option.some.inj he.symm
  show ‖v‖ / K ≤ ‖V K - V (K - 1)‖
  obtain ⟨k, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  -- `⟨D_k, v⟩ = |v|² - Σ_{i<k} ⟨D_i, v⟩ ≥ |v|² - k |v|²/(k+1)`
  have hsum : ∑ i ∈ Finset.range (k + 1), (V (i + 1) - V i) = v := by
    rw [Finset.sum_range_sub V (k + 1), hV0, hVK]
  have hinner : ∑ i ∈ Finset.range (k + 1), ⟪V (i + 1) - V i, v⟫ = ‖v‖ ^ 2 := by
    rw [← sum_inner, hsum, real_inner_self_eq_norm_sq]
  rw [Finset.sum_range_succ] at hinner
  have hfirst : ∑ i ∈ Finset.range k, ⟪V (i + 1) - V i, v⟫ ≤ k * (‖v‖ / (k + 1 : ℕ) * ‖v‖) := by
    calc ∑ i ∈ Finset.range k, ⟪V (i + 1) - V i, v⟫
        ≤ ∑ _i ∈ Finset.range k, ‖v‖ / (k + 1 : ℕ) * ‖v‖ := by
          refine Finset.sum_le_sum fun i hi => ?_
          have := hreg i (by rw [Finset.mem_range] at hi; omega)
          rw [← this]
          exact real_inner_le_norm _ _
      _ = k * (‖v‖ / (k + 1 : ℕ) * ‖v‖) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hlast := real_inner_le_norm (V (k + 1) - V k) v
  have hk1 : ((k + 1 : ℕ) : ℝ) = k + 1 := by push_cast; ring
  rw [hk1] at hfirst ⊢
  rw [div_le_iff₀ (by positivity)]
  have hkey : ‖v‖ ^ 2 / (k + 1) ≤ ‖V (k + 1) - V k‖ * ‖v‖ := by
    have e : ‖v‖ ^ 2 / (k + 1) = ‖v‖ ^ 2 - k * (‖v‖ / (k + 1) * ‖v‖) := by
      field_simp; ring
    rw [e]; linarith
  have : ‖v‖ * ‖v‖ ≤ ‖V (k + 1) - V k‖ * (k + 1) * ‖v‖ := by
    have h2 := mul_le_mul_of_nonneg_left hkey (show (0 : ℝ) ≤ k + 1 by positivity)
    rw [mul_div_cancel₀ _ (by positivity : (k : ℝ) + 1 ≠ 0)] at h2
    nlinarith
  exact le_of_mul_le_mul_right (by linarith) hR

/-- The squared vertex estimate behind HA3 D4 (c): for a polygon whose first `K - 1` edges have
length `|y - x| / K`, `|V i - x - (i/K)(y - x)|² ≤ 2 R (S - R)` (Cauchy–Schwarz and (4.8)). -/
theorem vertex_close_sq {V : ℕ → Rd d} (hK : 1 ≤ K) (hV0 : V 0 = x) (hVK : V K = y)
    (hreg : ∀ i, i + 1 < K → ‖V (i + 1) - V i‖ = ‖y - x‖ / K) {i : ℕ} (hiK : i ≤ K) :
    ‖V i - x - ((i : ℝ) / K) • (y - x)‖ ^ 2 ≤
      2 * ‖y - x‖ * (plen V K - ‖y - x‖) := by
  have hKpos : (0 : ℝ) < K := by exact_mod_cast hK
  have hchord : V K - V 0 = y - x := by rw [hV0, hVK]
  have hRS : ‖y - x‖ ≤ plen V K := by rw [← hchord]; exact norm_sub_le_plen V K
  have hex0 : 0 ≤ ‖y - x‖ * (plen V K - ‖y - x‖) :=
    mul_nonneg (norm_nonneg _) (by linarith)
  rcases eq_or_lt_of_le hiK with rfl | hiK'
  · rw [hVK, div_self hKpos.ne', one_smul, sub_self, norm_zero]
    have := mul_nonneg (zero_le_two : (0 : ℝ) ≤ 2) hex0
    rw [mul_assoc]
    simpa using this
  · -- `V i - x - (i/K) v = Σ_{l<i} w l` with `w l = D_l - v/K`
    have hdecomp : V i - x - ((i : ℝ) / K) • (y - x) =
        ∑ l ∈ Finset.range i, ((V (l + 1) - V l) - (1 / (K : ℝ)) • (y - x)) := by
      rw [Finset.sum_sub_distrib, Finset.sum_range_sub V i, hV0, Finset.sum_const,
        Finset.card_range, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul]
      congr 2
      ring
    -- each `|w l|² = (2/K) exTerm`
    have hwl : ∀ l < i, ‖(V (l + 1) - V l) - (1 / (K : ℝ)) • (y - x)‖ ^ 2 =
        (2 / K) * exTerm V K l := by
      intro l hl
      have hℓ : ‖V (l + 1) - V l‖ = ‖y - x‖ / K := hreg l (by omega)
      unfold exTerm
      rw [@norm_sub_sq_real, norm_smul, inner_smul_right, hℓ, hchord, Real.norm_eq_abs,
        abs_of_pos (by positivity : (0 : ℝ) < 1 / K)]
      ring
    have hsumw : ∑ l ∈ Finset.range i, ‖(V (l + 1) - V l) - (1 / (K : ℝ)) • (y - x)‖ ^ 2 ≤
        (2 / K) * (‖y - x‖ * (plen V K - ‖y - x‖)) := by
      rw [Finset.sum_congr rfl fun l hl => hwl l (Finset.mem_range.1 hl), ← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      calc ∑ l ∈ Finset.range i, exTerm V K l ≤ ∑ l ∈ Finset.range K, exTerm V K l :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.2 hiK)
              fun l _ _ => exTerm_nonneg V K l
        _ = ‖y - x‖ * (plen V K - ‖y - x‖) := by rw [sum_exTerm, hchord]
    have hCS : ‖∑ l ∈ Finset.range i, ((V (l + 1) - V l) - (1 / (K : ℝ)) • (y - x))‖ ^ 2 ≤
        i * ∑ l ∈ Finset.range i, ‖(V (l + 1) - V l) - (1 / (K : ℝ)) • (y - x)‖ ^ 2 := by
      calc _ ≤ (∑ l ∈ Finset.range i, ‖(V (l + 1) - V l) - (1 / (K : ℝ)) • (y - x)‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
        _ ≤ (Finset.range i).card *
              ∑ l ∈ Finset.range i, ‖(V (l + 1) - V l) - (1 / (K : ℝ)) • (y - x)‖ ^ 2 :=
            sq_sum_le_card_mul_sum_sq
        _ = _ := by rw [Finset.card_range]
    have hi' : (i : ℝ) ≤ K := by exact_mod_cast hiK
    rw [hdecomp]
    refine hCS.trans ?_
    calc (i : ℝ) * ∑ l ∈ Finset.range i,
          ‖(V (l + 1) - V l) - (1 / (K : ℝ)) • (y - x)‖ ^ 2
        ≤ K * ((2 / K) * (‖y - x‖ * (plen V K - ‖y - x‖))) :=
          mul_le_mul hi' hsumw (Finset.sum_nonneg fun l _ => sq_nonneg _) hKpos.le
      _ = 2 * ‖y - x‖ * (plen V K - ‖y - x‖) := by
          rw [← mul_assoc, mul_div_cancel₀ _ hKpos.ne', mul_assoc]

/-- **HA3 D4 (c)**: vertex closeness.  For a polygon `z ∈ G_K(x, y)` with threshold `a₀ ≤ 1`
and `x ≠ y`, every vertex satisfies `|z_i - x - (i/K)(y - x)| ≤ 2 |y - x| √a`, where
`a = log(len z / |y - x|)` is its log excess. -/
theorem goodFamily_vertex_close (hz : z ∈ goodFamily K a₀ x y) (hxy : x ≠ y) (ha₀ : a₀ ≤ 1) :
    ∀ i (hi : i < z.length), ‖z[i] - x - ((i : ℝ) / K) • (y - x)‖ ≤
      2 * ‖y - x‖ * Real.sqrt (Real.log (polyLen z / ‖y - x‖)) := by
  obtain ⟨V, hzV, hV0, hVK, hreg, -, hpoly⟩ := goodFamily_vertex hz
  have hR : 0 < ‖y - x‖ := norm_pos_iff.2 (sub_ne_zero.2 (Ne.symm hxy))
  have hK : 1 ≤ K := by
    by_contra h
    have hK0 : K = 0 := by omega
    rw [hK0] at hVK
    exact hxy (hV0.symm.trans hVK)
  have hchord : V K - V 0 = y - x := by rw [hV0, hVK]
  have hRS : ‖y - x‖ ≤ plen V K := by rw [← hchord]; exact norm_sub_le_plen V K
  have hS : 0 < plen V K := hR.trans_le hRS
  -- the log excess `a ∈ [0, 1]` and `S - R ≤ 2 a R`
  obtain ⟨a, ha⟩ : ∃ a, a = Real.log (plen V K / ‖y - x‖) := ⟨_, rfl⟩
  have hSR : plen V K / ‖y - x‖ = Real.exp a := by rw [ha, Real.exp_log (div_pos hS hR)]
  have ha0 : 0 ≤ a := by rw [ha]; exact Real.log_nonneg ((one_le_div hR).2 hRS)
  have ha1 : a ≤ 1 := by
    have h1 : plen V K / ‖y - x‖ ≤ Real.exp a₀ := by rw [div_le_iff₀ hR]; exact hpoly
    rw [hSR] at h1
    linarith [Real.exp_le_exp.1 h1]
  have hSexp : plen V K - ‖y - x‖ ≤ 2 * a * ‖y - x‖ := by
    have h1 := exp_sub_one_le_two_mul ha0 ha1
    have h2 : plen V K = Real.exp a * ‖y - x‖ := by
      rw [← hSR, div_mul_cancel₀ _ hR.ne']
    rw [h2]
    nlinarith
  intro i hi
  subst hzV
  have hiK : i ≤ K := by simp only [List.length_map, List.length_range] at hi; omega
  rw [List.getElem_map, List.getElem_range, polyLen_range_map]
  change ‖V i - x - ((i : ℝ) / K) • (y - x)‖ ≤
    2 * ‖y - x‖ * Real.sqrt (Real.log (plen V K / ‖y - x‖))
  rw [← ha]
  have hsq := vertex_close_sq hK hV0 hVK hreg hiK
  have h4 : 2 * ‖y - x‖ * (plen V K - ‖y - x‖) ≤ (2 * ‖y - x‖ * Real.sqrt a) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt ha0]
    nlinarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 (hsq.trans h4)

end Converse

end HigherDimLFPP.Upper
