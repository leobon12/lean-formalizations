import HigherDimLFPP.Field.RampPath

/-!
# The polygons `Q_δ(f)` of Lemma 4.3 and their graph couplings (packet P-F3a, T3, part 2)

Source: planning audit HA3 (`planning/audits/HA3-section-4.md`), Details D5, Step 1a (the
parametrization `Q_δ(f)` of the good family `G_K(0, e₁)`) and interface (I5) of §7
("`W∞(ν_{Q_δ(f)}, μ_{δf}) ≤ C_{n,R} δ²`"); HA2 D7 (G1), (G3), (G4b) for the same estimates for the
knot polygons of Lemma 3.3.

**The polygon.**  For `K = 2ⁿ`, `f ∈ V_n(ℝ^{d-1})` and `δ`, `Q_δ(f)` has vertices
`z_i = x_i e₁ + (0, δ f(i/K))` for `i < K` and `z_K = e₁`, with horizontal knots
`x_i = Σ_{l<i} √(K⁻² - δ² |f((l+1)/K) - f(l/K)|²)` (`qKnot`, `qVert`); its first `K - 1` edges have
length `1/K` (for small `δ`).  `qMeasure d n δ f` is its normalized arclength
`Upper.polyMeasure (qPoly d n δ f)` (the list form used for the good family `G_K`).

**Results** (for `f` in the vertex ball `B̂_R` and `0 < δ ≤ δ₀(n, R)`, `qPolygon_facts`):

* `ν_{Q_δ(f)}` is a probability measure with the growth bound (3.4) at scale `1` and constant `4`;
* `ν_{Q_δ(f)}` and `μ_{δf}` are coupled within `A δ²`, `A = A(n, R)`;
* `ν_{Q_δ(f)}` is carried by the ball of radius `2`.

**Proof.**  Every vertex of `Q_δ(f)` is within `η = K²(2R)²δ²` of the graph vertex
`(i/K, δ f(i/K))` (`norm_qVert_sub_graphPt_le`: the transverse parts agree and
`0 ≤ K⁻¹ - √(K⁻² - a) ≤ K a`).  Both measures are pushforwards of Lebesgue measure on `[0,1]`: the
graph measure under the uniform-speed parametrization of the graph polygon
(`map_rampPath_graph`, since `f` is affine on the mesh intervals), the polygon measure under its
arclength parametrization (`polyMeasure_eq_map_rampPath`).  The two parametrizations differ by
`O(η + ε)` where `ε` bounds `|ℓ_i - 1/K|` (`norm_arcParam_sub_le`, via
`norm_rampPath_sub_le` and the elementary bound `abs_ramp_arc_sub_le`).  Growth follows from
`Upper.forward_growth`: every edge advances horizontally by at least half its length.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric Filter Topology
open scoped RealInnerProductSpace ENNReal

namespace HigherDimLFPP

/-! ## Arclength parametrization of a polygon -/

section ArcParam

variable {d : ℕ}

/-- The normalized arclength measure of a polygon with nondegenerate edges is the pushforward of
Lebesgue measure on `[0,1]` under its arclength parametrization. -/
theorem polyMeasure_eq_map_rampPath {m : ℕ} (hm : 0 < m) (V : ℕ → Rd d)
    (hℓ : ∀ i < m, 0 < ‖V (i + 1) - V i‖) :
    Upper.polyMeasure ((List.range (m + 1)).map V) =
      (volume.restrict (Icc (0 : ℝ) 1)).map
        (rampPath m (fun i => Upper.plen V i / Upper.plen V m) V) := by
  have hS : 0 < Upper.plen V m :=
    Finset.sum_pos (fun i hi => hℓ i (Finset.mem_range.1 hi)) (Finset.nonempty_range_iff.2 hm.ne')
  rw [Upper.polyMeasure_range_map, map_rampPath V ?_ ?_ (div_self hS.ne')]
  · congr 1
    funext i
    rw [Upper.plen_succ, add_div]
    ring
  · intro i hi
    rw [div_lt_div_iff_of_pos_right hS, Upper.plen_succ]
    linarith [hℓ i hi]
  · simp only [Upper.plen, Finset.range_zero, Finset.sum_empty, zero_div]

/-- Partial lengths of a polygon whose edges have length `1/m ± ε`. -/
theorem abs_plen_sub_le {m : ℕ} {V : ℕ → Rd d} {ε : ℝ}
    (hℓ : ∀ i < m, |‖V (i + 1) - V i‖ - 1 / m| ≤ ε) :
    ∀ i ≤ m, |Upper.plen V i - (i : ℝ) / m| ≤ i * ε := by
  intro i
  induction i with
  | zero =>
    intro _
    simp only [Upper.plen, Finset.range_zero, Finset.sum_empty, Nat.cast_zero, zero_div,
      sub_zero, abs_zero, zero_mul, le_refl]
  | succ i ih =>
    intro hi
    have h1 := ih (by omega)
    have h2 := hℓ i (by omega)
    rw [Upper.plen_succ]
    have e : Upper.plen V i + ‖V (i + 1) - V i‖ - (((i + 1 : ℕ) : ℝ) / m) =
        (Upper.plen V i - (i : ℝ) / m) + (‖V (i + 1) - V i‖ - 1 / m) := by
      push_cast
      ring
    rw [e]
    calc |Upper.plen V i - (i : ℝ) / m + (‖V (i + 1) - V i‖ - 1 / m)|
        ≤ |Upper.plen V i - (i : ℝ) / m| + |‖V (i + 1) - V i‖ - 1 / m| := abs_add_le _ _
      _ ≤ i * ε + ε := add_le_add h1 h2
      _ = ((i + 1 : ℕ) : ℝ) * ε := by push_cast; ring

/-- The elementary ramp comparison: arclength breakpoints `P/S` against uniform breakpoints
`i/m`. -/
theorem abs_ramp_arc_sub_le {s S P ℓ m ε i : ℝ} (hm : 0 < m) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hℓ : 1 / (2 * m) ≤ ℓ) (hSpos : 0 < S) (hSε : |S - 1| ≤ m * ε) (hPε : |P - i / m| ≤ m * ε)
    (hℓε : |ℓ - 1 / m| ≤ ε) (hi0 : 0 ≤ i) (him : i ≤ m) :
    |(s - P / S) / ((P + ℓ) / S - P / S) - (s - i / m) / ((i + 1) / m - i / m)| ≤
      8 * m ^ 2 * ε := by
  have hℓpos : 0 < ℓ := lt_of_lt_of_le (by positivity) hℓ
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans hℓε
  have e1a : (P + ℓ) / S - P / S = ℓ / S := by rw [add_div]; ring
  have e1b : (i + 1) / m - i / m = 1 / m := by rw [add_div]; ring
  have e1 : (s - P / S) / (ℓ / S) - (s - i / m) / (1 / m) =
      (s * (S - m * ℓ) - (P - i * ℓ)) / ℓ := by
    field_simp
    ring
  rw [e1a, e1b, e1, abs_div, abs_of_pos hℓpos, div_le_iff₀ hℓpos]
  have hX : |S - m * ℓ| ≤ 2 * m * ε := by
    have e : S - m * ℓ = (S - 1) - m * (ℓ - 1 / m) := by field_simp; ring
    rw [e]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_of_pos hm]
    have := mul_le_mul_of_nonneg_left hℓε hm.le
    linarith
  have hY : |P - i * ℓ| ≤ 2 * m * ε := by
    have e : P - i * ℓ = (P - i / m) - i * (ℓ - 1 / m) := by field_simp; ring
    rw [e]
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_of_nonneg hi0]
    have h1 := mul_le_mul_of_nonneg_left hℓε hi0
    have h2 := mul_le_mul_of_nonneg_right him hε0
    linarith
  have hsX : |s * (S - m * ℓ)| ≤ |S - m * ℓ| := by
    rw [abs_mul, abs_of_nonneg hs0]
    exact mul_le_of_le_one_left (abs_nonneg _) hs1
  have h4 : |s * (S - m * ℓ) - (P - i * ℓ)| ≤ 4 * m * ε :=
    (abs_sub _ _).trans (by linarith)
  have h5 : 4 * m * ε ≤ 8 * m ^ 2 * ε * ℓ := by
    have : 1 ≤ 2 * m * ℓ := by
      rw [div_le_iff₀ (by positivity)] at hℓ
      linarith
    linarith [mul_le_mul_of_nonneg_left this (show (0 : ℝ) ≤ 4 * m * ε by positivity)]
  linarith

/-- **Arclength versus uniform parametrization** (HA2 D7 (G4); HA3 (I5)): if the polygon `V`
starts at `w 0`, its vertices are within `η` of those of `w`, and its `m` edges have lengths
`1/m ± ε` with `ε ≤ 1/(2m)`, then for `s ∈ [0,1]` its arclength parametrization is within
`m (2η + 8 m² ε B)` of the uniform parametrization of `w` (whose edges are at most `B` long). -/
theorem norm_arcParam_sub_le {m : ℕ} (hm : 0 < m) {V w : ℕ → Rd d} {η ε B : ℝ}
    (h0 : V 0 = w 0) (hη : ∀ i ≤ m, ‖V i - w i‖ ≤ η)
    (hℓ : ∀ i < m, |‖V (i + 1) - V i‖ - 1 / m| ≤ ε) (hε : ε ≤ 1 / (2 * m))
    (hB : ∀ i < m, ‖w (i + 1) - w i‖ ≤ B) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ‖rampPath m (fun i => Upper.plen V i / Upper.plen V m) V s -
      rampPath m (fun i => (i : ℝ) / m) w s‖ ≤ m * (2 * η + 8 * (m : ℝ) ^ 2 * ε * B) := by
  have hmr : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans (hℓ 0 hm)
  have hℓlow : ∀ i < m, 1 / (2 * (m : ℝ)) ≤ ‖V (i + 1) - V i‖ := by
    intro i hi
    have h1 := (abs_le.1 (hℓ i hi)).1
    have e : (1 : ℝ) / m - 1 / (2 * m) = 1 / (2 * m) := by field_simp; ring
    linarith
  have hplen := abs_plen_sub_le hℓ
  have hS : |Upper.plen V m - 1| ≤ m * ε := by
    have := hplen m le_rfl
    rwa [div_self hmr.ne'] at this
  have hSpos : 0 < Upper.plen V m := by
    have h1 := (abs_le.1 hS).1
    have h2 : (m : ℝ) * ε ≤ 1 / 2 := by
      rw [le_div_iff₀ (by positivity)] at hε
      linarith
    linarith
  refine (norm_rampPath_sub_le m _ _ V w s).trans ?_
  rw [h0, sub_self, norm_zero, zero_add]
  calc ∑ i ∈ Finset.range m, (‖V (i + 1) - V i - (w (i + 1) - w i)‖ +
        |ramp (Upper.plen V i / Upper.plen V m) (Upper.plen V (i + 1) / Upper.plen V m) s -
          ramp ((i : ℝ) / m) (((i + 1 : ℕ) : ℝ) / m) s| * ‖w (i + 1) - w i‖)
      ≤ ∑ _i ∈ Finset.range m, (2 * η + 8 * (m : ℝ) ^ 2 * ε * B) := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hi' := Finset.mem_range.1 hi
        have a1 : ‖V (i + 1) - V i - (w (i + 1) - w i)‖ ≤ 2 * η := by
          rw [show V (i + 1) - V i - (w (i + 1) - w i) = (V (i + 1) - w (i + 1)) - (V i - w i)
            by abel]
          refine (norm_sub_le _ _).trans ?_
          linarith [hη (i + 1) hi', hη i hi'.le]
        have a2 : |ramp (Upper.plen V i / Upper.plen V m) (Upper.plen V (i + 1) / Upper.plen V m)
            s - ramp ((i : ℝ) / m) (((i + 1 : ℕ) : ℝ) / m) s| ≤ 8 * (m : ℝ) ^ 2 * ε := by
          refine (abs_ramp_sub_le _ _ _ _ s).trans ?_
          rw [Upper.plen_succ, Nat.cast_succ]
          have hPi := hplen i hi'.le
          have hi_le : (i : ℝ) ≤ m := by exact_mod_cast hi'.le
          exact abs_ramp_arc_sub_le hmr hs.1 hs.2 (hℓlow i hi') hSpos hS
            (hPi.trans (mul_le_mul_of_nonneg_right hi_le hε0)) (hℓ i hi') (Nat.cast_nonneg i)
            hi_le
        have a3 := hB i hi'
        have a4 : |ramp (Upper.plen V i / Upper.plen V m) (Upper.plen V (i + 1) / Upper.plen V m)
            s - ramp ((i : ℝ) / m) (((i + 1 : ℕ) : ℝ) / m) s| * ‖w (i + 1) - w i‖ ≤
            8 * (m : ℝ) ^ 2 * ε * B :=
          mul_le_mul a2 a3 (norm_nonneg _) (by positivity)
        linarith
    _ = m * (2 * η + 8 * (m : ℝ) ^ 2 * ε * B) := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- **Growth of a forward polygon** at scale `1` with constant `4`: if every edge advances
horizontally by a positive amount at least half its length, and the total length is at least
`1`. -/
theorem polyMeasure_growthBound (hd : 0 < d) {m : ℕ} (V : ℕ → Rd d)
    (hS : 1 ≤ Upper.plen V m) (hpos : ∀ i < m, 0 < Lower.horiz (V (i + 1) - V i))
    (hfwd : ∀ i < m, ‖V (i + 1) - V i‖ ≤ 2 * Lower.horiz (V (i + 1) - V i)) :
    GrowthBound (Upper.polyMeasure ((List.range (m + 1)).map V)) 4 1 := by
  have he : e₁ d ≠ 0 := by
    intro h
    have := Lower.norm_e₁ hd
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have hproj : ∀ p q : Rd d, Upper.proj 0 (e₁ d) p - Upper.proj 0 (e₁ d) q =
      Lower.horiz (p - q) := by
    intro p q
    rw [Upper.proj_sub, Lower.norm_e₁ hd, div_one, real_inner_comm]
    rfl
  have hSpos : 0 < Upper.plen V m := lt_of_lt_of_le one_pos hS
  have hW0 : ∀ i < m, 0 ≤ ‖V (i + 1) - V i‖ / Upper.plen V m := fun i _ => by positivity
  rw [Upper.polyMeasure_range_map]
  have hprob : IsProbabilityMeasure
      (Upper.segSum m (fun i => ‖V (i + 1) - V i‖ / Upper.plen V m) V) := by
    constructor
    rw [Upper.segSum_univ V hW0, ← Finset.sum_div]
    change ENNReal.ofReal (Upper.plen V m / Upper.plen V m) = 1
    rw [div_self hSpos.ne', ENNReal.ofReal_one]
  intro w t ht
  have hgrowth := Upper.forward_growth (V := V)
    (W := fun i => ‖V (i + 1) - V i‖ / Upper.plen V m) 0 he (κ := 2) (by norm_num) hW0
    (fun i hi => by rw [hproj]; exact hpos i hi)
    (fun i hi => by
      rw [hproj]
      calc ‖V (i + 1) - V i‖ / Upper.plen V m ≤ ‖V (i + 1) - V i‖ :=
            div_le_self (norm_nonneg _) hS
        _ ≤ 2 * Lower.horiz (V (i + 1) - V i) := hfwd i hi) w t
  have h1 := Upper.real_le_min_of_le (by positivity) hgrowth
  rw [div_one]
  rcases le_total t 1 with htt | htt
  · rw [min_eq_right htt]
    exact h1.trans ((min_le_right _ _).trans (le_of_eq (by ring)))
  · rw [min_eq_left htt]
    exact h1.trans ((min_le_left _ _).trans (by norm_num))

end ArcParam

/-! ## The graph polygon -/

section GraphPolygon

variable {d : ℕ}

/-- On `[0,1]` the uniform parametrization of the graph polygon of `f ∈ V_n` is the graph map. -/
theorem rampPath_graph_eq {n : ℕ} {f : ℝ → Rd (d - 1)} (hf : f ∈ Vg (Rd (d - 1)) n) (δ : ℝ)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    rampPath (2 ^ n) (fun i => (i : ℝ) / ((2 ^ n : ℕ) : ℝ))
      (fun i => graphPt (d := d) δ f ((i : ℝ) / 2 ^ n)) s = graphPt δ f s := by
  have hL : (0 : ℝ) < 2 ^ n := by positivity
  have hcast : ((2 ^ n : ℕ) : ℝ) = 2 ^ n := by push_cast; ring
  obtain ⟨k, hk, hks⟩ := exists_mesh_piece n hs
  have hT : ∀ i : ℕ, i < 2 ^ n →
      (i : ℝ) / ((2 ^ n : ℕ) : ℝ) < ((i + 1 : ℕ) : ℝ) / ((2 ^ n : ℕ) : ℝ) := by
    intro i _
    rw [hcast]
    gcongr
    linarith
  have hks' : s ∈ Icc ((k : ℝ) / ((2 ^ n : ℕ) : ℝ)) (((k + 1 : ℕ) : ℝ) / ((2 ^ n : ℕ) : ℝ)) := by
    rw [hcast]; push_cast; exact hks
  rw [rampPath_eq _ hT hk hks', hcast]
  obtain ⟨t, ht⟩ : ∃ t : ℝ, t = 2 ^ n * s - k := ⟨_, rfl⟩
  have hcoef : (s - (k : ℝ) / 2 ^ n) / (((k + 1 : ℕ) : ℝ) / 2 ^ n - (k : ℝ) / 2 ^ n) = t := by
    rw [ht]
    push_cast
    field_simp
    ring
  rw [hcoef]
  have hpiece : f s = f ((k : ℝ) / 2 ^ n) + t • (f (((k : ℝ) + 1) / 2 ^ n) - f ((k : ℝ) / 2 ^ n)) := by
    rw [ht]
    exact Var.Vg_piece hf hk hks
  have hs2 : s = (k : ℝ) / 2 ^ n + t * (((k : ℝ) + 1) / 2 ^ n - (k : ℝ) / 2 ^ n) := by
    rw [ht]
    field_simp
    ring
  simp only [graphPt]
  rw [hpiece]
  conv_rhs => rw [hs2]
  push_cast
  simp only [smul_add, Lower.embedT_add, Lower.embedT_smul, Lower.embedT_sub, smul_sub]
  module

/-- The graph measure of `f ∈ V_n` is the pushforward of Lebesgue measure under the uniform
parametrization of its graph polygon. -/
theorem map_rampPath_graph {n : ℕ} {f : ℝ → Rd (d - 1)} (hf : f ∈ Vg (Rd (d - 1)) n) (δ : ℝ) :
    (volume.restrict (Icc (0 : ℝ) 1)).map (rampPath (2 ^ n) (fun i => (i : ℝ) / ((2 ^ n : ℕ) : ℝ))
      (fun i => graphPt (d := d) δ f ((i : ℝ) / 2 ^ n))) = graphMeasure d δ f := by
  unfold graphMeasure
  refine Measure.map_congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
  exact rampPath_graph_eq hf δ hs

/-- The edges of the graph polygon: `w_{i+1} - w_i = 2⁻ⁿ e₁ + (0, δ Δ_i f)`. -/
theorem graph_edge (n : ℕ) (δ : ℝ) (f : ℝ → Rd (d - 1)) (i : ℕ) :
    graphPt (d := d) δ f (((i + 1 : ℕ) : ℝ) / 2 ^ n) - graphPt δ f ((i : ℝ) / 2 ^ n) =
      ((2 : ℝ) ^ n)⁻¹ • e₁ d +
        Lower.embedT (δ • (f (((i : ℝ) + 1) / 2 ^ n) - f ((i : ℝ) / 2 ^ n))) := by
  rw [graphPt_sub]
  congr 2
  · push_cast; field_simp; ring
  · push_cast; ring_nf

theorem horiz_graph_edge (hd : 0 < d) (n : ℕ) (δ : ℝ) (f : ℝ → Rd (d - 1)) (i : ℕ) :
    Lower.horiz (graphPt (d := d) δ f (((i + 1 : ℕ) : ℝ) / 2 ^ n) - graphPt δ f ((i : ℝ) / 2 ^ n)) =
      ((2 : ℝ) ^ n)⁻¹ := by
  rw [graph_edge, Lower.horiz_smul_e₁_add_embedT hd]

theorem norm_graph_edge_sq (hd : 0 < d) (n : ℕ) (δ : ℝ) (f : ℝ → Rd (d - 1)) (i : ℕ) :
    ‖graphPt (d := d) δ f (((i + 1 : ℕ) : ℝ) / 2 ^ n) - graphPt δ f ((i : ℝ) / 2 ^ n)‖ ^ 2 =
      ((2 : ℝ) ^ n)⁻¹ ^ 2 + δ ^ 2 * ‖f (((i : ℝ) + 1) / 2 ^ n) - f ((i : ℝ) / 2 ^ n)‖ ^ 2 := by
  rw [graph_edge, Lower.norm_sq_smul_e₁_add_embedT hd, norm_smul, mul_pow, Real.norm_eq_abs,
    sq_abs]

/-- `√(q² + t) ≤ q + t/(2q)` for `q > 0`, `t ≥ 0`. -/
theorem sqrt_sq_add_le {q t : ℝ} (hq : 0 < q) (ht : 0 ≤ t) :
    Real.sqrt (q ^ 2 + t) ≤ q + t / (2 * q) := by
  rw [Real.sqrt_le_left (by positivity)]
  have : (q + t / (2 * q)) ^ 2 = q ^ 2 + t + (t / (2 * q)) ^ 2 := by field_simp; ring
  rw [this]
  nlinarith [sq_nonneg (t / (2 * q))]

/-- Length of the graph edges: `2⁻ⁿ ≤ |w_{i+1} - w_i| ≤ 2⁻ⁿ + 2ⁿ δ² |Δ_i f|² / 2`. -/
theorem norm_graph_edge_bounds (hd : 0 < d) (n : ℕ) (δ : ℝ) (f : ℝ → Rd (d - 1)) (i : ℕ) :
    ((2 : ℝ) ^ n)⁻¹ ≤ ‖graphPt (d := d) δ f (((i + 1 : ℕ) : ℝ) / 2 ^ n) -
        graphPt δ f ((i : ℝ) / 2 ^ n)‖ ∧
      ‖graphPt (d := d) δ f (((i + 1 : ℕ) : ℝ) / 2 ^ n) - graphPt δ f ((i : ℝ) / 2 ^ n)‖ ≤
        ((2 : ℝ) ^ n)⁻¹ +
          2 ^ n * (δ ^ 2 * ‖f (((i : ℝ) + 1) / 2 ^ n) - f ((i : ℝ) / 2 ^ n)‖ ^ 2) / 2 := by
  have hq : (0 : ℝ) < ((2 : ℝ) ^ n)⁻¹ := by positivity
  set t := δ ^ 2 * ‖f (((i : ℝ) + 1) / 2 ^ n) - f ((i : ℝ) / 2 ^ n)‖ ^ 2 with ht
  have ht0 : 0 ≤ t := by positivity
  have hsq := norm_graph_edge_sq (d := d) hd n δ f i
  rw [← ht] at hsq
  have hnorm : ‖graphPt (d := d) δ f (((i + 1 : ℕ) : ℝ) / 2 ^ n) -
      graphPt δ f ((i : ℝ) / 2 ^ n)‖ = Real.sqrt (((2 : ℝ) ^ n)⁻¹ ^ 2 + t) := by
    rw [← hsq, Real.sqrt_sq (norm_nonneg _)]
  rw [hnorm]
  constructor
  · rw [Real.le_sqrt hq.le (by positivity)]
    linarith
  · refine (sqrt_sq_add_le hq ht0).trans (le_of_eq ?_)
    field_simp

end GraphPolygon

/-! ## The polygons `Q_δ(f)` -/

section QPolygon

/-- Horizontal increment of the `l`-th edge of `Q_δ(f)`:
`√(2⁻²ⁿ - δ² |f((l+1)2⁻ⁿ) - f(l 2⁻ⁿ)|²)` (HA3 D5, Step 1a). -/
def qInc {E : Type*} [NormedAddCommGroup E] (n : ℕ) (δ : ℝ) (f : ℝ → E) (l : ℕ) : ℝ :=
  Real.sqrt (((2 : ℝ) ^ n)⁻¹ ^ 2 - δ ^ 2 * ‖f (((l : ℝ) + 1) / 2 ^ n) - f ((l : ℝ) / 2 ^ n)‖ ^ 2)

/-- Horizontal knot `x_i = Σ_{l<i} qInc l` of `Q_δ(f)`. -/
def qKnot {E : Type*} [NormedAddCommGroup E] (n : ℕ) (δ : ℝ) (f : ℝ → E) (i : ℕ) : ℝ :=
  ∑ l ∈ Finset.range i, qInc n δ f l

variable {d : ℕ}

/-- The vertices of `Q_δ(f)`: `z_i = x_i e₁ + (0, δ f(i 2⁻ⁿ))` for `i < 2ⁿ`, and `z_{2ⁿ} = e₁`
(HA3 D5, Step 1a). -/
def qVert (d n : ℕ) (δ : ℝ) (f : ℝ → Rd (d - 1)) (i : ℕ) : Rd d :=
  if i < 2 ^ n then qKnot n δ f i • e₁ d + Lower.embedT (δ • f ((i : ℝ) / 2 ^ n)) else e₁ d

/-- The polygon `Q_δ(f)` as a vertex list. -/
def qPoly (d n : ℕ) (δ : ℝ) (f : ℝ → Rd (d - 1)) : List (Rd d) :=
  (List.range (2 ^ n + 1)).map (qVert d n δ f)

/-- The normalized arclength `ν_{Q_δ(f)}` of `Q_δ(f)`. -/
def qMeasure (d n : ℕ) (δ : ℝ) (f : ℝ → Rd (d - 1)) : Measure (Rd d) :=
  Upper.polyMeasure (qPoly d n δ f)

theorem qInc_le {E : Type*} [NormedAddCommGroup E] (n : ℕ) (δ : ℝ) (f : ℝ → E) (l : ℕ) :
    qInc n δ f l ≤ ((2 : ℝ) ^ n)⁻¹ := by
  unfold qInc
  calc Real.sqrt (((2 : ℝ) ^ n)⁻¹ ^ 2 -
        δ ^ 2 * ‖f (((l : ℝ) + 1) / 2 ^ n) - f ((l : ℝ) / 2 ^ n)‖ ^ 2)
      ≤ Real.sqrt (((2 : ℝ) ^ n)⁻¹ ^ 2) := Real.sqrt_le_sqrt (by
        have : 0 ≤ δ ^ 2 * ‖f (((l : ℝ) + 1) / 2 ^ n) - f ((l : ℝ) / 2 ^ n)‖ ^ 2 := by
          positivity
        linarith)
    _ = ((2 : ℝ) ^ n)⁻¹ := Real.sqrt_sq (by positivity)

/-- `0 ≤ q - √(q² - a) ≤ a / q` for `q > 0`, `a ≥ 0`. -/
theorem sub_sqrt_sub_le {q a : ℝ} (hq : 0 < q) (ha : 0 ≤ a) :
    q - Real.sqrt (q ^ 2 - a) ≤ a / q := by
  rw [le_div_iff₀ hq]
  set r := Real.sqrt (q ^ 2 - a) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hrq : r ≤ q := by
    rw [hr]
    calc Real.sqrt (q ^ 2 - a) ≤ Real.sqrt (q ^ 2) := Real.sqrt_le_sqrt (by linarith)
      _ = q := Real.sqrt_sq hq.le
  have hr2 : q ^ 2 - a ≤ r ^ 2 := by
    rcases le_or_gt 0 (q ^ 2 - a) with h | h
    · rw [hr, Real.sq_sqrt h]
    · have : r = 0 := by rw [hr]; exact Real.sqrt_eq_zero'.2 h.le
      rw [this]
      linarith
  linarith [mul_le_mul_of_nonneg_left hrq hr0]

theorem inv_sub_qInc_le {E : Type*} [NormedAddCommGroup E] (n : ℕ) (δ : ℝ) (f : ℝ → E) (l : ℕ) :
    ((2 : ℝ) ^ n)⁻¹ - qInc n δ f l ≤
      2 ^ n * (δ ^ 2 * ‖f (((l : ℝ) + 1) / 2 ^ n) - f ((l : ℝ) / 2 ^ n)‖ ^ 2) := by
  have hq : (0 : ℝ) < ((2 : ℝ) ^ n)⁻¹ := by positivity
  have h := sub_sqrt_sub_le hq (a := δ ^ 2 * ‖f (((l : ℝ) + 1) / 2 ^ n) -
    f ((l : ℝ) / 2 ^ n)‖ ^ 2) (by positivity)
  rw [div_inv_eq_mul] at h
  unfold qInc
  linarith [h]

/-- **Vertex closeness** (HA3 (I5); HA2 D7 (G1)): for `f ∈ V_n` with vertex bound `R` and
`i ≤ 2ⁿ`, `|z_i - (i 2⁻ⁿ, δ f(i 2⁻ⁿ))| ≤ 4ⁿ (2R)² δ²`. -/
theorem norm_qVert_sub_graphPt_le (hd : 0 < d) {n : ℕ} {f : ℝ → Rd (d - 1)}
    (hf : f ∈ Vg (Rd (d - 1)) n) {R : ℝ}
    (hR : ∀ i : ℕ, i ≤ 2 ^ n → ‖f ((i : ℝ) / 2 ^ n)‖ ≤ R) (δ : ℝ) {i : ℕ} (hi : i ≤ 2 ^ n) :
    ‖qVert d n δ f i - graphPt δ f ((i : ℝ) / 2 ^ n)‖ ≤ (2 ^ n) ^ 2 * (2 * R) ^ 2 * δ ^ 2 := by
  have hL : (0 : ℝ) < 2 ^ n := by positivity
  have hR0 : 0 ≤ R := by
    have := hR 0 (Nat.zero_le _)
    rw [Nat.cast_zero, zero_div, hf.1, norm_zero] at this
    exact this
  rcases lt_or_eq_of_le hi with hlt | heq
  · have e : qVert d n δ f i - graphPt δ f ((i : ℝ) / 2 ^ n) =
        (qKnot n δ f i - (i : ℝ) / 2 ^ n) • e₁ d := by
      rw [qVert, ite_eq_left hlt, graphPt, sub_smul]
      abel
    rw [e, norm_smul, Lower.norm_e₁ hd, mul_one, Real.norm_eq_abs]
    -- `i 2⁻ⁿ - x_i = Σ_{l<i} (2⁻ⁿ - qInc l) ∈ [0, i 2ⁿ δ² (2R)²]`
    have hsum : (i : ℝ) / 2 ^ n - qKnot n δ f i =
        ∑ l ∈ Finset.range i, (((2 : ℝ) ^ n)⁻¹ - qInc n δ f l) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, qKnot,
        div_eq_mul_inv]
    have hΔ : ∀ l ∈ Finset.range i,
        ‖f (((l : ℝ) + 1) / 2 ^ n) - f ((l : ℝ) / 2 ^ n)‖ ≤ 2 * R := by
      intro l hl
      have hl' := Finset.mem_range.1 hl
      have h1 := hR (l + 1) (by omega)
      have h2 := hR l (by omega)
      rw [Nat.cast_add, Nat.cast_one] at h1
      exact (norm_sub_le _ _).trans (by linarith)
    have hterm : ∀ l ∈ Finset.range i, 0 ≤ ((2 : ℝ) ^ n)⁻¹ - qInc n δ f l ∧
        ((2 : ℝ) ^ n)⁻¹ - qInc n δ f l ≤ 2 ^ n * (δ ^ 2 * (2 * R) ^ 2) := by
      intro l hl
      refine ⟨sub_nonneg.2 (qInc_le n δ f l), (inv_sub_qInc_le n δ f l).trans ?_⟩
      gcongr
      exact hΔ l hl
    have hnn : 0 ≤ (i : ℝ) / 2 ^ n - qKnot n δ f i := by
      rw [hsum]; exact Finset.sum_nonneg fun l hl => (hterm l hl).1
    have hle : (i : ℝ) / 2 ^ n - qKnot n δ f i ≤ i * (2 ^ n * (δ ^ 2 * (2 * R) ^ 2)) := by
      rw [hsum]
      refine (Finset.sum_le_sum fun l hl => (hterm l hl).2).trans (le_of_eq ?_)
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [abs_sub_comm, abs_of_nonneg hnn]
    have hi' : (i : ℝ) ≤ 2 ^ n := by exact_mod_cast hlt.le
    calc (i : ℝ) / 2 ^ n - qKnot n δ f i ≤ i * (2 ^ n * (δ ^ 2 * (2 * R) ^ 2)) := hle
      _ ≤ 2 ^ n * (2 ^ n * (δ ^ 2 * (2 * R) ^ 2)) := by gcongr
      _ = (2 ^ n) ^ 2 * (2 * R) ^ 2 * δ ^ 2 := by ring
  · subst heq
    have h1 : ((2 ^ n : ℕ) : ℝ) / 2 ^ n = 1 := by push_cast; exact div_self hL.ne'
    rw [qVert, ite_eq_right (lt_irrefl _), h1, graphPt, hf.2.1, smul_zero, Lower.embedT_zero, add_zero,
      one_smul, sub_self, norm_zero]
    positivity

theorem qVert_zero {n : ℕ} {f : ℝ → Rd (d - 1)} (hf0 : f 0 = 0) (δ : ℝ) :
    qVert d n δ f 0 = 0 := by
  rw [qVert, ite_eq_left (Nat.two_pow_pos n), qKnot, Finset.range_zero, Finset.sum_empty, zero_smul,
    zero_add, Nat.cast_zero, zero_div, hf0, smul_zero, Lower.embedT_zero]

theorem graphPt_zero_left {n : ℕ} {f : ℝ → Rd (d - 1)} (hf0 : f 0 = 0) (δ : ℝ) :
    graphPt (d := d) δ f (((0 : ℕ) : ℝ) / 2 ^ n) = 0 := by
  rw [Nat.cast_zero, zero_div, graphPt, hf0, smul_zero, Lower.embedT_zero, zero_smul, add_zero]

/-- The size of the graph coupling of `Q_δ(f)`, as a multiple of `δ²`. -/
def qConst (n : ℕ) (R : ℝ) : ℝ :=
  (2 ^ n : ℝ) * (2 * ((2 ^ n) ^ 2 * (2 * R) ^ 2) +
    8 * (2 ^ n : ℝ) ^ 2 * (2 * ((2 ^ n) ^ 2 * (2 * R) ^ 2) + 2 ^ n * (2 * R) ^ 2 / 2) *
      ((2 ^ n : ℝ)⁻¹ + 1))

/-- The threshold `δ₀(n, R)` below which `Q_δ(f)` is a forward polygon close to the graph. -/
def qDelta0 (n : ℕ) (R : ℝ) : ℝ :=
  min 1 (((2 : ℝ) ^ n)⁻¹ /
    (8 * (2 * ((2 ^ n) ^ 2 * (2 * R) ^ 2) + 2 ^ n * (2 * R) ^ 2 / 2) + 2 * (2 * R) + 1))

theorem qDelta0_pos (n : ℕ) {R : ℝ} (hR : 0 ≤ R) : 0 < qDelta0 n R := by
  unfold qDelta0
  exact lt_min one_pos (by positivity)

/-- The graph polygon vertices `w_i = (i 2⁻ⁿ, δ f(i 2⁻ⁿ))`. -/
def gVert (d n : ℕ) (δ : ℝ) (f : ℝ → Rd (d - 1)) (i : ℕ) : Rd d :=
  graphPt δ f ((i : ℝ) / 2 ^ n)

/-- **Edge lengths of `Q_δ(f)`** (HA2 D7 (G1); HA3 D5, Step 1b), for every `δ`: for `f` in the
vertex ball `B̂_R` and `i < 2ⁿ`,
`|ℓ_i - 2⁻ⁿ| ≤ (2 · 4ⁿ (2R)² + 2ⁿ (2R)²/2) δ²`, where `ℓ_i = |z_{i+1} - z_i|`. -/
theorem abs_norm_qEdge_sub_le (hd : 0 < d) {n : ℕ} {R δ : ℝ} {f : ℝ → Rd (d - 1)}
    (hf : f ∈ vertBall (Rd (d - 1)) n R) {i : ℕ} (hi : i < 2 ^ n) :
    |‖qVert d n δ f (i + 1) - qVert d n δ f i‖ - ((2 : ℝ) ^ n)⁻¹| ≤
      (2 * ((2 ^ n) ^ 2 * (2 * R) ^ 2) + 2 ^ n * (2 * R) ^ 2 / 2) * δ ^ 2 := by
  obtain ⟨hfV, hfR⟩ := hf
  have hc1 := norm_qVert_sub_graphPt_le hd hfV hfR δ hi.le
  have hc2 := norm_qVert_sub_graphPt_le hd hfV hfR δ (show i + 1 ≤ 2 ^ n by omega)
  have hdiff : ‖(qVert d n δ f (i + 1) - qVert d n δ f i) - (gVert d n δ f (i + 1) -
      gVert d n δ f i)‖ ≤ 2 * ((2 ^ n) ^ 2 * (2 * R) ^ 2 * δ ^ 2) := by
    rw [show qVert d n δ f (i + 1) - qVert d n δ f i - (gVert d n δ f (i + 1) - gVert d n δ f i)
      = (qVert d n δ f (i + 1) - gVert d n δ f (i + 1)) - (qVert d n δ f i - gVert d n δ f i)
      by abel]
    refine (norm_sub_le _ _).trans ?_
    rw [gVert, gVert]
    linarith
  obtain ⟨b1, b2⟩ := norm_graph_edge_bounds (d := d) hd n δ f i
  have hΔ : ‖f (((i : ℝ) + 1) / 2 ^ n) - f ((i : ℝ) / 2 ^ n)‖ ≤ 2 * R := by
    have h1 := hfR (i + 1) hi
    have h2 := hfR i hi.le
    rw [Nat.cast_add, Nat.cast_one] at h1
    exact (norm_sub_le _ _).trans (by linarith)
  have hΔ2 : ‖f (((i : ℝ) + 1) / 2 ^ n) - f ((i : ℝ) / 2 ^ n)‖ ^ 2 ≤ (2 * R) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hΔ 2
  have h3 : (2 : ℝ) ^ n * (δ ^ 2 * ‖f (((i : ℝ) + 1) / 2 ^ n) - f ((i : ℝ) / 2 ^ n)‖ ^ 2) / 2 ≤
      2 ^ n * (2 * R) ^ 2 / 2 * δ ^ 2 := by
    have e1 : (2 : ℝ) ^ n * (δ ^ 2 * ‖f (((i : ℝ) + 1) / 2 ^ n) - f ((i : ℝ) / 2 ^ n)‖ ^ 2) / 2
        = (2 : ℝ) ^ n / 2 * (δ ^ 2 * ‖f (((i : ℝ) + 1) / 2 ^ n) - f ((i : ℝ) / 2 ^ n)‖ ^ 2) := by
      ring
    have e2 : (2 : ℝ) ^ n * (2 * R) ^ 2 / 2 * δ ^ 2 = (2 : ℝ) ^ n / 2 * (δ ^ 2 * (2 * R) ^ 2) := by
      ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hΔ2 (by positivity))
      (by positivity)
  have hw : gVert d n δ f (i + 1) - gVert d n δ f i =
      graphPt (d := d) δ f (((i + 1 : ℕ) : ℝ) / 2 ^ n) - graphPt δ f ((i : ℝ) / 2 ^ n) := rfl
  have a1 := abs_norm_sub_norm_le (qVert d n δ f (i + 1) - qVert d n δ f i)
    (gVert d n δ f (i + 1) - gVert d n δ f i)
  rw [hw] at a1 hdiff
  rw [abs_le] at a1 ⊢
  constructor <;> nlinarith

/-- **The polygon facts** (HA3 (I5), HA2 D7 (G3), (G4b)): for `f` in the vertex ball `B̂_R` and
`0 < δ ≤ δ₀(n, R)`, `ν_{Q_δ(f)}` is the arclength pushforward of Lebesgue measure (so a probability
measure), has the growth bound (3.4) at scale `1` with constant `4`, is coupled with `μ_{δf}`
within `A δ²` (`A = qConst n R`), and is carried by the ball of radius `2`. -/
theorem qPolygon_facts (hd : 0 < d) {n : ℕ} {R : ℝ} (hR0 : 0 ≤ R) {δ : ℝ} (hδ : 0 < δ)
    (hδ0 : δ ≤ qDelta0 n R) {f : ℝ → Rd (d - 1)} (hf : f ∈ vertBall (Rd (d - 1)) n R) :
    IsProbabilityMeasure (qMeasure d n δ f) ∧ GrowthBound (qMeasure d n δ f) 4 1 ∧
      CoupledWithin (qMeasure d n δ f) (graphMeasure d δ f) (qConst n R * δ ^ 2) ∧
      ∀ᵐ z ∂(qMeasure d n δ f), ‖z‖ ≤ 2 := by
  obtain ⟨hfV, hfR⟩ := hf
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = (2 : ℝ) ^ n := ⟨_, rfl⟩
  have hκpos : 0 < κ := by rw [hκ]; positivity
  have hκ1 : 1 ≤ κ := by rw [hκ]; exact one_le_pow₀ (by norm_num)
  have hκinv0 : 0 < κ⁻¹ := inv_pos.2 hκpos
  have hκinv1 : κ⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hκ1
  have hm : 0 < 2 ^ n := Nat.two_pow_pos n
  have hmcast : ((2 ^ n : ℕ) : ℝ) = κ := by rw [hκ]; push_cast; ring
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 2 * R := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  obtain ⟨η, hη⟩ : ∃ η : ℝ, η = κ ^ 2 * c ^ 2 * δ ^ 2 := ⟨_, rfl⟩
  obtain ⟨A₁, hA₁⟩ : ∃ A₁ : ℝ, A₁ = 2 * (κ ^ 2 * c ^ 2) + κ * c ^ 2 / 2 := ⟨_, rfl⟩
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = A₁ * δ ^ 2 := ⟨_, rfl⟩
  have hA₁0 : 0 ≤ A₁ := by rw [hA₁]; positivity
  have hη0 : 0 ≤ η := by rw [hη]; positivity
  -- smallness of `δ`
  have hδ0' : δ ≤ min 1 (κ⁻¹ / (8 * A₁ + 2 * c + 1)) := by
    have h := hδ0
    unfold qDelta0 at h
    rw [← hκ, ← hc, ← hA₁] at h
    exact h
  have hδ1 : δ ≤ 1 := hδ0'.trans (min_le_left _ _)
  have hD : 0 < 8 * A₁ + 2 * c + 1 := by positivity
  have hδ2 : δ * (8 * A₁ + 2 * c + 1) ≤ κ⁻¹ := by
    have h := hδ0'.trans (min_le_right _ _)
    rwa [le_div_iff₀ hD] at h
  have hδc : δ * c ≤ κ⁻¹ / 2 := by
    have h2 : δ * (2 * c) ≤ δ * (8 * A₁ + 2 * c + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hδ.le
    linarith
  have hδsq : δ ^ 2 ≤ δ := pow_le_of_le_one hδ.le hδ1 (by norm_num)
  have hεsmall : ε ≤ κ⁻¹ / 8 := by
    have h2 : A₁ * δ ^ 2 ≤ A₁ * δ := mul_le_mul_of_nonneg_left hδsq hA₁0
    have h3 : δ * (8 * A₁ + 2 * c + 1) = 8 * (A₁ * δ) + δ * (2 * c + 1) := by ring
    have h4 : 0 ≤ δ * (2 * c + 1) := by positivity
    rw [hε]
    linarith
  have hεeq : ε = 2 * η + κ * c ^ 2 / 2 * δ ^ 2 := by rw [hε, hA₁, hη]; ring
  have hgpos : 0 ≤ κ * c ^ 2 / 2 * δ ^ 2 := by positivity
  have hηε : 2 * η ≤ ε := by linarith
  have hgε : κ * c ^ 2 / 2 * δ ^ 2 ≤ ε := by linarith
  have hε1 : ε ≤ 1 := by linarith
  -- vertex closeness
  have hclose : ∀ i ≤ 2 ^ n, ‖qVert d n δ f i - gVert d n δ f i‖ ≤ η := by
    intro i hi
    have := norm_qVert_sub_graphPt_le hd hfV hfR δ hi
    rw [hη, hκ, hc]
    exact this
  have h0 : qVert d n δ f 0 = gVert d n δ f 0 := by
    rw [qVert_zero hfV.1, gVert, ← graphPt_zero_left (n := n) hfV.1 δ]
  -- the graph edges
  have hΔf : ∀ i : ℕ, i < 2 ^ n →
      ‖f (((i : ℝ) + 1) / 2 ^ n) - f ((i : ℝ) / 2 ^ n)‖ ≤ c := by
    intro i hi
    have h1 := hfR (i + 1) hi
    have h2 := hfR i hi.le
    rw [Nat.cast_add, Nat.cast_one] at h1
    exact (norm_sub_le _ _).trans (by rw [hc]; linarith)
  have hwlen : ∀ i < 2 ^ n, κ⁻¹ ≤ ‖gVert d n δ f (i + 1) - gVert d n δ f i‖ ∧
      ‖gVert d n δ f (i + 1) - gVert d n δ f i‖ ≤ κ⁻¹ + κ * c ^ 2 / 2 * δ ^ 2 := by
    intro i hi
    obtain ⟨b1, b2⟩ := norm_graph_edge_bounds (d := d) hd n δ f i
    have e : gVert d n δ f (i + 1) - gVert d n δ f i =
        graphPt (d := d) δ f (((i + 1 : ℕ) : ℝ) / 2 ^ n) - graphPt δ f ((i : ℝ) / 2 ^ n) := rfl
    have h1 : ‖f (((i : ℝ) + 1) / 2 ^ n) - f ((i : ℝ) / 2 ^ n)‖ ^ 2 ≤ c ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hΔf i hi) 2
    have h2 : δ ^ 2 * ‖f (((i : ℝ) + 1) / 2 ^ n) - f ((i : ℝ) / 2 ^ n)‖ ^ 2 ≤ δ ^ 2 * c ^ 2 :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : (2 : ℝ) ^ n * (δ ^ 2 * ‖f (((i : ℝ) + 1) / 2 ^ n) - f ((i : ℝ) / 2 ^ n)‖ ^ 2) / 2 ≤
        (2 : ℝ) ^ n * c ^ 2 / 2 * δ ^ 2 := by
      have e1 : (2 : ℝ) ^ n * (δ ^ 2 * ‖f (((i : ℝ) + 1) / 2 ^ n) - f ((i : ℝ) / 2 ^ n)‖ ^ 2) / 2
          = (2 : ℝ) ^ n / 2 * (δ ^ 2 * ‖f (((i : ℝ) + 1) / 2 ^ n) - f ((i : ℝ) / 2 ^ n)‖ ^ 2) := by
        ring
      have e2 : (2 : ℝ) ^ n * c ^ 2 / 2 * δ ^ 2 = (2 : ℝ) ^ n / 2 * (δ ^ 2 * c ^ 2) := by ring
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_left h2 (by positivity)
    rw [e, hκ]
    exact ⟨b1, b2.trans (by linarith)⟩
  have hwlen' : ∀ i < 2 ^ n, ‖gVert d n δ f (i + 1) - gVert d n δ f i‖ ≤ κ⁻¹ + 1 := by
    intro i hi
    have h1 := (hwlen i hi).2
    linarith
  -- the polygon edges
  have hdiff : ∀ i < 2 ^ n, ‖(qVert d n δ f (i + 1) - qVert d n δ f i) -
      (gVert d n δ f (i + 1) - gVert d n δ f i)‖ ≤ 2 * η := by
    intro i hi
    rw [show qVert d n δ f (i + 1) - qVert d n δ f i - (gVert d n δ f (i + 1) - gVert d n δ f i)
      = (qVert d n δ f (i + 1) - gVert d n δ f (i + 1)) - (qVert d n δ f i - gVert d n δ f i)
      by abel]
    refine (norm_sub_le _ _).trans ?_
    linarith [hclose (i + 1) hi, hclose i hi.le]
  have hℓ : ∀ i < 2 ^ n,
      |‖qVert d n δ f (i + 1) - qVert d n δ f i‖ - 1 / ((2 ^ n : ℕ) : ℝ)| ≤ ε := by
    intro i hi
    rw [hmcast, one_div]
    have a1 := abs_norm_sub_norm_le (qVert d n δ f (i + 1) - qVert d n δ f i)
      (gVert d n δ f (i + 1) - gVert d n δ f i)
    have a2 := hdiff i hi
    obtain ⟨b1, b2⟩ := hwlen i hi
    rw [abs_le] at a1 ⊢
    constructor <;> linarith
  have hεm : ε ≤ 1 / (2 * ((2 ^ n : ℕ) : ℝ)) := by
    rw [hmcast]
    have e : 1 / (2 * κ) = κ⁻¹ / 2 := by field_simp
    rw [e]
    linarith
  have hℓpos : ∀ i < 2 ^ n, 0 < ‖qVert d n δ f (i + 1) - qVert d n δ f i‖ := by
    intro i hi
    have h1 := (abs_le.1 (hℓ i hi)).1
    rw [hmcast, one_div] at h1
    linarith
  -- the measures as pushforwards
  have hmapQ : qMeasure d n δ f = (volume.restrict (Icc (0 : ℝ) 1)).map
      (rampPath (2 ^ n) (fun i => Upper.plen (qVert d n δ f) i /
        Upper.plen (qVert d n δ f) (2 ^ n)) (qVert d n δ f)) := by
    rw [qMeasure, qPoly]
    exact polyMeasure_eq_map_rampPath hm _ hℓpos
  have hmapG : (volume.restrict (Icc (0 : ℝ) 1)).map (rampPath (2 ^ n)
      (fun i => (i : ℝ) / ((2 ^ n : ℕ) : ℝ)) (gVert d n δ f)) = graphMeasure d δ f :=
    map_rampPath_graph (d := d) hfV δ
  have hprob : IsProbabilityMeasure (qMeasure d n δ f) := by
    rw [hmapQ]; infer_instance
  refine ⟨hprob, ?_, ?_, ?_⟩
  · -- growth: every edge advances horizontally by at least half its length
    have hhor : ∀ i < 2 ^ n, κ⁻¹ - 2 * η ≤
        Lower.horiz (qVert d n δ f (i + 1) - qVert d n δ f i) := by
      intro i hi
      have h1 := Lower.abs_horiz_le ((qVert d n δ f (i + 1) - qVert d n δ f i) -
        (gVert d n δ f (i + 1) - gVert d n δ f i)) hd
      rw [Lower.horiz_sub] at h1
      have h2 : Lower.horiz (gVert d n δ f (i + 1) - gVert d n δ f i) = κ⁻¹ := by
        rw [gVert, gVert, horiz_graph_edge hd, hκ]
      rw [h2] at h1
      linarith [(abs_le.1 (h1.trans (hdiff i hi))).1]
    have hS : 1 ≤ Upper.plen (qVert d n δ f) (2 ^ n) := by
      have h1 := Upper.norm_sub_le_plen (qVert d n δ f) (2 ^ n)
      have h2 : qVert d n δ f (2 ^ n) - qVert d n δ f 0 = e₁ d := by
        rw [qVert_zero hfV.1, sub_zero, qVert, ite_eq_right (lt_irrefl _)]
      rw [h2, Lower.norm_e₁ hd] at h1
      exact h1
    refine polyMeasure_growthBound hd _ hS (fun i hi => ?_) (fun i hi => ?_)
    · have := hhor i hi
      linarith
    · have h1 := hhor i hi
      have h2 : ‖qVert d n δ f (i + 1) - qVert d n δ f i‖ ≤
          ‖gVert d n δ f (i + 1) - gVert d n δ f i‖ + 2 * η := by
        have := norm_le_insert' (qVert d n δ f (i + 1) - qVert d n δ f i)
          (gVert d n δ f (i + 1) - gVert d n δ f i)
        linarith [hdiff i hi]
      have h3 := (hwlen i hi).2
      linarith
  · -- coupling
    rw [hmapQ, ← hmapG]
    refine coupledWithin_map (continuous_rampPath _ _ _).measurable
      (continuous_rampPath _ _ _).measurable fun s hs => ?_
    have h := norm_arcParam_sub_le hm h0 hclose hℓ hεm (B := κ⁻¹ + 1) hwlen' hs
    refine h.trans (le_of_eq ?_)
    rw [hmcast, hε, hA₁, hη, hc, hκ, qConst]
    ring
  · -- support
    rw [qMeasure, qPoly, Upper.polyMeasure_range_map]
    refine ae_norm_le_segSum fun i hi => ?_
    have h1 := hclose i hi
    have h2 : ‖gVert d n δ f i‖ ≤ 1 + δ * R := by
      rw [gVert]
      refine (norm_graphPt_le δ f _).trans ?_
      rw [Lower.norm_e₁ hd, mul_one, abs_of_nonneg (by positivity), abs_of_pos hδ]
      have h3 : (i : ℝ) / 2 ^ n ≤ 1 := by
        rw [div_le_one (by positivity)]
        exact_mod_cast hi
      have h4 := mul_le_mul_of_nonneg_left (hfR i hi) hδ.le
      linarith
    have h3 : ‖qVert d n δ f i‖ ≤ ‖gVert d n δ f i‖ + η := by
      have := norm_le_insert' (qVert d n δ f i) (gVert d n δ f i)
      linarith
    have h4 : δ * R ≤ 1 / 2 := by
      have : δ * c ≤ 1 / 2 := by linarith
      rw [hc] at this
      linarith
    linarith

end QPolygon

end HigherDimLFPP
