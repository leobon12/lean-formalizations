import HigherDimLFPP.Frozen.IsAdmissiblePath
import HigherDimLFPP.Frozen.LfppLength
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The partition tree of §4.1–4.2: definitions and node statements

Source: `source/higher-dimensional-lfpp-limit.pdf`, §4.1–4.2 (lines 570–803 of the text version),
as corrected by the planning audit HA3 (`planning/audits/HA3-section-4.md`: Details D1, D2, D4 and
the recommended Lean statements in "(c)"); ruling H7 (dyadic blocks `K = 2ⁿ`, threshold
`a₀ = c₀ / K` with `c₀ = 1/500`, explicit good family `G_K`).

2D source: the definitions `CutTree`, `CutTree.WF`, `segAvg`, `edges`, `polyLen` of
`LQGDimension/Blueprint/Draft/LFPPPlan.lean`, generalized as in HA3 (c):

* paths take values in a normed group (`Rd d` for the statements) instead of `ℂ`;
* the ratio of the first-exit construction is any natural number `K` (the source uses `K = 2ⁿ`);
* the containment property `P_v ⊂ B̄(x_v, 4 R_v)` is required for non-root nodes only, and the
  root has its own containment radius `ρ₀` (`2 √d` for the cube `U = (-2,2)^d`, HA3 F7);
* `G_u` and the cost `b_u` use a threshold `a₀` (`b_u = min(a_u, a₀)/δ²`), instead of the 2D
  threshold `1` and bins `⌊min(A, 1)/δ²⌋`;
* the oscillation is taken on `closure U` at distance `5 ε` (D2);
* the good family `G_K(x, y)` of Lemma 4.3 is explicit (HA3 F2).

The node statements `PathTreeExists`, `ChainLengthBound`, `TreeInequality` and
`GoodNodeGeometry` are HA3's (c) statements with the frozen `cube`, `e₁`, `IsAdmissiblePath`,
`lfppLength` and `Rd`.  They are proved in `HigherDimLFPP.Upper.PathTree`,
`HigherDimLFPP.Upper.TreeInequality` and `HigherDimLFPP.Upper.GoodNode`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set
open scoped RealInnerProductSpace

namespace HigherDimLFPP.Upper

/-! ## Trees of consecutive subpaths -/

/-- A finite tree of consecutive subpaths of a path (as `LQGDimension.Blueprint.Draft.CutTree`):
nodes are addresses (root `[]`, children `u ++ [i]`); node `u` is the subpath on the time
interval `[t₀ u, t₁ u]` and has `nch u` children (`0` for leaves). -/
structure CutTree where
  /-- The addresses of the nodes. -/
  nodes : Finset (List ℕ)
  /-- Start time of the subpath of a node. -/
  t₀ : List ℕ → ℝ
  /-- End time of the subpath of a node. -/
  t₁ : List ℕ → ℝ
  /-- Number of children of a node. -/
  nch : List ℕ → ℕ

namespace CutTree

variable {E : Type*} [NormedAddCommGroup E] (T : CutTree) (γ : ℝ → E)

/-- Start point `x_u` of the chord of node `u`. -/
def x (u : List ℕ) : E := γ (T.t₀ u)

/-- End point `y_u` of the chord of node `u`. -/
def y (u : List ℕ) : E := γ (T.t₁ u)

/-- Chord length `R_u = |y_u - x_u|`. -/
def R (u : List ℕ) : ℝ := ‖T.y γ u - T.x γ u‖

/-- `S_u = Σ_v R_v` over the children `v` of `u` ((4.4)). -/
def S (u : List ℕ) : ℝ := ∑ i ∈ Finset.range (T.nch u), T.R γ (u ++ [i])

/-- The log excess `a_u = log(S_u / R_u)` ((4.4)). -/
def A (u : List ℕ) : ℝ := Real.log (T.S γ u / T.R γ u)

/-- The unit flow `θ(v) = Π p_{uv}` with `p_{uv} = R_v / S_u` along the ancestry of `v`. -/
def flow (v : List ℕ) : ℝ :=
  ∏ j ∈ Finset.range v.length, T.R γ (v.take (j + 1)) / T.S γ (v.take j)

/-- The leaves. -/
def leaves : Finset (List ℕ) := T.nodes.filter fun u => T.nch u = 0

/-- Well-formedness: the consecutive first-exit partition of §4.1 at ratio `K`, cutoff `ε` and
root containment radius `ρ₀` (`2 √d` for `U = (-2,2)^d`); (4.2) and HA3 D1. -/
structure WF (K : ℕ) (ε ρ₀ : ℝ) : Prop where
  root_mem : [] ∈ T.nodes
  root_time : T.t₀ [] = 0 ∧ T.t₁ [] = 1
  child_mem : ∀ u ∈ T.nodes, ∀ i < T.nch u, u ++ [i] ∈ T.nodes
  is_child : ∀ v ∈ T.nodes, v = [] ∨ ∃ u ∈ T.nodes, ∃ i < T.nch u, v = u ++ [i]
  time_le : ∀ u ∈ T.nodes, T.t₀ u ≤ T.t₁ u
  consecutive : ∀ u ∈ T.nodes, 0 < T.nch u →
    T.t₀ (u ++ [0]) = T.t₀ u ∧ T.t₁ (u ++ [T.nch u - 1]) = T.t₁ u ∧
    ∀ i, i + 1 < T.nch u → T.t₁ (u ++ [i]) = T.t₀ (u ++ [i + 1])
  internal_iff : ∀ u ∈ T.nodes, 0 < T.nch u ↔ ε < T.R γ u
  scale : ∀ u ∈ T.nodes, ∀ i < T.nch u,
    T.R γ u / (2 * K) ≤ T.R γ (u ++ [i]) ∧ T.R γ (u ++ [i]) ≤ 3 * T.R γ u / (2 * K)
  regular : ∀ u ∈ T.nodes, ∀ i, i + 1 < T.nch u → T.R γ (u ++ [i]) = T.R γ u / K
  ball : ∀ v ∈ T.nodes, v ≠ [] → ∀ t ∈ Icc (T.t₀ v) (T.t₁ v), ‖γ t - T.x γ v‖ ≤ 4 * T.R γ v
  root_ball : ∀ t ∈ Icc (0 : ℝ) 1, ‖γ t - γ 0‖ ≤ ρ₀

end CutTree

/-! ## Segment averages, oscillation, polygons -/

/-- `⟨φ, ν_{[a,b]}⟩ = ∫₀¹ φ(a + s (b - a)) ds`, the average of `φ` over the segment `[a, b]`
(`φ a` if `a = b`). -/
def segAvg {d : ℕ} (φ : Rd d → ℝ) (a b : Rd d) : ℝ :=
  ∫ s in (0 : ℝ)..1, φ (a + s • (b - a))

/-- The oscillation `ω(r)` of `φ` on `closure U` at distance `r`. -/
def osc {d : ℕ} (φ : Rd d → ℝ) (r : ℝ) : ℝ :=
  sSup {v | ∃ z w : Rd d, z ∈ closure (cube d) ∧ w ∈ closure (cube d) ∧ ‖z - w‖ ≤ r ∧
    v = |φ z - φ w|}

/-- The edges `[z₀,z₁], [z₁,z₂], …` of a vertex list. -/
def edges {d : ℕ} (z : List (Rd d)) : List (Rd d × Rd d) := z.zip z.tail

/-- Euclidean length of a polygon given by its vertex list. -/
def polyLen {d : ℕ} (z : List (Rd d)) : ℝ := ((edges z).map fun e => ‖e.2 - e.1‖).sum

/-- The good family `G_K(x, y)` (HA3 F2; the explicit form of the "intrinsic good family" of
Lemma 4.3) with threshold `a₀`: polygons with vertices `z₀ = x, …, z_K = y`, whose first `K - 1`
edges have length `|y - x| / K`, all of whose edges make an angle at most `1/10` with `y - x`,
and whose length is at most `e^{a₀} |y - x|`. -/
def goodFamily {d : ℕ} (K : ℕ) (a₀ : ℝ) (x y : Rd d) : Set (List (Rd d)) :=
  {z | z.length = K + 1 ∧ z.head? = some x ∧ z.getLast? = some y ∧
    (∀ e ∈ (edges z).dropLast, ‖e.2 - e.1‖ = ‖y - x‖ / K) ∧
    (∀ e ∈ edges z, Real.cos (1 / 10) * ‖e.2 - e.1‖ * ‖y - x‖ ≤ ⟪e.2 - e.1, y - x⟫) ∧
    polyLen z ≤ Real.exp a₀ * ‖y - x‖}

namespace CutTree

variable {d : ℕ} (T : CutTree) (γ : ℝ → Rd d)

/-- `H_u = ⟨φ, ν_{I_u}⟩`, `I_u = [x_u, y_u]`. -/
def H (φ : Rd d → ℝ) (u : List ℕ) : ℝ := segAvg φ (T.x γ u) (T.y γ u)

/-- `G_u` of §4.3 with threshold `a₀`: `-Δ_u` if `u` is good (`a_u ≤ a₀`), and
`max_v (H_u - H_v)` over the children otherwise. -/
def G (a₀ : ℝ) (φ : Rd d → ℝ) (u : List ℕ) : ℝ :=
  if T.A γ u ≤ a₀ then
    T.H γ φ u - ∑ i ∈ Finset.range (T.nch u), (T.R γ (u ++ [i]) / T.S γ u) * T.H γ φ (u ++ [i])
  else ⨆ i : Fin (T.nch u), (T.H γ φ u - T.H γ φ (u ++ [(i : ℕ)]))

/-- The cost `b_u = min(a_u, a₀) / δ²` of (4.15): `a_u / δ²` if good, `a₀ / δ²` if bad. -/
def bcost (a₀ δ : ℝ) (u : List ℕ) : ℝ := min (T.A γ u) a₀ / δ ^ 2

/-- The child polygon `Q_u` (vertices `x_{u0}, …, x_{u(p-1)}, y_u`). -/
def childPoly (u : List ℕ) : List (Rd d) :=
  (List.range (T.nch u)).map (fun i => T.x γ (u ++ [i])) ++ [T.y γ u]

end CutTree

/-! ## Node statements (HA3 (c)) -/

/-- **(4.2)–(4.3): tree existence** (generalizes `LQGDimension.LFPPTree.pathTreeExists`).
Every admissible path has a well-formed partition tree, for every ratio `K ≥ 8` and every cutoff
`ε ∈ (0, 1)`, with root containment radius `2 √d`. -/
def PathTreeExists (d : ℕ) [NeZero d] : Prop :=
  ∀ γ : ℝ → Rd d, IsAdmissiblePath d γ → ∀ K : ℕ, 8 ≤ K → ∀ ε ∈ Ioo (0 : ℝ) 1,
    ∃ T : CutTree, T.WF γ K ε (2 * Real.sqrt d)

/-- **(4.3) for every cutoff:** a chain of internal nodes has at most `⌈log(1/ε)/log(2K/3)⌉`
nodes, i.e. every leaf has depth at most `log(1/ε)/log(2K/3) + 1`. -/
def ChainLengthBound (d : ℕ) [NeZero d] : Prop :=
  ∀ γ : ℝ → Rd d, IsAdmissiblePath d γ → ∀ K : ℕ, 8 ≤ K → ∀ ε ∈ Ioo (0 : ℝ) 1,
    ∀ T : CutTree, T.WF γ K ε (2 * Real.sqrt d) → ∀ v ∈ T.leaves,
      (v.length : ℝ) ≤ Real.log (1 / ε) / Real.log (2 * K / 3) + 1

/-- **Lemma 4.1 + (4.16), deterministic** (HA3 D2).  For every admissible path, well-formed
tree, threshold `a₀ ≥ 0`, continuous field and `ζ = δ^{3/2}`:
`log ∫_P e^{ζφ} ≥ ζ H_root - ζ ω(5ε) - δ² Σ_v θ(v) Σ_{u ≺ v} (δ^{-1/2} G_u - b_u)`, the length is
positive, and `θ` is a probability on the leaves. -/
def TreeInequality (d : ℕ) [NeZero d] : Prop :=
  ∀ γ : ℝ → Rd d, IsAdmissiblePath d γ → ∀ K : ℕ, 8 ≤ K → ∀ ε ∈ Ioo (0 : ℝ) 1,
    ∀ T : CutTree, T.WF γ K ε (2 * Real.sqrt d) → ∀ a₀ ≥ (0 : ℝ),
    ∀ φ : Rd d → ℝ, Continuous φ → ∀ δ > 0,
      0 < lfppLength (δ ^ (3 / 2 : ℝ)) φ γ ∧
      δ ^ (3 / 2 : ℝ) * T.H γ φ [] - δ ^ (3 / 2 : ℝ) * osc φ (5 * ε)
        - δ ^ 2 * ∑ v ∈ T.leaves, T.flow γ v * ∑ j ∈ Finset.range v.length,
            (δ ^ (-(1 / 2 : ℝ)) * T.G γ a₀ φ (v.take j) - T.bcost γ a₀ δ (v.take j)) ≤
        Real.log (lfppLength (δ ^ (3 / 2 : ℝ)) φ γ) ∧
      (∀ v ∈ T.leaves, 0 ≤ T.flow γ v) ∧ ∑ v ∈ T.leaves, T.flow γ v = 1

/-- **Lemma 4.2** with `c₀ = 1/500` (HA3 D4, F5): a good node has exactly `K` children and its
child polygon lies in the explicit good family `G_K` with threshold `a₀ = c₀ / K`. -/
def GoodNodeGeometry (d : ℕ) [NeZero d] : Prop :=
  ∀ γ : ℝ → Rd d, IsAdmissiblePath d γ → ∀ K : ℕ, 8 ≤ K → ∀ ε ∈ Ioo (0 : ℝ) 1,
    ∀ T : CutTree, T.WF γ K ε (2 * Real.sqrt d) → ∀ u ∈ T.nodes, 0 < T.nch u →
      T.A γ u ≤ 1 / 500 / K →
      T.nch u = K ∧ T.childPoly γ u ∈ goodFamily K (1 / 500 / K) (T.x γ u) (T.y γ u)

end HigherDimLFPP.Upper
