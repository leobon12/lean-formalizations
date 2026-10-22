import HigherDimLQGMetric.Routing.Mesh
import HigherDimLQGMetric.Core.Defs

/-!
# The mesh of `∂B₂`, its spanning tree and the collector ([S] Lemma 4.1′, MA1 A16, (G4))

Packet S2a. Source: planning audit `planning/audits/MA1-sections-1-4.md`, Details (a) **A16**,
"Geometry (deterministic)"; blueprint Part A §4 (`blueprint/sections/s4-routing.tex`), Definition
`def:mesh`, Lemma `lem:mesh-connected` and Lemma `lem:mesh-geometry` (G4).

`S = ∂B₂ = sphere 0 2`. The vertex set `𝒱 = meshVertices δ S` (corners of the closed cubes of
`δℤ^d` meeting `S`) and the mesh graph `(𝒱, ℰ) = meshGraph δ S` are packet M4's
(`HigherDimLQGMetric/Topology/NonSepMesh.lean`); here:

* **Lemma M** for `S = ∂B₂` (`routingMesh_connected`, `d ≥ 2`), finiteness of `𝒱`
  (`routingMesh_finite`), a spanning tree (`exists_routingTree`), tree edges are lattice edges
  (`latticeGraph_adj_of_le_meshGraph`) of length `δ`, distinct tree edges are distinct lattice
  edges (`sym2_val_ne`).
* The collector `meshCollector d δ = V = {x : dist(x, S) < 3√d δ}` and (G4): every vertex is within
  `√d δ` of `S` (`exists_mem_sphere_dist_le_of_mem_meshVertices`); `N_v`, `T_e`, `Box_e`, `Ω_{v,e}`,
  `Star_v ⊆ V` for `v ∈ 𝒱` (`meshStar_subset_meshCollector` etc.);
  `V̄ ⊆ Ā_{2-3√dδ, 2+3√dδ}` (`closure_meshCollector_subset_annCl`); **smallness condition**
  `0 < δ ≤ 1/(4√d)` gives `V̄ ⊆ A_{1,3}` (`closure_meshCollector_subset_ann_one_three`), `V̄`
  compact (`isCompact_closure_meshCollector`), i.e. `V ⋐ A_{1,3}`; every point of `V̄` is within
  `4√d δ` of a vertex (`exists_meshVertex_dist_le`).
-/

set_option autoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set Metric
open HigherDimLFPP (Rd)
open HigherDimLQGMetric.Topology (latticePoint latticeGraph latticeCube IsCubeCorner meshVertices
  meshGraph floorCorner mem_latticeCube_floorCorner meshGraph_connected_sphere
  meshVertices_sphere_finite exists_isTree_le_meshGraph_sphere)
open Routing

variable {d : ℕ}

/-! ### Lattice cubes -/

/-- Two points of one closed lattice cube are at distance `≤ √d δ`. -/
lemma dist_le_of_mem_latticeCube {δ : ℝ} (hδ : 0 ≤ δ) {k : Fin d → ℤ} {x y : Rd d}
    (hx : x ∈ latticeCube δ k) (hy : y ∈ latticeCube δ k) : dist x y ≤ Real.sqrt d * δ := by
  rw [EuclideanSpace.dist_eq]
  have h : ∑ i, dist (x i) (y i) ^ 2 ≤ (d : ℝ) * δ ^ 2 := by
    calc ∑ i, dist (x i) (y i) ^ 2 ≤ ∑ _i : Fin d, δ ^ 2 := by
          apply Finset.sum_le_sum
          intro i _
          obtain ⟨hx1, hx2⟩ := hx i
          obtain ⟨hy1, hy2⟩ := hy i
          have e : ((k i : ℝ) + 1) * δ = (k i : ℝ) * δ + δ := by ring
          rw [e] at hx2 hy2
          have habs : |x i - y i| ≤ δ := abs_le.2 ⟨by linarith, by linarith⟩
          rw [Real.dist_eq]
          exact pow_le_pow_left₀ (abs_nonneg _) habs 2
      _ = (d : ℝ) * δ ^ 2 := by simp
  calc Real.sqrt (∑ i, dist (x i) (y i) ^ 2) ≤ Real.sqrt ((d : ℝ) * δ ^ 2) := Real.sqrt_le_sqrt h
    _ = Real.sqrt d * δ := by rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq hδ]

/-- A corner of a lattice cube lies in the cube. -/
lemma latticePoint_mem_latticeCube {δ : ℝ} (hδ : 0 ≤ δ) {k m : Fin d → ℤ}
    (h : IsCubeCorner k m) : latticePoint δ m ∈ latticeCube δ k := by
  intro i
  rw [Routing.latticePoint_apply]
  rcases h i with hi | hi <;> rw [hi] <;> push_cast <;> constructor <;> nlinarith

/-- Every vertex of the mesh of `S` is within `√d δ` of a point of `S`. -/
theorem exists_mem_sphere_dist_le_of_mem_meshVertices {δ : ℝ} (hδ : 0 ≤ δ) {S : Set (Rd d)}
    {m : Fin d → ℤ} (hm : m ∈ meshVertices δ S) :
    ∃ p ∈ S, dist (latticePoint δ m) p ≤ Real.sqrt d * δ := by
  obtain ⟨k, hkm, p, hpk, hpS⟩ := hm
  exact ⟨p, hpS, dist_le_of_mem_latticeCube hδ (latticePoint_mem_latticeCube hδ hkm) hpk⟩

/-- The floor corner of a point of `S` is a mesh vertex. -/
lemma floorCorner_mem_meshVertices {δ : ℝ} (hδ : 0 < δ) {S : Set (Rd d)} {p : Rd d}
    (hp : p ∈ S) : floorCorner δ p ∈ meshVertices δ S :=
  ⟨floorCorner δ p, fun _ => Or.inl rfl, p, mem_latticeCube_floorCorner hδ p, hp⟩

/-- A point is within `√d δ` of (the lattice point of) its floor corner. -/
lemma dist_latticePoint_floorCorner_le {δ : ℝ} (hδ : 0 < δ) (p : Rd d) :
    dist p (latticePoint δ (floorCorner δ p)) ≤ Real.sqrt d * δ :=
  dist_le_of_mem_latticeCube hδ.le (mem_latticeCube_floorCorner hδ p)
    (latticePoint_mem_latticeCube hδ.le fun _ => Or.inl rfl)

/-! ### Lemma M and the spanning tree for `S = ∂B₂` -/

/-- **Lemma M (A16)** for `S = ∂B₂`, `d ≥ 2`: the mesh graph `(𝒱, ℰ)` is connected. -/
theorem routingMesh_connected (hd : 2 ≤ d) {δ : ℝ} (hδ : 0 < δ) :
    (meshGraph δ (sphere (0 : Rd d) 2)).Connected :=
  meshGraph_connected_sphere hd hδ 0 (by norm_num)

/-- The vertex set `𝒱` of the mesh of `∂B₂` is finite. -/
theorem routingMesh_finite {δ : ℝ} (hδ : 0 < δ) : (meshVertices δ (sphere (0 : Rd d) 2)).Finite :=
  meshVertices_sphere_finite hδ 0 2

/-- A spanning tree `𝒯 ⊆ ℰ` of the mesh of `∂B₂` (`d ≥ 2`). -/
theorem exists_routingTree (hd : 2 ≤ d) {δ : ℝ} (hδ : 0 < δ) :
    ∃ T ≤ meshGraph δ (sphere (0 : Rd d) 2), T.IsTree :=
  exists_isTree_le_meshGraph_sphere hd hδ 0 (by norm_num)

/-- Edges of a subgraph of the mesh graph (e.g. of the spanning tree) are lattice edges. -/
theorem latticeGraph_adj_of_le_meshGraph {δ : ℝ} {S : Set (Rd d)}
    {T : SimpleGraph (meshVertices δ S)} (hT : T ≤ meshGraph δ S) {a b : meshVertices δ S}
    (h : T.Adj a b) : (latticeGraph d).Adj a.1 b.1 :=
  hT h

/-- Distinct edges of a graph on the mesh vertices are distinct lattice edges. -/
theorem Routing.sym2_val_ne {δ : ℝ} {S : Set (Rd d)} {a b a' b' : meshVertices δ S}
    (h : s(a, b) ≠ s(a', b')) : s(a.1, b.1) ≠ s(a'.1, b'.1) := by
  intro h'
  apply h
  rcases Sym2.eq_iff.1 h' with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [Subtype.ext h1, Subtype.ext h2]
  · rw [Subtype.ext h1, Subtype.ext h2]
    exact Sym2.eq_swap

/-! ### The collector -/

/-- The collector `V = {x : dist(x, ∂B₂) < 3√d δ}` (A16), as the `3√dδ`-thickening of `∂B₂`
(`mem_meshCollector_iff`). -/
def meshCollector (d : ℕ) (δ : ℝ) : Set (Rd d) :=
  thickening (3 * Real.sqrt d * δ) (sphere (0 : Rd d) 2)

lemma isOpen_meshCollector (d : ℕ) (δ : ℝ) : IsOpen (meshCollector d δ) := isOpen_thickening

lemma mem_meshCollector_iff (hd : 1 ≤ d) {δ : ℝ} {x : Rd d} :
    x ∈ meshCollector d δ ↔ infDist x (sphere (0 : Rd d) 2) < 3 * Real.sqrt d * δ := by
  have : Nontrivial (Rd d) :=
    Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [finrank_euclideanSpace_fin]; omega)
  exact mem_thickening_iff_infDist_lt (NormedSpace.sphere_nonempty.2 (by norm_num))

lemma sphere_subset_meshCollector (hd : 1 ≤ d) {δ : ℝ} (hδ : 0 < δ) :
    sphere (0 : Rd d) 2 ⊆ meshCollector d δ := by
  have : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast hd)
  exact self_subset_thickening (by positivity) _

/-- Points within `2√d δ` of a vertex lie in the collector. -/
theorem ball_subset_meshCollector {δ : ℝ} (hδ : 0 ≤ δ) {m : Fin d → ℤ}
    (hm : m ∈ meshVertices δ (sphere (0 : Rd d) 2)) :
    ball (latticePoint δ m) (2 * Real.sqrt d * δ) ⊆ meshCollector d δ := by
  intro x hx
  obtain ⟨p, hp, hmp⟩ := exists_mem_sphere_dist_le_of_mem_meshVertices hδ hm
  refine mem_thickening_iff.2 ⟨p, hp, ?_⟩
  have h1 := mem_ball.1 hx
  have h2 := dist_triangle x (latticePoint δ m) p
  linarith

/-- **(G4)** `Star_v ⊆ V` for every vertex `v ∈ 𝒱` (`d ≥ 1`). -/
theorem meshStar_subset_meshCollector (hd : 1 ≤ d) {δ : ℝ} (hδ : 0 < δ) {m : Fin d → ℤ}
    (hm : m ∈ meshVertices δ (sphere (0 : Rd d) 2)) : meshStar δ m ⊆ meshCollector d δ := by
  have hsq : 1 ≤ Real.sqrt d := Real.one_le_sqrt.2 (by exact_mod_cast hd)
  refine (meshStar_subset_ball hδ m).trans ((ball_subset_ball ?_).trans
    (ball_subset_meshCollector hδ.le hm))
  nlinarith

/-- **(G4)** `N_v ⊆ V` for `v ∈ 𝒱`. -/
theorem vertBall_subset_meshCollector (hd : 1 ≤ d) {δ : ℝ} (hδ : 0 < δ) {m : Fin d → ℤ}
    (hm : m ∈ meshVertices δ (sphere (0 : Rd d) 2)) :
    vertBall δ (latticePoint δ m) ⊆ meshCollector d δ :=
  (vertBall_subset_meshStar δ m).trans (meshStar_subset_meshCollector hd hδ hm)

/-- **(G4)** `T_e ⊆ V` for a lattice edge `e = {v, w}` with `v ∈ 𝒱`. -/
theorem edgeTube_subset_meshCollector (hd : 1 ≤ d) {δ : ℝ} (hδ : 0 < δ) {m m' : Fin d → ℤ}
    (hm : m ∈ meshVertices δ (sphere (0 : Rd d) 2)) (h : (latticeGraph d).Adj m m') :
    edgeTube δ (latticePoint δ m) (latticePoint δ m') ⊆ meshCollector d δ :=
  (edgeTube_subset_meshStar δ h).trans (meshStar_subset_meshCollector hd hδ hm)

/-- **(G4)** `Box_e ⊆ V` for a lattice edge `e = {v, w}` with `v ∈ 𝒱`. -/
theorem centralBox_subset_meshCollector (hd : 1 ≤ d) {δ : ℝ} (hδ : 0 < δ) {m m' : Fin d → ℤ}
    (hm : m ∈ meshVertices δ (sphere (0 : Rd d) 2)) (h : (latticeGraph d).Adj m m') :
    centralBox δ (latticePoint δ m) (latticePoint δ m') ⊆ meshCollector d δ :=
  (centralBox_subset_meshStar hδ h).trans (meshStar_subset_meshCollector hd hδ hm)

/-- **(G4)** `Ω_{v,e} ⊆ V` for a lattice edge `e = (v, w)` with `v ∈ 𝒱`. -/
theorem routingRegion_subset_meshCollector (hd : 1 ≤ d) {δ : ℝ} (hδ : 0 < δ) {m m' : Fin d → ℤ}
    (hm : m ∈ meshVertices δ (sphere (0 : Rd d) 2)) (h : (latticeGraph d).Adj m m') :
    routingRegion δ (latticePoint δ m) (latticePoint δ m') ⊆ meshCollector d δ :=
  (routingRegion_subset_meshStar δ h).trans (meshStar_subset_meshCollector hd hδ hm)

/-- **(G4)** `V̄ ⊆ Ā_{2-3√dδ, 2+3√dδ}`. -/
theorem closure_meshCollector_subset_annCl {δ : ℝ} (hδ : 0 ≤ δ) :
    closure (meshCollector d δ) ⊆
      annCl 0 (2 - 3 * Real.sqrt d * δ) (2 + 3 * Real.sqrt d * δ) := by
  have hr : 0 ≤ 3 * Real.sqrt d * δ := by positivity
  intro x hx
  have hx' := closure_thickening_subset_cthickening _ _ hx
  rw [(isCompact_sphere (0 : Rd d) 2).cthickening_eq_biUnion_closedBall hr] at hx'
  obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.1 hx'
  have hp' : ‖p‖ = 2 := mem_sphere_zero_iff_norm.1 hp
  have hxp' : ‖x - p‖ ≤ 3 * Real.sqrt d * δ := by rw [← dist_eq_norm]; exact mem_closedBall.1 hxp
  have h1 : ‖x‖ ≤ ‖p‖ + ‖x - p‖ := by
    calc ‖x‖ = ‖p + (x - p)‖ := by congr 1; abel
      _ ≤ ‖p‖ + ‖x - p‖ := norm_add_le _ _
  have h2 : ‖p‖ ≤ ‖x‖ + ‖x - p‖ := by
    calc ‖p‖ = ‖x - (x - p)‖ := by congr 1; abel
      _ ≤ ‖x‖ + ‖x - p‖ := norm_sub_le _ _
  simp only [annCl, mem_ofPred_eq, sub_zero]
  constructor <;> linarith

/-- `V̄ ⊆ A_{a,b}` whenever `a < 2 - 3√dδ` and `2 + 3√dδ < b`. -/
theorem closure_meshCollector_subset_ann {δ a b : ℝ} (hδ : 0 ≤ δ) (ha : a < 2 - 3 * Real.sqrt d * δ)
    (hb : 2 + 3 * Real.sqrt d * δ < b) : closure (meshCollector d δ) ⊆ ann 0 a b := by
  intro x hx
  obtain ⟨h1, h2⟩ := closure_meshCollector_subset_annCl hδ hx
  exact ⟨by linarith, by linarith⟩

/-- **Smallness condition.** For `δ ≤ 1/(4√d)`: `3√d δ ≤ 3/4`. -/
lemma Routing.three_sqrt_mul_le {δ : ℝ} (hδ' : δ ≤ 1 / (4 * Real.sqrt d)) :
    3 * Real.sqrt d * δ ≤ 3 / 4 := by
  rcases (Real.sqrt_nonneg (d : ℝ)).eq_or_lt with h | h
  · rw [← h]
    norm_num
  · have : Real.sqrt d * δ ≤ 1 / 4 := by
      calc Real.sqrt d * δ ≤ Real.sqrt d * (1 / (4 * Real.sqrt d)) :=
            mul_le_mul_of_nonneg_left hδ' h.le
        _ = 1 / 4 := by field_simp
    linarith

/-- **(G4), `V ⋐ A_{1,3}`.** Under the smallness condition `0 < δ ≤ 1/(4√d)`, `V̄ ⊆ A_{1,3}`. -/
theorem closure_meshCollector_subset_ann_one_three {δ : ℝ} (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / (4 * Real.sqrt d)) : closure (meshCollector d δ) ⊆ ann 0 1 3 := by
  have := three_sqrt_mul_le (d := d) hδ'
  exact closure_meshCollector_subset_ann hδ.le (by linarith) (by linarith)

/-- `V̄` is compact. -/
theorem isCompact_closure_meshCollector (d : ℕ) (δ : ℝ) : IsCompact (closure (meshCollector d δ)) :=
  isCompact_of_isClosed_isBounded isClosed_closure
    (isBounded_sphere.thickening.closure)

/-- **(G4), covering bound.** Every point of `V̄` is within `4√d δ` of a vertex of the mesh. -/
theorem exists_meshVertex_dist_le {δ : ℝ} (hδ : 0 < δ) {x : Rd d}
    (hx : x ∈ closure (meshCollector d δ)) :
    ∃ m ∈ meshVertices δ (sphere (0 : Rd d) 2),
      dist x (latticePoint δ m) ≤ 4 * Real.sqrt d * δ := by
  have hr : 0 ≤ 3 * Real.sqrt d * δ := by positivity
  have hx' := closure_thickening_subset_cthickening _ _ hx
  rw [(isCompact_sphere (0 : Rd d) 2).cthickening_eq_biUnion_closedBall hr] at hx'
  obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.1 hx'
  refine ⟨floorCorner δ p, floorCorner_mem_meshVertices hδ hp, ?_⟩
  have h1 := mem_closedBall.1 hxp
  have h2 := dist_latticePoint_floorCorner_le hδ p
  have h3 := dist_triangle x p (latticePoint δ (floorCorner δ p))
  linarith

end HigherDimLQGMetric
