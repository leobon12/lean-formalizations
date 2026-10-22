import HigherDimLQGMetric.Routing.Lemma41MeshEdges

/-! Geometry of the family of routed lattice edges. -/

set_option autoImplicit false

noncomputable section

open Set HigherDimLFPP LQGMetric.MetricGeometry

namespace HigherDimLQGMetric

def lemma41_meshLeft {d : ℕ} {δ : ℝ} {S : Set (Rd d)}
    {T : SimpleGraph (Topology.meshVertices δ S)} (e : T.edgeSet) :
    Topology.meshVertices δ S := e.1.out.1

def lemma41_meshRight {d : ℕ} {δ : ℝ} {S : Set (Rd d)}
    {T : SimpleGraph (Topology.meshVertices δ S)} (e : T.edgeSet) :
    Topology.meshVertices δ S := e.1.out.2

def lemma41_meshRegL {d : ℕ} {δ : ℝ} {S : Set (Rd d)}
    {T : SimpleGraph (Topology.meshVertices δ S)}
    (ρ : Rd d × Rd d → ℝ) (hρ : IsCoordinate ρ) (e : T.edgeSet) :
    Set (MetricFunSpace ρ hρ.metric) :=
  MetricFunSpace.pt ρ hρ.metric ''
    routingRegion δ (Topology.latticePoint δ (lemma41_meshLeft e).1)
      (Topology.latticePoint δ (lemma41_meshRight e).1)

def lemma41_meshRegR {d : ℕ} {δ : ℝ} {S : Set (Rd d)}
    {T : SimpleGraph (Topology.meshVertices δ S)}
    (ρ : Rd d × Rd d → ℝ) (hρ : IsCoordinate ρ) (e : T.edgeSet) :
    Set (MetricFunSpace ρ hρ.metric) :=
  MetricFunSpace.pt ρ hρ.metric ''
    routingRegion δ (Topology.latticePoint δ (lemma41_meshRight e).1)
      (Topology.latticePoint δ (lemma41_meshLeft e).1)

def lemma41_meshBox {d : ℕ} {δ : ℝ} {S : Set (Rd d)}
    {T : SimpleGraph (Topology.meshVertices δ S)}
    (ρ : Rd d × Rd d → ℝ) (hρ : IsCoordinate ρ) (e : T.edgeSet) :
    Set (MetricFunSpace ρ hρ.metric) :=
  MetricFunSpace.pt ρ hρ.metric ''
    centralBox δ (Topology.latticePoint δ (lemma41_meshLeft e).1)
      (Topology.latticePoint δ (lemma41_meshRight e).1)

def lemma41_meshSource {d : ℕ} {δ : ℝ} {S : Set (Rd d)}
    {T : SimpleGraph (Topology.meshVertices δ S)} (e : T.edgeSet) (flip : Bool) :
    Topology.meshVertices δ S :=
  if flip then lemma41_meshRight e else lemma41_meshLeft e

def lemma41_meshTarget {d : ℕ} {δ : ℝ} {S : Set (Rd d)}
    {T : SimpleGraph (Topology.meshVertices δ S)} (e : T.edgeSet) (flip : Bool) :
    Topology.meshVertices δ S :=
  if flip then lemma41_meshLeft e else lemma41_meshRight e

def lemma41_meshRegion {d : ℕ} {δ : ℝ} {S : Set (Rd d)}
    {T : SimpleGraph (Topology.meshVertices δ S)}
    (ρ : Rd d × Rd d → ℝ) (hρ : IsCoordinate ρ)
    (e : T.edgeSet) (flip : Bool) : Set (MetricFunSpace ρ hρ.metric) :=
  MetricFunSpace.pt ρ hρ.metric ''
    routingRegion δ (Topology.latticePoint δ (lemma41_meshSource e flip).1)
      (Topology.latticePoint δ (lemma41_meshTarget e flip).1)

theorem lemma41_mesh_region_false {d : ℕ} {δ : ℝ} {S : Set (Rd d)}
    {T : SimpleGraph (Topology.meshVertices δ S)}
    (ρ : Rd d × Rd d → ℝ) (hρ : IsCoordinate ρ) (e : T.edgeSet) :
    lemma41_meshRegion ρ hρ e false = lemma41_meshRegL ρ hρ e := rfl

theorem lemma41_mesh_region_true {d : ℕ} {δ : ℝ} {S : Set (Rd d)}
    {T : SimpleGraph (Topology.meshVertices δ S)}
    (ρ : Rd d × Rd d → ℝ) (hρ : IsCoordinate ρ) (e : T.edgeSet) :
    lemma41_meshRegion ρ hρ e true = lemma41_meshRegR ρ hρ e := rfl

theorem lemma41_mesh_edge_ne {d : ℕ} {δ : ℝ} {S : Set (Rd d)}
    {T : SimpleGraph (Topology.meshVertices δ S)} (e : T.edgeSet) :
    lemma41_meshLeft e ≠ lemma41_meshRight e := by
  intro h
  have hadj : T.Adj (lemma41_meshLeft e) (lemma41_meshRight e) := by
    apply T.mem_edgeSet.mp
    simpa only [lemma41_meshLeft, lemma41_meshRight, e.1.out_eq] using e.2
  exact T.ne_of_adj hadj h

theorem lemma41_mesh_box_disjoint {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {S : Set (Rd d)} {T : SimpleGraph (Topology.meshVertices δ S)}
    (hT : T ≤ Topology.meshGraph δ S)
    (ρ : Rd d × Rd d → ℝ) (hρ : IsCoordinate ρ)
    (e f : T.edgeSet) (hef : e ≠ f) :
    Disjoint (lemma41_meshBox ρ hρ e) (lemma41_meshBox ρ hρ f) := by
  apply Set.disjoint_image_of_injective (by intro x y h; exact h)
  exact disjoint_centralBox_centralBox hδ
    (lemma41_tree_edge_adj hT e) (lemma41_tree_edge_adj hT f)
    (lemma41_tree_edges_ne e f hef)

theorem lemma41_mesh_box_regL_disjoint {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {S : Set (Rd d)} {T : SimpleGraph (Topology.meshVertices δ S)}
    (hT : T ≤ Topology.meshGraph δ S)
    (ρ : Rd d × Rd d → ℝ) (hρ : IsCoordinate ρ)
    (e f : T.edgeSet) (hef : e ≠ f) :
    Disjoint (lemma41_meshBox ρ hρ e) (lemma41_meshRegL ρ hρ f) := by
  apply Set.disjoint_image_of_injective (by intro x y h; exact h)
  exact (disjoint_routingRegion_centralBox hδ
    (lemma41_tree_edge_adj hT f) (lemma41_tree_edge_adj hT e)
    (lemma41_tree_edges_ne f e hef.symm)).symm

theorem lemma41_mesh_box_regR_disjoint {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {S : Set (Rd d)} {T : SimpleGraph (Topology.meshVertices δ S)}
    (hT : T ≤ Topology.meshGraph δ S)
    (ρ : Rd d × Rd d → ℝ) (hρ : IsCoordinate ρ)
    (e f : T.edgeSet) (hef : e ≠ f) :
    Disjoint (lemma41_meshBox ρ hρ e) (lemma41_meshRegR ρ hρ f) := by
  apply Set.disjoint_image_of_injective (by intro x y h; exact h)
  exact (disjoint_routingRegion_centralBox hδ
    (lemma41_tree_edge_adj hT f).symm (lemma41_tree_edge_adj hT e)
    (by simpa only [Sym2.eq_swap] using lemma41_tree_edges_ne f e hef.symm)).symm

theorem lemma41_mesh_regions_disjoint {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {S : Set (Rd d)} {T : SimpleGraph (Topology.meshVertices δ S)}
    (hT : T ≤ Topology.meshGraph δ S)
    (ρ : Rd d × Rd d → ℝ) (hρ : IsCoordinate ρ)
    (e f : T.edgeSet) (hef : e ≠ f) (be bf : Bool)
    (hsource : lemma41_meshSource e be ≠ lemma41_meshSource f bf) :
    Disjoint (lemma41_meshRegion ρ hρ e be)
      (lemma41_meshRegion ρ hρ f bf) := by
  have heAdj : (Topology.latticeGraph d).Adj
      (lemma41_meshSource e be).1 (lemma41_meshTarget e be).1 := by
    cases be with
    | false => exact lemma41_tree_edge_adj hT e
    | true => exact (lemma41_tree_edge_adj hT e).symm
  have hfAdj : (Topology.latticeGraph d).Adj
      (lemma41_meshSource f bf).1 (lemma41_meshTarget f bf).1 := by
    cases bf with
    | false => exact lemma41_tree_edge_adj hT f
    | true => exact (lemma41_tree_edge_adj hT f).symm
  have heEq : s((lemma41_meshSource e be).1, (lemma41_meshTarget e be).1) =
      s((lemma41_meshLeft e).1, (lemma41_meshRight e).1) := by
    cases be <;> simp [lemma41_meshSource, lemma41_meshTarget, Sym2.eq_swap]
  have hfEq : s((lemma41_meshSource f bf).1, (lemma41_meshTarget f bf).1) =
      s((lemma41_meshLeft f).1, (lemma41_meshRight f).1) := by
    cases bf <;> simp [lemma41_meshSource, lemma41_meshTarget, Sym2.eq_swap]
  have hne : s((lemma41_meshSource e be).1, (lemma41_meshTarget e be).1) ≠
      s((lemma41_meshSource f bf).1, (lemma41_meshTarget f bf).1) := by
    rw [heEq, hfEq]
    exact lemma41_tree_edges_ne e f hef
  have hsource' : (lemma41_meshSource e be).1 ≠ (lemma41_meshSource f bf).1 := by
    intro h
    exact hsource (Subtype.ext h)
  apply Set.disjoint_image_of_injective (by intro x y h; exact h)
  exact lemma41_disjoint_routing_regions hδ heAdj hfAdj hne hsource'

theorem lemma41_mesh_region_subset_star {d : ℕ} {δ : ℝ}
    {S : Set (Rd d)} {T : SimpleGraph (Topology.meshVertices δ S)}
    (hT : T ≤ Topology.meshGraph δ S)
    (ρ : Rd d × Rd d → ℝ) (hρ : IsCoordinate ρ)
    (e : T.edgeSet) (b : Bool) :
    lemma41_meshRegion ρ hρ e b ⊆
      MetricFunSpace.pt ρ hρ.metric '' meshStar δ (lemma41_meshSource e b).1 := by
  have hAdj : (Topology.latticeGraph d).Adj
      (lemma41_meshSource e b).1 (lemma41_meshTarget e b).1 := by
    cases b with
    | false => exact lemma41_tree_edge_adj hT e
    | true => exact (lemma41_tree_edge_adj hT e).symm
  exact image_mono (routingRegion_subset_meshStar δ hAdj)

theorem lemma41_mesh_box_subset_stars {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {S : Set (Rd d)} {T : SimpleGraph (Topology.meshVertices δ S)}
    (hT : T ≤ Topology.meshGraph δ S)
    (ρ : Rd d × Rd d → ℝ) (hρ : IsCoordinate ρ)
    (e : T.edgeSet) :
    lemma41_meshBox ρ hρ e ⊆
      (MetricFunSpace.pt ρ hρ.metric '' meshStar δ (lemma41_meshLeft e).1) ∩
      (MetricFunSpace.pt ρ hρ.metric '' meshStar δ (lemma41_meshRight e).1) := by
  intro x hx
  exact ⟨(image_mono (centralBox_subset_meshStar hδ (lemma41_tree_edge_adj hT e))) hx,
    (image_mono (centralBox_subset_meshStar' hδ (lemma41_tree_edge_adj hT e))) hx⟩

end HigherDimLQGMetric
