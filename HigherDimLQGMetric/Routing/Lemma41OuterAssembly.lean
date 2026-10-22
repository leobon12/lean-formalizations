import HigherDimLQGMetric.Routing.Lemma41OuterFamily

/-! Finite assembly of the routed pieces in the annular coordinate. -/

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open Set Topology HigherDimLFPP LQGMetric.MetricGeometry BoundedContinuousFunction
open scoped ENNReal

namespace HigherDimLQGMetric

theorem lemma41_outer_family_partition {d : ℕ} (hd : 3 ≤ d)
    {δ : ℝ} (hδ : 0 < δ) (hsmall : δ ≤ 1 / (4 * Real.sqrt d))
    {T : SimpleGraph (Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2))}
    (hT : T ≤ Topology.meshGraph δ (Metric.sphere (0 : Rd d) 2))
    (hTconn : T.Connected)
    (ρ : (configOuter d) × (configOuter d) → ℝ) (hρ : IsCoordinate ρ)
    (Cost : MetricFunSpace ρ hρ.metric → MetricFunSpace ρ hρ.metric → ℝ≥0∞)
    (a₁ c₃ : ℝ)
    (P : ∀ e : T.edgeSet, Lemma41LocalPiece
      (lemma41_outerMeshPoint (by omega : 1 ≤ d) hδ hsmall ρ hρ (lemma41_meshLeft e))
      (lemma41_outerMeshPoint (by omega : 1 ≤ d) hδ hsmall ρ hρ (lemma41_meshRight e))
      (lemma41_outerMeshRegL ρ hρ e) (lemma41_outerMeshRegR ρ hρ e)
      (lemma41_outerMeshBox ρ hρ e) Cost a₁ c₃) :
    let C : Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2) →
        Set (MetricFunSpace ρ hρ.metric) :=
      fun v => ⋃ e : T.edgeSet,
        lemma41_side lemma41_meshLeft lemma41_meshRight
          (fun e => (P e).L) (fun e => (P e).R) e v
    (∀ v, IsCompact (C v) ∧ IsConnected (C v) ∧
      lemma41_outerMeshPoint (by omega : 1 ≤ d) hδ hsmall ρ hρ v ∈ C v ∧
      C v ⊆ lemma41_outerMeshStar ρ hρ v) ∧
    (∀ v w, v ≠ w → Disjoint (C v) (C w)) ∧
    (⋃ e, (P e).K) \ (⋃ e, (P e).σ '' Ioo (0 : ℝ) 1) = ⋃ v, C v := by
  classical
  letI : Fintype (Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2)) :=
    (routingMesh_finite hδ).fintype
  letI : Nontrivial (Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2)) :=
    lemma41_routing_mesh_nontrivial (by omega : 1 ≤ d) hδ hsmall
  letI : Fintype T.edgeSet := Fintype.ofFinite _
  let left : T.edgeSet → Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2) := lemma41_meshLeft
  let right : T.edgeSet → Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2) := lemma41_meshRight
  let p : Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2) →
      MetricFunSpace ρ hρ.metric :=
    lemma41_outerMeshPoint (by omega : 1 ≤ d) hδ hsmall ρ hρ
  let C : Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2) →
      Set (MetricFunSpace ρ hρ.metric) :=
    fun v => ⋃ e : T.edgeSet,
      lemma41_side left right (fun e => (P e).L) (fun e => (P e).R) e v
  have hpart := lemma41_family_partition left right
    (fun e => lemma41_mesh_edge_ne e) p
    (lemma41_outerMeshRegL ρ hρ) (lemma41_outerMeshRegR ρ hρ)
    (lemma41_outerMeshBox ρ hρ) Cost a₁ c₃ P
    (fun v => lemma41_tree_incident_out hTconn v)
    (fun e f v w hef hvw => lemma41_outer_family_cross hδ hT
      (by omega : 1 ≤ d) hsmall ρ hρ Cost a₁ c₃ P e f v w hef hvw)
    (fun e f v hef => lemma41_outer_family_box_side hδ hT
      (by omega : 1 ≤ d) hsmall ρ hρ Cost a₁ c₃ P e f v hef)
  change (∀ v, IsCompact (C v) ∧ IsConnected (C v) ∧ p v ∈ C v) ∧
    (∀ v w, v ≠ w → Disjoint (C v) (C w)) ∧
    (⋃ e, (P e).K) \ (⋃ e, (P e).σ '' Ioo (0 : ℝ) 1) = ⋃ v, C v at hpart
  refine ⟨?_, hpart.2.1, hpart.2.2⟩
  intro v
  refine ⟨(hpart.1 v).1, (hpart.1 v).2.1, (hpart.1 v).2.2, ?_⟩
  intro x hx
  obtain ⟨e, he⟩ := Set.mem_iUnion.mp hx
  exact lemma41_outer_family_side_star hT (by omega : 1 ≤ d) hδ hsmall
    ρ hρ Cost a₁ c₃ P e v he

theorem lemma41_outer_family_graph {d : ℕ} (hd : 3 ≤ d)
    {δ : ℝ} (hδ : 0 < δ) (hsmall : δ ≤ 1 / (4 * Real.sqrt d))
    {T : SimpleGraph (Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2))}
    (hT : T ≤ Topology.meshGraph δ (Metric.sphere (0 : Rd d) 2))
    (hTconn : T.Connected)
    (ρ : (configOuter d) × (configOuter d) → ℝ) (hρ : IsCoordinate ρ)
    (Cost : MetricFunSpace ρ hρ.metric → MetricFunSpace ρ hρ.metric → ℝ≥0∞)
    (a₁ c₃ : ℝ)
    (P : ∀ e : T.edgeSet, Lemma41LocalPiece
      (lemma41_outerMeshPoint (by omega : 1 ≤ d) hδ hsmall ρ hρ (lemma41_meshLeft e))
      (lemma41_outerMeshPoint (by omega : 1 ≤ d) hδ hsmall ρ hρ (lemma41_meshRight e))
      (lemma41_outerMeshRegL ρ hρ e) (lemma41_outerMeshRegR ρ hρ e)
      (lemma41_outerMeshBox ρ hρ e) Cost a₁ c₃) :
    IsFiniteRectGraph (⋃ e, (P e).K) ∧
      (⋃ e, (P e).K) ⊆ lemma41_outerImage ρ hρ (meshCollector d δ) ∧
      (∀ v : Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2),
        lemma41_outerMeshPoint (by omega : 1 ≤ d) hδ hsmall ρ hρ v ∈
          ⋃ e, (P e).K) := by
  classical
  letI : Fintype (Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2)) :=
    (routingMesh_finite hδ).fintype
  letI : Nontrivial (Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2)) :=
    lemma41_routing_mesh_nontrivial (by omega : 1 ≤ d) hδ hsmall
  letI : Fintype T.edgeSet := Fintype.ofFinite _
  let K : T.edgeSet → Set (MetricFunSpace ρ hρ.metric) := fun e => (P e).K
  let p : Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2) →
      MetricFunSpace ρ hρ.metric :=
    lemma41_outerMeshPoint (by omega : 1 ≤ d) hδ hsmall ρ hρ
  have hinc : ∀ v : Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2),
      ∃ e : T.edgeSet, v ∈ (e : Sym2 _) := lemma41_tree_incident hTconn
  have hp : ∀ (e : T.edgeSet) (v : Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2)),
      v ∈ (e : Sym2 _) → p v ∈ K e := by
    intro e v hv
    rw [← e.1.out_eq] at hv
    rcases Sym2.mem_iff.mp hv with hv | hv
    · subst v
      change p (lemma41_meshLeft e) ∈ (P e).K
      rw [(P e).graph_eq]
      exact Or.inl (Or.inl (P e).pLmem)
    · subst v
      change p (lemma41_meshRight e) ∈ (P e).K
      rw [(P e).graph_eq]
      exact Or.inr (P e).pRmem
  have hconn : IsConnected (⋃ e, K e) :=
    lemma41_connected_edge_union_of_vertices T hTconn hinc p K
      (fun e => (P e).graph) hp
  have hgraph : IsFiniteRectGraph (⋃ e, K e) :=
    lemma41_finite_union_graph K (fun e => (P e).graph) hconn
  have hsub : (⋃ e, K e) ⊆ lemma41_outerImage ρ hρ (meshCollector d δ) := by
    intro x hx
    obtain ⟨e, he⟩ := Set.mem_iUnion.mp hx
    change x ∈ (P e).K at he
    rw [(P e).graph_eq] at he
    have heAdj := lemma41_tree_edge_adj hT e
    rcases he with (heL | heM) | heR
    · exact (lemma41_outerImage_mono ρ hρ
        (routingRegion_subset_meshCollector (by omega : 1 ≤ d) hδ
          (lemma41_meshLeft e).property heAdj)) ((P e).Lregion heL)
    · exact (lemma41_outerImage_mono ρ hρ
        (centralBox_subset_meshCollector (by omega : 1 ≤ d) hδ
          (lemma41_meshLeft e).property heAdj)) ((P e).σbox heM)
    · exact (lemma41_outerImage_mono ρ hρ
        (routingRegion_subset_meshCollector (by omega : 1 ≤ d) hδ
          (lemma41_meshRight e).property heAdj.symm)) ((P e).Rregion heR)
  refine ⟨hgraph, hsub, ?_⟩
  intro v
  obtain ⟨e, he⟩ := hinc v
  exact Set.mem_iUnion_of_mem e (hp e v he)

theorem lemma41_outer_family_forcing {d : ℕ} (hd : 3 ≤ d)
    {δ : ℝ} (hδ : 0 < δ) (hsmall : δ ≤ 1 / (4 * Real.sqrt d))
    {T : SimpleGraph (Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2))}
    (hT : T ≤ Topology.meshGraph δ (Metric.sphere (0 : Rd d) 2))
    (hTconn : T.Connected)
    (ρ : (configOuter d) × (configOuter d) → ℝ) (hρ : IsCoordinate ρ)
    (Cost : MetricFunSpace ρ hρ.metric → MetricFunSpace ρ hρ.metric → ℝ≥0∞)
    (a₁ c₃ : ℝ)
    (P : ∀ e : T.edgeSet, Lemma41LocalPiece
      (lemma41_outerMeshPoint (by omega : 1 ≤ d) hδ hsmall ρ hρ (lemma41_meshLeft e))
      (lemma41_outerMeshPoint (by omega : 1 ≤ d) hδ hsmall ρ hρ (lemma41_meshRight e))
      (lemma41_outerMeshRegL ρ hρ e) (lemma41_outerMeshRegR ρ hρ e)
      (lemma41_outerMeshBox ρ hρ e) Cost a₁ c₃)
    {b : ℝ} (hb : 0 < b)
    (hdiam : ∀ v : Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2),
      ∀ x ∈ lemma41_outerMeshStar ρ hρ v,
      ∀ y ∈ lemma41_outerMeshStar ρ hρ v, dist x y < b / 8)
    {Tlen ℓ : ℝ} (hTlen : 0 ≤ Tlen) (hℓ0 : 0 ≤ ℓ) (hℓT : ℓ ≤ Tlen)
    (Q : Icc (0 : ℝ) Tlen →ᵇ MetricFunSpace ρ hρ.metric)
    (hQK : ∀ u ∈ Icc (0 : ℝ) ℓ,
      Set.IccExtend hTlen Q u ∈ ⋃ e, (P e).K)
    (hQi : InjOn (Set.IccExtend hTlen Q) (Icc 0 ℓ))
    (hsep : b / 4 ≤ dist (Set.IccExtend hTlen Q 0)
      (Set.IccExtend hTlen Q ℓ)) :
    ∃ e : T.edgeSet,
      TraversesMarkedArc hℓT Q (P e).σ ∨
        TraversesMarkedArc hℓT Q (fun r => (P e).σ (1 - r)) := by
  classical
  letI : Fintype (Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2)) :=
    (routingMesh_finite hδ).fintype
  letI : Nontrivial (Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2)) :=
    lemma41_routing_mesh_nontrivial (by omega : 1 ≤ d) hδ hsmall
  letI : Fintype T.edgeSet := Fintype.ofFinite _
  let left : T.edgeSet → Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2) := lemma41_meshLeft
  let right : T.edgeSet → Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2) := lemma41_meshRight
  let p : Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2) →
      MetricFunSpace ρ hρ.metric :=
    lemma41_outerMeshPoint (by omega : 1 ≤ d) hδ hsmall ρ hρ
  let C : Topology.meshVertices δ (Metric.sphere (0 : Rd d) 2) →
      Set (MetricFunSpace ρ hρ.metric) :=
    fun v => ⋃ e : T.edgeSet,
      lemma41_side left right (fun e => (P e).L) (fun e => (P e).R) e v
  let K : Set (MetricFunSpace ρ hρ.metric) := ⋃ e, (P e).K
  let σ : T.edgeSet → ℝ → MetricFunSpace ρ hρ.metric := fun e => (P e).σ
  have hpart := lemma41_outer_family_partition hd hδ hsmall hT hTconn ρ hρ Cost a₁ c₃ P
  change (∀ v, IsCompact (C v) ∧ IsConnected (C v) ∧
      p v ∈ C v ∧ C v ⊆ lemma41_outerMeshStar ρ hρ v) ∧
    (∀ v w, v ≠ w → Disjoint (C v) (C w)) ∧
    K \ (⋃ e, σ e '' Ioo (0 : ℝ) 1) = ⋃ v, C v at hpart
  have hboxside : ∀ e f v, e ≠ f →
      Disjoint (lemma41_outerMeshBox ρ hρ e)
        (lemma41_side left right (fun e => (P e).L) (fun e => (P e).R) f v) := by
    intro e f v hef
    exact lemma41_outer_family_box_side hδ hT (by omega : 1 ≤ d) hsmall
      ρ hρ Cost a₁ c₃ P e f v hef
  have hσC : ∀ e v u, u ∈ Icc (0 : ℝ) 1 → σ e u ∈ C v →
      (u = 0 ∧ v = left e) ∨ (u = 1 ∧ v = right e) := by
    exact lemma41_family_mark_contacts left right p
      (lemma41_outerMeshRegL ρ hρ) (lemma41_outerMeshRegR ρ hρ)
      (lemma41_outerMeshBox ρ hρ) Cost a₁ c₃ P hboxside
  have hσσ : ∀ e f, e ≠ f →
      Disjoint (σ e '' Icc (0 : ℝ) 1) (σ f '' Icc (0 : ℝ) 1) := by
    apply lemma41_family_marks_disjoint left right p
      (lemma41_outerMeshRegL ρ hρ) (lemma41_outerMeshRegR ρ hρ)
      (lemma41_outerMeshBox ρ hρ) Cost a₁ c₃ P
    intro e f hef
    exact lemma41_outer_boxes_disjoint hδ hT ρ hρ e f hef
  have hgraph : K = (⋃ v, C v) ∪ (⋃ e, σ e '' Icc (0 : ℝ) 1) := by
    exact lemma41_family_graph_eq left right (fun e => lemma41_mesh_edge_ne e) p
      (lemma41_outerMeshRegL ρ hρ) (lemma41_outerMeshRegR ρ hρ)
      (lemma41_outerMeshBox ρ hρ) Cost a₁ c₃ P
  have hσstar : ∀ e, σ e '' Icc (0 : ℝ) 1 ⊆
      lemma41_outerMeshStar ρ hρ (left e) ∩
      lemma41_outerMeshStar ρ hρ (right e) := by
    intro e
    exact (P e).σbox.trans (lemma41_outer_box_subset_stars hδ hT ρ hρ e)
  exact lemma41_forcing_of_components K C (lemma41_outerMeshStar ρ hρ) left right σ
    (fun e => lemma41_mesh_edge_ne e)
    (fun v => (hpart.1 v).1) hpart.2.1
    (fun e => (P e).σcontinuous) (fun e => (P e).σinjective)
    hσC hσσ (fun v => (hpart.1 v).2.2.2) hσstar hgraph
    hb hdiam hTlen hℓ0 hℓT Q hQK hQi hsep

end HigherDimLQGMetric
