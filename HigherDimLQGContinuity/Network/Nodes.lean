import HigherDimLQGContinuity.Network.Diameter

/-! # Closed nodes of the label network -/

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open Set Metric
open HigherDimLFPP (Rd)

namespace HigherDimLQGContinuity

variable {μ ν r c₁ : ℝ}

theorem edgeGateClosed_isClosed {d Kc Kl N : ℕ} {S : SiteData d}
    (ℓ : SiteLabel S Kc Kl N μ ν r c₁) (e : S.Edge) (i : Fin 2)
    (g : ℝ) : IsClosed (edgeGateClosed ℓ e i g) := by
  unfold edgeGateClosed ballUnion
  exact isClosed_biUnion_finset fun _ _ => isClosed_closedBall

theorem edgeChamberClosed_isClosed {d Kc Kl N : ℕ} {S : SiteData d}
    (ℓ : SiteLabel S Kc Kl N μ ν r c₁) (e : S.Edge) (ω : ℝ) :
    IsClosed (edgeChamberClosed ℓ ω e) :=
  closedBallSpecs_isClosed _

theorem vertexTubeClosed_isClosed {d Kc Kl N : ℕ} {S : SiteData d}
    (ℓ : SiteLabel S Kc Kl N μ ν r c₁) (ω : ℝ) (v : S.Vertex) :
    IsClosed (vertexTubeClosed ℓ ω v) := by
  classical
  letI : Fintype S.Vertex := (siteMesh_vertices_finite S.mesh.δm_pos).fintype
  letI : Fintype S.Edge := Fintype.ofFinite S.Edge
  unfold vertexTubeClosed
  apply isClosed_iUnion_of_finite
  intro e
  apply isClosed_iUnion_of_finite
  intro i
  split_ifs
  · exact closedBallSpecs_isClosed _
  · exact isClosed_empty

theorem labelNet_node_isClosed {d : ℕ} (S : SiteData d) (C : SiteConsts)
    {Kc Kl : ℕ}
    (ℓ : SiteLabel S Kc Kl C.N C.μ C.ν C.r (Routing.gpC1 4)) :
    ∀ n : NetworkNode S, IsClosed ((labelNet S C ℓ).Node n) := by
  let gates : Set (Rd d) := ⋃ e : S.Edge, ⋃ i : Fin 2,
    interior (edgeGateClosed ℓ e i C.g)
  have hopen : IsOpen gates := by
    unfold gates
    exact isOpen_iUnion fun e => isOpen_iUnion fun i => isOpen_interior
  intro n
  rcases n with v | ⟨e, i⟩
  · change IsClosed (vertexTubeClosed ℓ C.ω v \ gates)
    exact (vertexTubeClosed_isClosed ℓ C.ω v).sdiff hopen
  · fin_cases i
    · change IsClosed (edgeGateClosed ℓ e 0 C.g)
      exact edgeGateClosed_isClosed ℓ e 0 C.g
    · change IsClosed (edgeChamberClosed ℓ C.ω e \ gates)
      exact (edgeChamberClosed_isClosed ℓ e C.ω).sdiff hopen
    · change IsClosed (edgeGateClosed ℓ e 1 C.g)
      exact edgeGateClosed_isClosed ℓ e 1 C.g

theorem edgeTubeClosed_subset_vertex {d Kc Kl N : ℕ} {S : SiteData d}
    {μ ν r c₁ ω : ℝ} (ℓ : SiteLabel S Kc Kl N μ ν r c₁)
    (e : S.Edge) (i : Fin 2) :
    edgeRetainedClosed ℓ e i ω ∪ edgeLeadClosed ℓ e i ω ⊆
      vertexTubeClosed ℓ ω (S.retainedVertex e i) := by
  intro x hx
  have hpiece : closedBallSpecs
      (((edgeRetainedSamples ℓ e i ω) ∪ (edgeLeadSamples ℓ e i ω)).image
        fun y => (y, ω)) =
      edgeRetainedClosed ℓ e i ω ∪ edgeLeadClosed ℓ e i ω := by
    rw [Finset.image_union, closedBallSpecs_union]
    simp only [closedBallSpecs_image, edgeRetainedClosed, edgeLeadClosed]
  unfold vertexTubeClosed
  apply mem_iUnion.mpr
  refine ⟨e, mem_iUnion.mpr ⟨i, ?_⟩⟩
  simpa only [ite_true, hpiece] using hx

theorem labelNet_U_eq_edgeUnion {d : ℕ} (S : SiteData d) (C : SiteConsts)
    {Kc Kl : ℕ}
    (ℓ : SiteLabel S Kc Kl C.N C.μ C.ν C.r (Routing.gpC1 4)) :
    (labelNet S C ℓ).U =
      ⋃ e : S.Edge, closedBallSpecs (edgeBallSpecs ℓ e C.g C.ω) := by
  classical
  letI : Fintype S.Vertex := (siteMesh_vertices_finite S.mesh.δm_pos).fintype
  letI : Fintype S.Edge := Fintype.ofFinite S.Edge
  change closedBallSpecs (labelBallSpecs ℓ C.g C.ω) = _
  rw [labelBallSpecs, closedBallSpecs_biUnion]
  ext x
  simp

/-- Every closed ball is assigned to a gate, chamber, or vertex node after
open gate interiors are excised. -/
theorem labelNet_nodes_cover {d : ℕ} (S : SiteData d) (C : SiteConsts)
    {Kc Kl : ℕ}
    (ℓ : SiteLabel S Kc Kl C.N C.μ C.ν C.r (Routing.gpC1 4)) :
    (labelNet S C ℓ).U ⊆
      ⋃ n : NetworkNode S, (labelNet S C ℓ).Node n := by
  let gates : Set (Rd d) := ⋃ e : S.Edge, ⋃ i : Fin 2,
    interior (edgeGateClosed ℓ e i C.g)
  intro x hx
  have hnodeGate : x ∈ gates →
      x ∈ ⋃ n : NetworkNode S, (labelNet S C ℓ).Node n := by
    intro hxG
    obtain ⟨e, he⟩ := mem_iUnion.mp hxG
    obtain ⟨i, hi⟩ := mem_iUnion.mp he
    fin_cases i
    · apply mem_iUnion.mpr
      refine ⟨Sum.inr (e, 0), ?_⟩
      change x ∈ edgeGateClosed ℓ e 0 C.g
      exact interior_subset hi
    · apply mem_iUnion.mpr
      refine ⟨Sum.inr (e, 2), ?_⟩
      change x ∈ edgeGateClosed ℓ e 1 C.g
      exact interior_subset hi
  by_cases hxG : x ∈ gates
  · exact hnodeGate hxG
  rw [labelNet_U_eq_edgeUnion] at hx
  obtain ⟨e, he⟩ := mem_iUnion.mp hx
  rw [edgeBallSpecs_closed_eq] at he
  have hTube (i : Fin 2)
      (hi : x ∈ edgeRetainedClosed ℓ e i C.ω ∪ edgeLeadClosed ℓ e i C.ω) :
      x ∈ ⋃ n : NetworkNode S, (labelNet S C ℓ).Node n := by
    apply mem_iUnion.mpr
    refine ⟨Sum.inl (S.retainedVertex e i), ?_⟩
    change x ∈ vertexTubeClosed ℓ C.ω (S.retainedVertex e i) \ gates
    exact ⟨edgeTubeClosed_subset_vertex ℓ e i hi, hxG⟩
  have hCh (hch : x ∈ edgeChamberClosed ℓ C.ω e) :
      x ∈ ⋃ n : NetworkNode S, (labelNet S C ℓ).Node n := by
    apply mem_iUnion.mpr
    refine ⟨Sum.inr (e, 1), ?_⟩
    change x ∈ edgeChamberClosed ℓ C.ω e \ gates
    exact ⟨hch, hxG⟩
  have hGate0 (hg : x ∈ edgeGateClosed ℓ e 0 C.g) :
      x ∈ ⋃ n : NetworkNode S, (labelNet S C ℓ).Node n := by
    exact mem_iUnion.mpr ⟨Sum.inr (e, 0), hg⟩
  have hGate1 (hg : x ∈ edgeGateClosed ℓ e 1 C.g) :
      x ∈ ⋃ n : NetworkNode S, (labelNet S C ℓ).Node n := by
    exact mem_iUnion.mpr ⟨Sum.inr (e, 2), hg⟩
  simp only [mem_union] at he
  rcases he with h | hR1
  · rcases h with h | hL1
    · rcases h with h | hG1
      · rcases h with h | hCh'
        · rcases h with h | hG0
          · rcases h with hR0 | hL0
            · exact hTube 0 (Or.inl hR0)
            · exact hTube 0 (Or.inr hL0)
          · exact hGate0 hG0
        · exact hCh hCh'
      · exact hGate1 hG1
    · exact hTube 1 (Or.inr hL1)
  · exact hTube 1 (Or.inl hR1)

theorem labelNet_node_subset_U {d : ℕ} (S : SiteData d) (C : SiteConsts)
    {Kc Kl : ℕ}
    (ℓ : SiteLabel S Kc Kl C.N C.μ C.ν C.r (Routing.gpC1 4)) :
    ∀ n : NetworkNode S, (labelNet S C ℓ).Node n ⊆ (labelNet S C ℓ).U := by
  have hEdge (e : S.Edge) :
      closedBallSpecs (edgeBallSpecs ℓ e C.g C.ω) ⊆ (labelNet S C ℓ).U := by
    rw [labelNet_U_eq_edgeUnion]
    intro x hx
    exact mem_iUnion.mpr ⟨e, hx⟩
  have hTube (e : S.Edge) (i : Fin 2) :
      edgeRetainedClosed ℓ e i C.ω ∪ edgeLeadClosed ℓ e i C.ω ⊆
        closedBallSpecs (edgeBallSpecs ℓ e C.g C.ω) := by
    fin_cases i
    · rw [edgeBallSpecs_closed_eq]
      intro x hx
      simp only [mem_union]
      tauto
    · rw [edgeBallSpecs_closed_eq]
      intro x hx
      have hx' : x ∈ edgeRetainedClosed ℓ e 1 C.ω ∪
          edgeLeadClosed ℓ e 1 C.ω := by simpa using hx
      simp only [mem_union] at hx'
      simp only [mem_union]
      tauto
  have hGate0 (e : S.Edge) :
      edgeGateClosed ℓ e 0 C.g ⊆
        closedBallSpecs (edgeBallSpecs ℓ e C.g C.ω) := by
    rw [edgeBallSpecs_closed_eq]
    intro x hx
    simp only [mem_union]
    tauto
  have hGate1 (e : S.Edge) :
      edgeGateClosed ℓ e 1 C.g ⊆
        closedBallSpecs (edgeBallSpecs ℓ e C.g C.ω) := by
    rw [edgeBallSpecs_closed_eq]
    intro x hx
    simp only [mem_union]
    tauto
  have hCh (e : S.Edge) :
      edgeChamberClosed ℓ C.ω e ⊆
        closedBallSpecs (edgeBallSpecs ℓ e C.g C.ω) := by
    rw [edgeBallSpecs_closed_eq]
    intro x hx
    simp only [mem_union]
    tauto
  intro n x hx
  rcases n with v | ⟨e, i⟩
  · have hxv : x ∈ vertexTubeClosed ℓ C.ω v := hx.1
    unfold vertexTubeClosed at hxv
    obtain ⟨e, he⟩ := mem_iUnion.mp hxv
    obtain ⟨i, hi⟩ := mem_iUnion.mp he
    by_cases hvi : S.retainedVertex e i = v
    · simp only [hvi, ite_true] at hi
      have hpiece : closedBallSpecs
          (((edgeRetainedSamples ℓ e i C.ω) ∪ (edgeLeadSamples ℓ e i C.ω)).image
            fun y => (y, C.ω)) =
          edgeRetainedClosed ℓ e i C.ω ∪ edgeLeadClosed ℓ e i C.ω := by
        rw [Finset.image_union, closedBallSpecs_union]
        simp only [closedBallSpecs_image, edgeRetainedClosed, edgeLeadClosed]
      exact hEdge e (hTube e i (hpiece ▸ hi))
    · simp only [hvi, ite_false, mem_empty_iff_false] at hi
  · fin_cases i
    · exact hEdge e (hGate0 e hx)
    · exact hEdge e (hCh e hx.1)
    · exact hEdge e (hGate1 e hx)

end HigherDimLQGContinuity
