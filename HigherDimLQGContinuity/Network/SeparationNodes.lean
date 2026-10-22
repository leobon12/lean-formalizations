import HigherDimLQGContinuity.Network.SeparationRetainedCross

/-! # Membership and incidence for the closed network nodes -/

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open Set Metric
open HigherDimLFPP (Rd)

namespace HigherDimLQGContinuity

variable {μ ν r c₁ : ℝ}

theorem edgeTubeClosed_eq_piece_union {d Kc Kl N : ℕ}
    {S : SiteData d} (ℓ : SiteLabel S Kc Kl N μ ν r c₁)
    (e : S.Edge) (i : Fin 2) (ω : ℝ) :
    closedBallSpecs (((edgeRetainedSamples ℓ e i ω) ∪
      (edgeLeadSamples ℓ e i ω)).image fun x => (x, ω)) =
      edgeRetainedClosed ℓ e i ω ∪ edgeLeadClosed ℓ e i ω := by
  rw [Finset.image_union, closedBallSpecs_union]
  simp only [closedBallSpecs_image, edgeRetainedClosed, edgeLeadClosed]

theorem vertexTubeClosed_mem_piece {d Kc Kl N : ℕ}
    {S : SiteData d} (ℓ : SiteLabel S Kc Kl N μ ν r c₁)
    (ω : ℝ) (v : S.Vertex) {x : Rd d}
    (hx : x ∈ vertexTubeClosed ℓ ω v) :
    ∃ (e : S.Edge) (i : Fin 2),
      S.retainedVertex e i = v ∧
      (x ∈ edgeRetainedClosed ℓ e i ω ∨ x ∈ edgeLeadClosed ℓ e i ω) := by
  unfold vertexTubeClosed at hx
  obtain ⟨e, he⟩ := mem_iUnion.mp hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp he
  by_cases hvi : S.retainedVertex e i = v
  · simp only [hvi, ite_true] at hi
    rw [edgeTubeClosed_eq_piece_union] at hi
    exact ⟨e, i, hvi, hi⟩
  · simp only [hvi, ite_false, mem_empty_iff_false] at hi

theorem labelNet_vertex_mem_piece {d : ℕ} (S : SiteData d)
    (C : SiteConsts) {Kc Kl : ℕ}
    (ℓ : SiteLabel S Kc Kl C.N C.μ C.ν C.r (Routing.gpC1 4))
    (v : S.Vertex) {x : Rd d}
    (hx : x ∈ (labelNet S C ℓ).Node (Sum.inl v)) :
    ∃ (e : S.Edge) (i : Fin 2),
      S.retainedVertex e i = v ∧
      (x ∈ edgeRetainedClosed ℓ e i C.ω ∨ x ∈ edgeLeadClosed ℓ e i C.ω) ∧
      x ∉ ⋃ f : S.Edge, ⋃ j : Fin 2,
        interior (edgeGateClosed ℓ f j C.g) := by
  change x ∈ vertexTubeClosed ℓ C.ω v \
    (⋃ f : S.Edge, ⋃ j : Fin 2,
      interior (edgeGateClosed ℓ f j C.g)) at hx
  obtain ⟨e, i, he, hpiece⟩ := vertexTubeClosed_mem_piece ℓ C.ω v hx.1
  exact ⟨e, i, he, hpiece, hx.2⟩

theorem labelNet_chamber_mem_piece {d : ℕ} (S : SiteData d)
    (C : SiteConsts) {Kc Kl : ℕ}
    (ℓ : SiteLabel S Kc Kl C.N C.μ C.ν C.r (Routing.gpC1 4))
    (e : S.Edge) {x : Rd d}
    (hx : x ∈ (labelNet S C ℓ).Node (Sum.inr (e, (1 : Fin 3)))) :
    x ∈ edgeChamberClosed ℓ C.ω e ∧
      ∀ (f : S.Edge) (j : Fin 2),
        x ∉ interior (edgeGateClosed ℓ f j C.g) := by
  change x ∈ edgeChamberClosed ℓ C.ω e \
    (⋃ f : S.Edge, ⋃ j : Fin 2,
      interior (edgeGateClosed ℓ f j C.g)) at hx
  refine ⟨hx.1, ?_⟩
  intro f j h
  exact hx.2 (mem_iUnion.mpr ⟨f, mem_iUnion.mpr ⟨j, h⟩⟩)

theorem labelNet_vertex_not_gate {d : ℕ} (S : SiteData d)
    (C : SiteConsts) {Kc Kl : ℕ}
    (ℓ : SiteLabel S Kc Kl C.N C.μ C.ν C.r (Routing.gpC1 4))
    (v : S.Vertex) {x : Rd d}
    (hx : x ∈ (labelNet S C ℓ).Node (Sum.inl v))
    (e : S.Edge) (i : Fin 2) :
    x ∉ interior (edgeGateClosed ℓ e i C.g) := by
  obtain ⟨_, _, _, _, hno⟩ := labelNet_vertex_mem_piece S C ℓ v hx
  intro h
  exact hno (mem_iUnion.mpr ⟨e, mem_iUnion.mpr ⟨i, h⟩⟩)

theorem labelNet_adj_vertex_gate0 {d : ℕ} (S : SiteData d)
    (C : SiteConsts) {Kc Kl : ℕ}
    (ℓ : SiteLabel S Kc Kl C.N C.μ C.ν C.r (Routing.gpC1 4))
    (e : S.Edge) :
    (labelNet S C ℓ).adj.Adj
      (Sum.inl (S.edgeLeft e)) (Sum.inr (e, (0 : Fin 3))) := by
  change (SimpleGraph.fromRel (networkIncidence S)).Adj _ _
  rw [SimpleGraph.fromRel_adj]
  simp [networkIncidence]

theorem labelNet_adj_vertex_gate1 {d : ℕ} (S : SiteData d)
    (C : SiteConsts) {Kc Kl : ℕ}
    (ℓ : SiteLabel S Kc Kl C.N C.μ C.ν C.r (Routing.gpC1 4))
    (e : S.Edge) :
    (labelNet S C ℓ).adj.Adj
      (Sum.inl (S.edgeRight e)) (Sum.inr (e, (2 : Fin 3))) := by
  change (SimpleGraph.fromRel (networkIncidence S)).Adj _ _
  rw [SimpleGraph.fromRel_adj]
  simp [networkIncidence]

theorem labelNet_adj_gate0_chamber {d : ℕ} (S : SiteData d)
    (C : SiteConsts) {Kc Kl : ℕ}
    (ℓ : SiteLabel S Kc Kl C.N C.μ C.ν C.r (Routing.gpC1 4))
    (e : S.Edge) :
    (labelNet S C ℓ).adj.Adj
      (Sum.inr (e, (0 : Fin 3))) (Sum.inr (e, (1 : Fin 3))) := by
  change (SimpleGraph.fromRel (networkIncidence S)).Adj _ _
  rw [SimpleGraph.fromRel_adj]
  simp [networkIncidence]

theorem labelNet_adj_gate1_chamber {d : ℕ} (S : SiteData d)
    (C : SiteConsts) {Kc Kl : ℕ}
    (ℓ : SiteLabel S Kc Kl C.N C.μ C.ν C.r (Routing.gpC1 4))
    (e : S.Edge) :
    (labelNet S C ℓ).adj.Adj
      (Sum.inr (e, (2 : Fin 3))) (Sum.inr (e, (1 : Fin 3))) := by
  change (SimpleGraph.fromRel (networkIncidence S)).Adj _ _
  rw [SimpleGraph.fromRel_adj]
  simp [networkIncidence]

end HigherDimLQGContinuity
