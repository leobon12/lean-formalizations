import HigherDimLQGContinuity.Network.SeparationVertex

/-! # Vertex nodes versus chamber and gate nodes -/

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open Set Metric
open HigherDimLFPP (Rd)

namespace HigherDimLQGContinuity

theorem edgeTubePiece_sep_other_box {d : ℕ} (S : SiteData d)
    (hd : 2 ≤ d) (Cnet v : ℝ) (hv : 0 < v)
    (hA : SiteConstsA S (siteConsts S Cnet v))
    {Kc Kl : ℕ}
    (ℓ : SiteLabel S Kc Kl (siteConsts S Cnet v).N
      (siteConsts S Cnet v).μ (siteConsts S Cnet v).ν
      (siteConsts S Cnet v).r (Routing.gpC1 4))
    (f e : S.Edge) (hfe : f ≠ e) (i : Fin 2)
    {x y : Rd d}
    (hx : x ∈ edgeRetainedClosed ℓ f i (siteConsts S Cnet v).ω ∪
      edgeLeadClosed ℓ f i (siteConsts S Cnet v).ω)
    (hy : y ∈ edgeBoxPieces ℓ e (siteConsts S Cnet v).g
      (siteConsts S Cnet v).ω) :
    (siteConsts S Cnet v).δsep ≤ dist x y := by
  rcases hx with hxR | hxL
  · have h := edgeBoxPieces_sep_other_retained S hd Cnet v hv hA ℓ
      e f (Ne.symm hfe) i hy hxR
    rw [dist_comm] at h
    exact h
  · exact edgeBoxPieces_sep_other_box S hd Cnet v hv hA ℓ
      f e hfe (edgeLeadClosed_subset_boxPieces ℓ f i _ _ hxL) hy

theorem labelNet_vertex_chamber_sep {d : ℕ} (S : SiteData d)
    (hd : 2 ≤ d) (Cnet v : ℝ) (hv : 0 < v)
    (hA : SiteConstsA S (siteConsts S Cnet v))
    {Kc Kl : ℕ}
    (ℓ : SiteLabel S Kc Kl (siteConsts S Cnet v).N
      (siteConsts S Cnet v).μ (siteConsts S Cnet v).ν
      (siteConsts S Cnet v).r (Routing.gpC1 4))
    (hreal : IsRealizable S ℓ S.seed.A S.seed.α S.seed.β
      (siteConsts S Cnet v).t₀)
    (u : S.Vertex) (e : S.Edge) {x y : Rd d}
    (hx : x ∈ (labelNet S (siteConsts S Cnet v) ℓ).Node (Sum.inl u))
    (hy : y ∈ (labelNet S (siteConsts S Cnet v) ℓ).Node
      (Sum.inr (e, (1 : Fin 3)))) :
    (siteConsts S Cnet v).δsep ≤ dist x y := by
  let C := siteConsts S Cnet v
  obtain ⟨f, i, _, hpiece, _⟩ := labelNet_vertex_mem_piece S C ℓ u hx
  have hch := labelNet_chamber_mem_piece S C ℓ e hy
  by_cases hfe : f = e
  · subst e
    fin_cases i
    · rcases hpiece with hret | hlead
      · exact edgeRetained0_chamber_sep S hd Cnet v hv hA ℓ hreal f
          ⟨hret, labelNet_vertex_not_gate S C ℓ u hx f 0⟩
          ⟨hch.1, hch.2 f 0⟩
      · exact edgeLead0_chamber_sep S hd Cnet v hv hA ℓ hreal f
          ⟨hlead, labelNet_vertex_not_gate S C ℓ u hx f 0⟩
          ⟨hch.1, hch.2 f 0⟩
    · rcases hpiece with hret | hlead
      · exact edgeRetained1_chamber_sep S hd Cnet v hv hA ℓ hreal f
          ⟨hret, labelNet_vertex_not_gate S C ℓ u hx f 1⟩
          ⟨hch.1, hch.2 f 1⟩
      · exact edgeLead1_chamber_sep S hd Cnet v hv hA ℓ hreal f
          ⟨hlead, labelNet_vertex_not_gate S C ℓ u hx f 1⟩
          ⟨hch.1, hch.2 f 1⟩
  · exact edgeTubePiece_sep_other_box S hd Cnet v hv hA ℓ
      f e hfe i hpiece (edgeChamberClosed_subset_boxPieces ℓ e C.g C.ω hch.1)

theorem labelNet_vertex_gate0_sep {d : ℕ} (S : SiteData d)
    (hd : 2 ≤ d) (Cnet v : ℝ) (hv : 0 < v) (hv1 : v ≤ 1)
    (hA : SiteConstsA S (siteConsts S Cnet v))
    {Kc Kl : ℕ}
    (ℓ : SiteLabel S Kc Kl (siteConsts S Cnet v).N
      (siteConsts S Cnet v).μ (siteConsts S Cnet v).ν
      (siteConsts S Cnet v).r (Routing.gpC1 4))
    (hreal : IsRealizable S ℓ S.seed.A S.seed.α S.seed.β
      (siteConsts S Cnet v).t₀)
    (u : S.Vertex) (e : S.Edge)
    (hnot : ¬ (labelNet S (siteConsts S Cnet v) ℓ).adj.Adj
      (Sum.inl u) (Sum.inr (e, (0 : Fin 3))))
    {x y : Rd d}
    (hx : x ∈ (labelNet S (siteConsts S Cnet v) ℓ).Node (Sum.inl u))
    (hy : y ∈ (labelNet S (siteConsts S Cnet v) ℓ).Node
      (Sum.inr (e, (0 : Fin 3)))) :
    (siteConsts S Cnet v).δsep ≤ dist x y := by
  let C := siteConsts S Cnet v
  obtain ⟨f, i, hfu, hpiece, _⟩ := labelNet_vertex_mem_piece S C ℓ u hx
  change y ∈ edgeGateClosed ℓ e 0 C.g at hy
  by_cases hfe : f = e
  · subst e
    fin_cases i
    · have hu : u = S.edgeLeft f := by
        simpa [SiteData.retainedVertex] using hfu.symm
      exact False.elim (hnot (hu ▸ labelNet_adj_vertex_gate0 S C ℓ f))
    · rcases hpiece with hret | hlead
      · exact edgeRetained1_gate0_sep S hd Cnet v hv hv1 hA ℓ hreal f hret hy
      · exact edgeLead1_gate0_sep S hd Cnet v hv hv1 hA ℓ hreal f hlead hy
  · exact edgeTubePiece_sep_other_box S hd Cnet v hv hA ℓ
      f e hfe i hpiece (edgeGateClosed_subset_boxPieces ℓ e 0 C.g C.ω hy)

theorem labelNet_vertex_gate1_sep {d : ℕ} (S : SiteData d)
    (hd : 2 ≤ d) (Cnet v : ℝ) (hv : 0 < v) (hv1 : v ≤ 1)
    (hA : SiteConstsA S (siteConsts S Cnet v))
    {Kc Kl : ℕ}
    (ℓ : SiteLabel S Kc Kl (siteConsts S Cnet v).N
      (siteConsts S Cnet v).μ (siteConsts S Cnet v).ν
      (siteConsts S Cnet v).r (Routing.gpC1 4))
    (hreal : IsRealizable S ℓ S.seed.A S.seed.α S.seed.β
      (siteConsts S Cnet v).t₀)
    (u : S.Vertex) (e : S.Edge)
    (hnot : ¬ (labelNet S (siteConsts S Cnet v) ℓ).adj.Adj
      (Sum.inl u) (Sum.inr (e, (2 : Fin 3))))
    {x y : Rd d}
    (hx : x ∈ (labelNet S (siteConsts S Cnet v) ℓ).Node (Sum.inl u))
    (hy : y ∈ (labelNet S (siteConsts S Cnet v) ℓ).Node
      (Sum.inr (e, (2 : Fin 3)))) :
    (siteConsts S Cnet v).δsep ≤ dist x y := by
  let C := siteConsts S Cnet v
  obtain ⟨f, i, hfu, hpiece, _⟩ := labelNet_vertex_mem_piece S C ℓ u hx
  change y ∈ edgeGateClosed ℓ e 1 C.g at hy
  by_cases hfe : f = e
  · subst e
    fin_cases i
    · rcases hpiece with hret | hlead
      · exact edgeRetained0_gate1_sep S hd Cnet v hv hv1 hA ℓ hreal f hret hy
      · exact edgeLead0_gate1_sep S hd Cnet v hv hv1 hA ℓ hreal f hlead hy
    · have hu : u = S.edgeRight f := by
        simpa [SiteData.retainedVertex] using hfu.symm
      exact False.elim (hnot (hu ▸ labelNet_adj_vertex_gate1 S C ℓ f))
  · exact edgeTubePiece_sep_other_box S hd Cnet v hv hA ℓ
      f e hfe i hpiece (edgeGateClosed_subset_boxPieces ℓ e 1 C.g C.ω hy)

end HigherDimLQGContinuity
