import HigherDimLQGContinuity.Network.SeparationVertexOther

/-! # Exact nonadjacent-node separation, display (4.8) -/

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open Set Metric
open HigherDimLFPP (Rd)

namespace HigherDimLQGContinuity

theorem labelNet_edge_node_subset_boxPieces {d : ℕ} (S : SiteData d)
    (C : SiteConsts) {Kc Kl : ℕ}
    (ℓ : SiteLabel S Kc Kl C.N C.μ C.ν C.r (Routing.gpC1 4))
    (e : S.Edge) (k : Fin 3) :
    (labelNet S C ℓ).Node (Sum.inr (e, k)) ⊆
      edgeBoxPieces ℓ e C.g C.ω := by
  fin_cases k
  · intro x hx
    exact edgeGateClosed_subset_boxPieces ℓ e 0 C.g C.ω hx
  · intro x hx
    exact edgeChamberClosed_subset_boxPieces ℓ e C.g C.ω
      (labelNet_chamber_mem_piece S C ℓ e hx).1
  · intro x hx
    exact edgeGateClosed_subset_boxPieces ℓ e 1 C.g C.ω hx

theorem labelNet_edge_nodes_sep {d : ℕ} (S : SiteData d)
    (hd : 2 ≤ d) (Cnet v : ℝ) (hv : 0 < v) (hv1 : v ≤ 1)
    (hA : SiteConstsA S (siteConsts S Cnet v))
    {Kc Kl : ℕ}
    (ℓ : SiteLabel S Kc Kl (siteConsts S Cnet v).N
      (siteConsts S Cnet v).μ (siteConsts S Cnet v).ν
      (siteConsts S Cnet v).r (Routing.gpC1 4))
    (hreal : IsRealizable S ℓ S.seed.A S.seed.α S.seed.β
      (siteConsts S Cnet v).t₀)
    (e f : S.Edge) (k j : Fin 3)
    (hne : Sum.inr (e, k) ≠ (Sum.inr (f, j) : NetworkNode S))
    (hnot : ¬ (labelNet S (siteConsts S Cnet v) ℓ).adj.Adj
      (Sum.inr (e, k)) (Sum.inr (f, j)))
    {x y : Rd d}
    (hx : x ∈ (labelNet S (siteConsts S Cnet v) ℓ).Node (Sum.inr (e, k)))
    (hy : y ∈ (labelNet S (siteConsts S Cnet v) ℓ).Node (Sum.inr (f, j))) :
    (siteConsts S Cnet v).δsep ≤ dist x y := by
  let C := siteConsts S Cnet v
  by_cases hef : e = f
  · subst f
    fin_cases k <;> fin_cases j
    · exact False.elim (hne rfl)
    · exact False.elim (hnot (labelNet_adj_gate0_chamber S C ℓ e))
    · change x ∈ edgeGateClosed ℓ e 0 C.g at hx
      change y ∈ edgeGateClosed ℓ e 1 C.g at hy
      exact edgeGateClosed_cross_sep S hd Cnet v hv hv1 hA ℓ hreal e hx hy
    · exact False.elim (hnot (labelNet_adj_gate0_chamber S C ℓ e).symm)
    · exact False.elim (hne rfl)
    · exact False.elim (hnot (labelNet_adj_gate1_chamber S C ℓ e).symm)
    · change x ∈ edgeGateClosed ℓ e 1 C.g at hx
      change y ∈ edgeGateClosed ℓ e 0 C.g at hy
      have h := edgeGateClosed_cross_sep S hd Cnet v hv hv1 hA ℓ hreal e hy hx
      rw [dist_comm] at h
      exact h
    · exact False.elim (hnot (labelNet_adj_gate1_chamber S C ℓ e))
    · exact False.elim (hne rfl)
  · exact edgeBoxPieces_sep_other_box S hd Cnet v hv hA ℓ e f hef
      (labelNet_edge_node_subset_boxPieces S C ℓ e k hx)
      (labelNet_edge_node_subset_boxPieces S C ℓ f j hy)

/-- The complete quantitative incidence list (4.8), under the proved site
constant order clauses. -/
theorem labelNet_sep_of_order {d : ℕ} (S : SiteData d)
    (hd : 2 ≤ d) (Cnet v : ℝ) (hv : 0 < v) (hv1 : v ≤ 1)
    (hA : SiteConstsA S (siteConsts S Cnet v))
    {Kc Kl : ℕ}
    (ℓ : SiteLabel S Kc Kl (siteConsts S Cnet v).N
      (siteConsts S Cnet v).μ (siteConsts S Cnet v).ν
      (siteConsts S Cnet v).r (Routing.gpC1 4))
    (hreal : IsRealizable S ℓ S.seed.A S.seed.α S.seed.β
      (siteConsts S Cnet v).t₀) :
    ∀ n n' : NetworkNode S, n ≠ n' →
      ¬ (labelNet S (siteConsts S Cnet v) ℓ).adj.Adj n n' →
      ∀ x ∈ (labelNet S (siteConsts S Cnet v) ℓ).Node n,
      ∀ y ∈ (labelNet S (siteConsts S Cnet v) ℓ).Node n',
        (siteConsts S Cnet v).δsep ≤ dist x y := by
  intro n n' hne hnot x hx y hy
  rcases n with u | ⟨e, k⟩
  · rcases n' with w | ⟨f, j⟩
    · have huw : u ≠ w := by
        intro h
        exact hne (congrArg Sum.inl h)
      exact labelNet_vertex_vertex_sep S hd Cnet v hv hA ℓ u w huw hx hy
    · fin_cases j
      · exact labelNet_vertex_gate0_sep S hd Cnet v hv hv1 hA
          ℓ hreal u f hnot hx hy
      · exact labelNet_vertex_chamber_sep S hd Cnet v hv hA
          ℓ hreal u f hx hy
      · exact labelNet_vertex_gate1_sep S hd Cnet v hv hv1 hA
          ℓ hreal u f hnot hx hy
  · rcases n' with u | ⟨f, j⟩
    · have hnot' : ¬ (labelNet S (siteConsts S Cnet v) ℓ).adj.Adj
          (Sum.inl u) (Sum.inr (e, k)) := fun h => hnot h.symm
      fin_cases k
      · have h := labelNet_vertex_gate0_sep S hd Cnet v hv hv1 hA
          ℓ hreal u e hnot' hy hx
        rw [dist_comm] at h
        exact h
      · have h := labelNet_vertex_chamber_sep S hd Cnet v hv hA
          ℓ hreal u e hy hx
        rw [dist_comm] at h
        exact h
      · have h := labelNet_vertex_gate1_sep S hd Cnet v hv hv1 hA
          ℓ hreal u e hnot' hy hx
        rw [dist_comm] at h
        exact h
    · exact labelNet_edge_nodes_sep S hd Cnet v hv hv1 hA
        ℓ hreal e f k j hne hnot hx hy

/-- Public site-specific form of (4.8), with a fixed threshold independent
of the tolerance and label. -/
theorem labelNet_sep {d : ℕ} (S : SiteData d) (hd : 2 ≤ d) :
    ∃ vsite : ℝ, 0 < vsite ∧ ∀ v : ℝ,
      0 < v → v ≤ vsite →
      ∀ {Kc Kl : ℕ}
        (ℓ : SiteLabel S Kc Kl (siteConsts S (siteNetCnet S) v).N
          (siteConsts S (siteNetCnet S) v).μ
          (siteConsts S (siteNetCnet S) v).ν
          (siteConsts S (siteNetCnet S) v).r (Routing.gpC1 4)),
        IsRealizable S ℓ S.seed.A S.seed.α S.seed.β
          (siteConsts S (siteNetCnet S) v).t₀ →
        ∀ n n' : NetworkNode S, n ≠ n' →
          ¬ (labelNet S (siteConsts S (siteNetCnet S) v) ℓ).adj.Adj n n' →
          ∀ x ∈ (labelNet S (siteConsts S (siteNetCnet S) v) ℓ).Node n,
          ∀ y ∈ (labelNet S (siteConsts S (siteNetCnet S) v) ℓ).Node n',
            (siteConsts S (siteNetCnet S) v).δsep ≤ dist x y := by
  have hCnet : 0 < siteNetCnet S :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
      (siteNetCnet_ge_one S hd)
  obtain ⟨vsite, c, Cmax, K, hvsite, hvsite1, hc, hCmax, hK,
    _, _, _, _, hspec⟩ := siteConsts_spec S hd (siteNetCnet S) hCnet
  refine ⟨vsite, hvsite, ?_⟩
  intro v hv hvs Kc Kl ℓ hreal
  have hv1 : v ≤ 1 := (hvs.trans hvsite1).trans (by norm_num)
  have hA := (hspec v hv hvs).1
  exact labelNet_sep_of_order S hd (siteNetCnet S) v hv hv1 hA ℓ hreal

end HigherDimLQGContinuity
