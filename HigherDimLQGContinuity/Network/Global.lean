import HigherDimLQGContinuity.Network.Edge

/-! # Connected union of bridges over a connected finite graph -/

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open Set Metric
open HigherDimLFPP (Rd)

namespace HigherDimLQGContinuity

/-- Connected edge bridges containing their two endpoint points have
connected union. The nontriviality condition removes the isolated one-vertex
case, where the edge union is empty. -/
theorem connected_edgeBridge_union {V α : Type*}
    [Fintype V] [Nontrivial V] [TopologicalSpace α]
    (G : SimpleGraph V) (hG : G.Connected)
    (p : V → α) (B : G.edgeSet → Set α)
    (hB : ∀ e : G.edgeSet, IsConnected (B e))
    (hEnd : ∀ e : G.edgeSet,
      p e.1.out.1 ∈ B e ∧ p e.1.out.2 ∈ B e) :
    IsConnected (⋃ e : G.edgeSet, B e) := by
  classical
  letI : Fintype G.edgeSet := Fintype.ofFinite _
  let inc (v : V) : Finset G.edgeSet :=
    Finset.univ.filter fun e => v = e.1.out.1 ∨ v = e.1.out.2
  let star (v : V) : Set α := {p v} ∪ ⋃ e ∈ inc v, B e
  have hinc (v : V) (e : G.edgeSet) (he : e ∈ inc v) : p v ∈ B e := by
    obtain hl | hr := (Finset.mem_filter.mp he).2
    · rw [hl]
      exact (hEnd e).1
    · rw [hr]
      exact (hEnd e).2
  have hstar (v : V) : IsConnected (star v) := by
    exact connected_union_of_common_point (p v) (inc v) B
      (fun e _ => hB e) (fun e he => hinc v e he)
  have hadj_inc (v w : V) (h : G.Adj v w) :
      ∃ e : G.edgeSet, e ∈ inc v ∧ e ∈ inc w := by
    let e : G.edgeSet := ⟨s(v, w), G.mem_edgeSet.mpr h⟩
    have heq : s(e.1.out.1, e.1.out.2) = s(v, w) := by
      simpa only [e] using e.1.out_eq
    have hp := Sym2.eq_iff.mp heq
    refine ⟨e, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases hp with ⟨hl, _⟩ | ⟨_, hr⟩
      · left
        exact hl.symm
      · right
        exact hr.symm
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rcases hp with ⟨_, hr⟩ | ⟨hl, _⟩
      · right
        exact hr.symm
      · left
        exact hl.symm
  have hadj_star (v w : V) (h : G.Adj v w) :
      (star v ∩ star w).Nonempty := by
    obtain ⟨e, hev, hew⟩ := hadj_inc v w h
    refine ⟨p v, ?_, ?_⟩
    · exact Or.inl rfl
    · exact Or.inr (mem_iUnion₂.mpr ⟨e, hew, hinc v e hev⟩)
  have hstarConnected : IsConnected (⋃ v : V, star v) := by
    apply IsConnected.iUnion_of_reflTransGen hstar
    intro v w
    have hpath := (G.reachable_iff_reflTransGen v w).mp (hG v w)
    exact (Relation.ReflTransGen.mono (fun a b hab => hadj_star a b hab)) v w hpath
  have hEq : (⋃ v : V, star v) = ⋃ e : G.edgeSet, B e := by
    ext x
    constructor
    · intro hx
      obtain ⟨v, hxv⟩ := mem_iUnion.mp hx
      rcases hxv with hsingle | hbridges
      · have hxpv : x = p v := by simpa only [mem_singleton_iff] using hsingle
        obtain ⟨w, hvw⟩ := hG.preconnected.exists_adj_of_nontrivial v
        obtain ⟨e, hev, _⟩ := hadj_inc v w hvw
        exact mem_iUnion.mpr ⟨e, hxpv.symm ▸ hinc v e hev⟩
      · obtain ⟨e, _, hxe⟩ := mem_iUnion₂.mp hbridges
        exact mem_iUnion.mpr ⟨e, hxe⟩
    · intro hx
      obtain ⟨e, hxe⟩ := mem_iUnion.mp hx
      let v : V := e.1.out.1
      have he : e ∈ inc v := Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, Or.inl rfl⟩
      exact mem_iUnion.mpr ⟨v, Or.inr (mem_iUnion₂.mpr ⟨e, he, hxe⟩)⟩
  rw [← hEq]
  exact hstarConnected

/-- The buffered annular site mesh has at least two vertices. This transfers
the certified nontrivial sphere mesh through the inclusion of the radius-two
sphere into the buffered annulus. -/
theorem siteMesh_nontrivial {d : ℕ} (S : SiteData d) (hd : 2 ≤ d) :
    Nontrivial S.Vertex := by
  have hsqrt : 0 < Real.sqrt d := Real.sqrt_pos.2 (by exact_mod_cast (show 0 < d by omega))
  have hbound : S.mesh.δm ≤ 1 / (4 * Real.sqrt d) := by
    apply (le_div_iff₀ (by positivity : 0 < 4 * Real.sqrt d)).2
    nlinarith [S.mesh.δm_small]
  letI : Nontrivial
      (HigherDimLQGMetric.Topology.meshVertices S.mesh.δm
        (sphere (0 : Rd d) 2)) :=
    HigherDimLQGMetric.lemma41_routing_mesh_nontrivial
      (by omega : 1 ≤ d) S.mesh.δm_pos hbound
  have hSphere : sphere (0 : Rd d) 2 ⊆ siteMeshRing d S.mesh.δm := by
    intro x hx
    have hnorm : ‖x‖ = 2 := by
      simpa only [mem_sphere, dist_zero_right] using hx
    change 3 / 2 + 3 * Real.sqrt d * S.mesh.δm ≤ ‖x - 0‖ ∧
      ‖x - 0‖ ≤ 5 / 2 - 3 * Real.sqrt d * S.mesh.δm
    simp only [sub_zero, hnorm]
    constructor <;> nlinarith [S.mesh.δm_small]
  have hmono : HigherDimLQGMetric.Topology.meshVertices S.mesh.δm
      (sphere (0 : Rd d) 2) ⊆ S.Vertex := by
    intro m hm
    rcases hm with ⟨k, hcorner, x, hcube, hxSphere⟩
    exact ⟨k, hcorner, x, hcube, hSphere hxSphere⟩
  obtain ⟨u, v, huv⟩ := nontrivial_iff.mp
    (inferInstance : Nontrivial
      (HigherDimLQGMetric.Topology.meshVertices S.mesh.δm
        (sphere (0 : Rd d) 2)))
  exact nontrivial_iff.mpr
    ⟨⟨u.1, hmono u.2⟩, ⟨v.1, hmono v.2⟩,
      fun h => huv (Subtype.ext (congrArg (fun z : S.Vertex => z.1) h))⟩

theorem labelNet_Uo_eq_edgeUnion {d : ℕ} (S : SiteData d) (C : SiteConsts)
    {Kc Kl : ℕ}
    (ℓ : SiteLabel S Kc Kl C.N C.μ C.ν C.r (Routing.gpC1 4)) :
    (labelNet S C ℓ).Uo =
      ⋃ e : S.Edge, openBallSpecs (edgeBallSpecs ℓ e C.g C.ω) := by
  classical
  letI : Fintype S.Vertex := (siteMesh_vertices_finite S.mesh.δm_pos).fintype
  letI : Fintype S.Edge := Fintype.ofFinite S.Edge
  change openBallSpecs (labelBallSpecs ℓ C.g C.ω) = _
  rw [labelBallSpecs, openBallSpecs_biUnion]
  ext x
  simp

theorem labelNet_vertex_mem_Uo {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (C : SiteConsts) {Kc Kl : ℕ}
    (ℓ : SiteLabel S Kc Kl C.N C.μ C.ν C.r (Routing.gpC1 4))
    (hω : 0 < C.ω) (v : S.Vertex) :
    S.vertexPoint v ∈ (labelNet S C ℓ).Uo := by
  letI : Nontrivial S.Vertex := siteMesh_nontrivial S hd
  obtain ⟨e, hleft | hright⟩ :=
    HigherDimLQGMetric.lemma41_tree_incident_out S.mesh.tree_isTree.connected v
  · rw [labelNet_Uo_eq_edgeUnion]
    exact mem_iUnion.mpr ⟨e, hleft.symm ▸ edgeBallSpecs_mem_left ℓ e hω⟩
  · rw [labelNet_Uo_eq_edgeUnion]
    exact mem_iUnion.mpr ⟨e, hright.symm ▸ edgeBallSpecs_mem_right ℓ e hω⟩

/-- The network's open core is connected, given the scalar consequences of
the explicit site-constant order. -/
theorem labelNet_connected {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (C : SiteConsts) {Kc Kl : ℕ}
    (ℓ : SiteLabel S Kc Kl C.N C.μ C.ν C.r (Routing.gpC1 4))
    (hreal : IsRealizable S ℓ S.seed.A S.seed.α S.seed.β C.t₀)
    (hμ : 0 ≤ C.μ) (hω : 0 < C.ω)
    (hμω : Real.sqrt d / 2 * C.μ < C.ω)
    (hμg : Real.sqrt d / 2 * C.μ < C.g)
    (ht₀ : 0 < C.t₀) (ht₀six : C.t₀ ≤ 1 / 6)
    (htipwidth : (d : ℝ) * C.ν + Real.sqrt d / 2 * C.μ < C.g) :
    IsConnected (labelNet S C ℓ).Uo := by
  classical
  letI : Fintype S.Vertex := (siteMesh_vertices_finite S.mesh.δm_pos).fintype
  letI : Nontrivial S.Vertex := siteMesh_nontrivial S hd
  let B : S.Edge → Set (Rd d) :=
    fun e => openBallSpecs (edgeBallSpecs ℓ e C.g C.ω)
  have hB : ∀ e : S.Edge, IsConnected (B e) := by
    intro e
    exact edgeBallSpecs_connected S ℓ e (hreal e) hμ hω hμω hμg ht₀ ht₀six htipwidth
  have hEnd : ∀ e : S.Edge,
      S.vertexPoint e.1.out.1 ∈ B e ∧ S.vertexPoint e.1.out.2 ∈ B e := by
    intro e
    exact ⟨edgeBallSpecs_mem_left ℓ e hω,
      edgeBallSpecs_mem_right ℓ e hω⟩
  have hconn := connected_edgeBridge_union S.mesh.tree
    S.mesh.tree_isTree.connected S.vertexPoint B hB hEnd
  have hEq : (labelNet S C ℓ).Uo = ⋃ e : S.Edge, B e := by
    change openBallSpecs (labelBallSpecs ℓ C.g C.ω) = ⋃ e : S.Edge, B e
    rw [labelBallSpecs, openBallSpecs_biUnion]
    ext x
    simp [B]
  rw [hEq]
  exact hconn

/-- Connectivity specialized to Q3's explicit site constants. -/
theorem labelNet_connected_siteConsts {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (Cnet v : ℝ) (hv : 0 < v) (hv1 : v ≤ 1)
    {Kc Kl : ℕ}
    (ℓ : SiteLabel S Kc Kl (siteConsts S Cnet v).N
      (siteConsts S Cnet v).μ (siteConsts S Cnet v).ν
      (siteConsts S Cnet v).r (Routing.gpC1 4))
    (hreal : IsRealizable S ℓ S.seed.A S.seed.α S.seed.β
      (siteConsts S Cnet v).t₀) :
    IsConnected (labelNet S (siteConsts S Cnet v) ℓ).Uo := by
  let C := siteConsts S Cnet v
  have hν : 0 < C.ν := siteConsts_ν_pos S hd Cnet v
  have hω : 0 < C.ω := by
    change 0 < siteOmegaCoeff d * C.ν ^ 4
    exact mul_pos (siteOmegaCoeff_pos d (by omega)) (pow_pos hν _)
  have hsqrt : 0 < Real.sqrt d :=
    Real.sqrt_pos.2 (by exact_mod_cast (show 0 < d by omega))
  have hμ : 0 ≤ C.μ := by
    change 0 ≤ C.ω ^ 2 / (2 * Real.sqrt d)
    positivity
  have hcell : Real.sqrt d / 2 * C.μ ≤ C.ω / 4 :=
    siteConsts_cell_radius_bound S hd Cnet v
  have hμω : Real.sqrt d / 2 * C.μ < C.ω := by linarith
  have hων : C.ω ≤ C.ν := siteConsts_omega_le_nu S hd Cnet v
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hdν : C.ν ≤ (d : ℝ) * C.ν := by
    nlinarith [mul_le_mul_of_nonneg_right hdR hν.le]
  have hμg : Real.sqrt d / 2 * C.μ < C.g := by
    change Real.sqrt d / 2 * C.μ < 100 * d * C.ν
    nlinarith [hcell, hων]
  have htipwidth : (d : ℝ) * C.ν + Real.sqrt d / 2 * C.μ < C.g := by
    change (d : ℝ) * C.ν + Real.sqrt d / 2 * C.μ < 100 * d * C.ν
    nlinarith [hcell, hων]
  exact labelNet_connected S hd C ℓ hreal hμ hω hμω hμg
    (siteConsts_t₀_pos S Cnet v hv)
    (siteConsts_t₀_le_sixth S Cnet v hv hv1) htipwidth

/-- The finite overlap graph required by the union-of-balls diameter lemma is
connected for every realizable label. -/
theorem labelNet_overlap_connected {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (Cnet v : ℝ) (hv : 0 < v) (hv1 : v ≤ 1)
    {Kc Kl : ℕ}
    (ℓ : SiteLabel S Kc Kl (siteConsts S Cnet v).N
      (siteConsts S Cnet v).μ (siteConsts S Cnet v).ν
      (siteConsts S Cnet v).r (Routing.gpC1 4))
    (hreal : IsRealizable S ℓ S.seed.A S.seed.α S.seed.β
      (siteConsts S Cnet v).t₀) :
    let C := siteConsts S Cnet v
    let F := labelBallSpecs ℓ C.g C.ω
    (SimpleGraph.fromRel (fun p q : F =>
      (ball p.1.1 p.1.2 ∩ ball q.1.1 q.1.2).Nonempty)).Connected := by
  let C := siteConsts S Cnet v
  let F := labelBallSpecs ℓ C.g C.ω
  have hν : 0 < C.ν := siteConsts_ν_pos S hd Cnet v
  have hω : 0 < C.ω := by
    change 0 < siteOmegaCoeff d * C.ν ^ 4
    exact mul_pos (siteOmegaCoeff_pos d (by omega)) (pow_pos hν _)
  have hg : 0 < C.g := by
    change 0 < 100 * d * C.ν
    positivity
  have hconn : IsConnected (openBallSpecs F) := by
    change IsConnected (labelNet S C ℓ).Uo
    exact labelNet_connected_siteConsts S hd Cnet v hv hv1 ℓ hreal
  have hF : F.Nonempty := by
    obtain ⟨x, hx⟩ := hconn.nonempty
    obtain ⟨p, hp, _⟩ := mem_iUnion₂.mp hx
    exact ⟨p, hp⟩
  exact overlapGraph_connected_of_openBallSpecs_connected F hF
    (labelBallSpecs_radius_pos ℓ hg hω) hconn

end HigherDimLQGContinuity
