import HigherDimLQGContinuity.Network.StarGraph

/-! # Euclidean footprint of an augmented vertex star -/

set_option autoImplicit false
set_option linter.style.haveILetI false
set_option maxHeartbeats 400000

noncomputable section

open Set Metric
open HigherDimLFPP (Rd)

namespace HigherDimLQGContinuity

variable {μ ν r c₁ : ℝ}

theorem closedBallSpecs_image_near {d : ℕ} (Q : Finset (Rd d))
    (o : Rd d) {R t : ℝ}
    (hQ : ∀ z ∈ Q, dist z o ≤ R)
    {x : Rd d}
    (hx : x ∈ closedBallSpecs (Q.image fun z => (z, t))) :
    dist x o ≤ R + t := by
  obtain ⟨p, hp, hxp⟩ := mem_iUnion₂.mp hx
  obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hp
  have htri := dist_triangle x z o
  have hxz := mem_closedBall.mp hxp
  linarith [hQ z hz]

theorem box_near_retainedVertex {d : ℕ} (S : SiteData d)
    (hd : 2 ≤ d) (e : S.Edge) (i : Fin 2) :
    S.box e ⊆ closedBall (S.vertexPoint (S.retainedVertex e i))
      (S.mesh.δm / 2 + Real.sqrt d * S.boxHalfSide) := by
  fin_cases i
  · simpa [SiteData.retainedVertex] using S.box_near_left hd e
  · simpa [SiteData.retainedVertex] using S.box_near_right hd e

theorem box_near_starVertex {d : ℕ} (S : SiteData d)
    (hd : 2 ≤ d) (e : S.Edge) (v : S.Vertex)
    (hv : S.edgeLeft e = v ∨ S.edgeRight e = v) :
    S.box e ⊆ closedBall (S.vertexPoint v)
      (S.mesh.δm / 2 + Real.sqrt d * S.boxHalfSide) := by
  rcases hv with h | h
  · rw [← h]; exact S.box_near_left hd e
  · rw [← h]; exact S.box_near_right hd e

theorem edgeChamberClosed_near_star {d Kc Kl N : ℕ}
    (S : SiteData d) (hd : 2 ≤ d)
    {μ ν r c₁ ω : ℝ} (hμ : 0 ≤ μ)
    (ℓ : SiteLabel S Kc Kl N μ ν r c₁)
    (e : S.Edge) (v : S.Vertex)
    (hv : S.edgeLeft e = v ∨ S.edgeRight e = v)
    {x : Rd d} (hx : x ∈ edgeChamberClosed ℓ ω e) :
    dist x (S.vertexPoint v) ≤
      S.mesh.δm / 2 + Real.sqrt d * S.boxHalfSide + ω := by
  apply closedBallSpecs_image_near (edgeChamberSites ℓ e)
    (S.vertexPoint v) ?_ hx
  intro z hz
  have hzbox := (edgeCellSites_subset_box hμ ℓ e).1 hz
  exact mem_closedBall.mp (box_near_starVertex S hd e v hv hzbox)

theorem edgeGateClosed_near_star {d Kc Kl N : ℕ}
    (S : SiteData d) (hd : 2 ≤ d)
    {μ ν r c₁ g : ℝ} (hμ : 0 ≤ μ)
    (ℓ : SiteLabel S Kc Kl N μ ν r c₁)
    (e : S.Edge) (i : Fin 2) (v : S.Vertex)
    (hv : S.edgeLeft e = v ∨ S.edgeRight e = v)
    {x : Rd d} (hx : x ∈ edgeGateClosed ℓ e i g) :
    dist x (S.vertexPoint v) ≤
      S.mesh.δm / 2 + Real.sqrt d * S.boxHalfSide + g := by
  unfold edgeGateClosed ballUnion at hx
  obtain ⟨k, hk, hxk⟩ := mem_iUnion₂.mp hx
  have hzbox : cellCenter μ (S.edgeCenter e) k ∈ S.box e := by
    fin_cases i
    · exact (ℓ e).2.2.1 k hk (cellCenter_mem_cell hμ _ _)
    · exact (ℓ e).2.2.2.1 k hk (cellCenter_mem_cell hμ _ _)
  have hnear := mem_closedBall.mp (box_near_starVertex S hd e v hv hzbox)
  have htri := dist_triangle x (cellCenter μ (S.edgeCenter e) k) (S.vertexPoint v)
  have hxk' := mem_closedBall.mp hxk
  linarith

theorem vertexTubeClosed_near {d Kc Kl N : ℕ}
    (S : SiteData d) (hd : 2 ≤ d)
    (ℓ : SiteLabel S Kc Kl N μ ν r c₁) (ω : ℝ)
    (v : S.Vertex) {x : Rd d}
    (hx : x ∈ vertexTubeClosed ℓ ω v) :
    dist x (S.vertexPoint v) ≤
      S.mesh.δm / 2 + Real.sqrt d * S.boxHalfSide + ω := by
  unfold vertexTubeClosed at hx
  obtain ⟨e, he⟩ := mem_iUnion.mp hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp he
  by_cases hvi : S.retainedVertex e i = v
  · simp only [hvi, ite_true] at hi
    apply closedBallSpecs_image_near
      ((edgeRetainedSamples ℓ e i ω) ∪ (edgeLeadSamples ℓ e i ω))
      (S.vertexPoint v) ?_ hi
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · rw [← hvi]
      exact mem_closedBall.mp
        (edgeRetainedSamples_subset_vertexBall hd ℓ e i ω hz)
    · rw [← hvi]
      exact mem_closedBall.mp
        (box_near_retainedVertex S hd e i
          (edgeLeadSamples_subset_box ℓ e i ω hz))
  · simp only [hvi, ite_false, mem_empty_iff_false] at hi

theorem labelNet_node_near_star {d Kc Kl : ℕ}
    (S : SiteData d) (hd : 2 ≤ d)
    (C : SiteConsts) (hμ : 0 ≤ C.μ) (hg : 0 ≤ C.g) (hω : 0 ≤ C.ω)
    (ℓ : SiteLabel S Kc Kl C.N C.μ C.ν C.r (Routing.gpC1 4))
    (v : S.Vertex) (n : NetworkNode S)
    (hn : n ∈ networkAugStar S v)
    {x : Rd d} (hx : x ∈ (labelNet S C ℓ).Node n) :
    dist x (S.vertexPoint v) ≤
      S.mesh.δm / 2 + Real.sqrt d * S.boxHalfSide + C.g + C.ω := by
  rcases n with w | ⟨e, i⟩
  · have hw : w = v := hn
    subst w
    have hx' : x ∈ vertexTubeClosed ℓ C.ω v := hx.1
    have h := vertexTubeClosed_near S hd ℓ C.ω v hx'
    linarith
  · fin_cases i
    · have hside : S.edgeLeft e = v := hn
      have hx' : x ∈ edgeGateClosed ℓ e 0 C.g := hx
      have h := edgeGateClosed_near_star S hd hμ ℓ e 0 v
        (Or.inl hside) hx'
      linarith
    · have hside : S.edgeLeft e = v ∨ S.edgeRight e = v := hn
      have hx' : x ∈ edgeChamberClosed ℓ C.ω e := hx.1
      have h := edgeChamberClosed_near_star S hd hμ ℓ e v hside hx'
      linarith
    · have hside : S.edgeRight e = v := hn
      have hx' : x ∈ edgeGateClosed ℓ e 1 C.g := hx
      have h := edgeGateClosed_near_star S hd hμ ℓ e 1 v
        (Or.inr hside) hx'
      linarith

/-- The geometric part of the star conclusion, given Q3's proved order
inequalities. -/
theorem q4_labelNet_star_of_order {d : ℕ} (S : SiteData d)
    (hd : 2 ≤ d) (Cnet v : ℝ)
    (hCnet : 0 < Cnet) (hv : 0 < v) (hv1 : v ≤ 1)
    (hA : SiteConstsA S (siteConsts S Cnet v))
    (hC : SiteConstsC S (siteConsts S Cnet v) v)
    {Kc Kl : ℕ}
    (ℓ : SiteLabel S Kc Kl (siteConsts S Cnet v).N
      (siteConsts S Cnet v).μ (siteConsts S Cnet v).ν
      (siteConsts S Cnet v).r (Routing.gpC1 4))
    (T : Set (NetworkNode S))
    (hconn : ((labelNet S (siteConsts S Cnet v) ℓ).adj.induce T).Connected)
    (hNo : ∀ e : S.Edge,
      ¬ (Sum.inr (e, (0 : Fin 3)) ∈ T ∧
        Sum.inr (e, (2 : Fin 3)) ∈ T)) :
    ∃ z : Rd d,
      closedBall z (4 * S.mesh.δm) ⊆ siteA d ∧
      (⋃ n ∈ T, Metric.cthickening (siteConsts S Cnet v).ς
        ((labelNet S (siteConsts S Cnet v) ℓ).Node n)) ⊆
          closedBall z S.mesh.δm := by
  let C := siteConsts S Cnet v
  have hμ : 0 ≤ C.μ := by
    change 0 ≤ C.ω ^ 2 / (2 * Real.sqrt d)
    have hdR : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
    have hsqrt : 0 < Real.sqrt d := Real.sqrt_pos.mpr hdR
    positivity
  have hν : 0 < C.ν := siteConsts_ν_pos S hd Cnet v
  have hg : 0 ≤ C.g := by
    change 0 ≤ 100 * d * C.ν
    positivity
  have hω : 0 ≤ C.ω := by
    change 0 ≤ siteOmegaCoeff d * C.ν ^ 4
    exact mul_nonneg (siteOmegaCoeff_pos d (by omega)).le
      (pow_nonneg hν.le _)
  have hς : 0 ≤ C.ς :=
    (siteConsts_varsigma_pos S hd Cnet v hCnet hv hv1).le
  obtain ⟨w, hw⟩ := network_connected_subset_augStar S T hconn hNo
  refine ⟨S.vertexPoint w, ?_, ?_⟩
  · have hroot : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr
      (by exact_mod_cast (show 1 ≤ d by omega))
    have hR : 4 * S.mesh.δm ≤ 10 * Real.sqrt d * S.mesh.δm := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hroot) S.mesh.δm_pos.le,
        S.mesh.δm_pos]
    exact (closedBall_subset_closedBall hR).trans
      ((siteMesh_geometry S hd).vertex_ball_A w)
  · intro x hx
    obtain ⟨n, hn, hxn⟩ := mem_iUnion₂.mp hx
    have hclosed := labelNet_node_isClosed S C ℓ n
    rw [hclosed.cthickening_eq_biUnion_closedBall hς] at hxn
    obtain ⟨y, hyn, hxy⟩ := mem_iUnion₂.mp hxn
    have hnear := labelNet_node_near_star S hd C hμ hg hω ℓ w n
      (hw hn) hyn
    have hmargin := siteConsts_star_radius_margin S hd Cnet v hv hA hC
    have htri := dist_triangle x y (S.vertexPoint w)
    apply mem_closedBall.mpr
    have hxy' := mem_closedBall.mp hxy
    linarith

end HigherDimLQGContinuity
