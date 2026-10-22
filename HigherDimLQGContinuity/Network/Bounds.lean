import HigherDimLQGContinuity.Network.Nodes

/-! # Geometric bounds for the finite ball network -/

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open Set Metric
open HigherDimLFPP (Rd)

namespace HigherDimLQGContinuity

variable {μ ν r c₁ : ℝ}

theorem cellCenter_mem_cell {d : ℕ} {μ : ℝ} (hμ : 0 ≤ μ)
    (o : Rd d) (k : Fin d → ℤ) :
    cellCenter μ o k ∈ cell μ o k := by
  intro i
  rw [cellCenter, PiLp.toLp_apply]
  constructor <;> nlinarith

theorem edgeCellSites_subset_box {d Kc Kl N : ℕ} {S : SiteData d}
    {μ ν r c₁ : ℝ} (hμ : 0 ≤ μ)
    (ℓ : SiteLabel S Kc Kl N μ ν r c₁) (e : S.Edge) :
    (↑(edgeChamberSites ℓ e) : Set (Rd d)) ⊆ S.box e ∧
      ∀ i : Fin 2, (↑(edgeGateSites ℓ e i) : Set (Rd d)) ⊆ S.box e := by
  rcases (ℓ e).2 with ⟨hch, hg0, hg1, _, _, _⟩
  constructor
  · intro x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    exact hch k hk (cellCenter_mem_cell hμ _ _)
  · intro i x hx
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hx
    fin_cases i
    · exact hg0 k hk (cellCenter_mem_cell hμ _ _)
    · exact hg1 k hk (cellCenter_mem_cell hμ _ _)

theorem leadSamples_subset_centerBall {d Kl N : ℕ} (S : SiteData d)
    (hd : 2 ≤ d) (e : S.Edge) (P : LeadCode d Kl N)
    {ν r c₁ ω : ℝ} {p : Rd d}
    (hP : P.Geometry ν r c₁ (S.edgeCenter e) S.boxHalfSide p) :
    (↑(leadSamples P ν ω) : Set (Rd d)) ⊆
      closedBall (S.edgeCenter e) (Real.sqrt d * S.boxHalfSide) := by
  intro x hx
  obtain ⟨j, hj, hxj⟩ := Finset.mem_biUnion.mp hx
  have hjlast : j.val < P.last.val := (Finset.mem_filter.mp hj).2
  have hj₀ : j.castSucc ≤ P.last := by
    exact Fin.le_def.mpr (by simpa using Nat.le_of_lt hjlast)
  have hj₁ : j.succ ≤ P.last := by
    exact Fin.le_def.mpr (by simpa using hjlast)
  have hbox₀ : P.point ν j.castSucc ∈ S.box e := (hP.2.2.1 j.castSucc hj₀).1
  have hbox₁ : P.point ν j.succ ∈ S.box e := (hP.2.2.1 j.succ hj₁).1
  have hnear₀ := S.box_subset_center_ball hd e hbox₀
  have hnear₁ := S.box_subset_center_ball hd e hbox₁
  have hseg := segmentSamples_subset_segment (P.point ν j.castSucc)
    (P.point ν j.succ) ω hxj
  exact (convex_closedBall _ _).segment_subset hnear₀ hnear₁ hseg

theorem leadSamples_subset_box {d Kl N : ℕ} (S : SiteData d)
    (e : S.Edge) (P : LeadCode d Kl N)
    {ν r c₁ ω : ℝ} {p : Rd d}
    (hP : P.Geometry ν r c₁ (S.edgeCenter e) S.boxHalfSide p) :
    (↑(leadSamples P ν ω) : Set (Rd d)) ⊆ S.box e := by
  intro x hx
  obtain ⟨j, hj, hxj⟩ := Finset.mem_biUnion.mp hx
  have hjlast : j.val < P.last.val := (Finset.mem_filter.mp hj).2
  have hj₀ : j.castSucc ≤ P.last :=
    Fin.le_def.mpr (by simpa using Nat.le_of_lt hjlast)
  have hj₁ : j.succ ≤ P.last :=
    Fin.le_def.mpr (by simpa using hjlast)
  have hbox₀ : P.point ν j.castSucc ∈ S.box e := (hP.2.2.1 j.castSucc hj₀).1
  have hbox₁ : P.point ν j.succ ∈ S.box e := (hP.2.2.1 j.succ hj₁).1
  have hseg := segmentSamples_subset_segment (P.point ν j.castSucc)
    (P.point ν j.succ) ω hxj
  exact (Routing.convex_resBox (S.edgeCenter e) S.boxHalfSide).segment_subset
    hbox₀ hbox₁ hseg

theorem edgeLeadSamples_subset_box {d Kc Kl N : ℕ} {S : SiteData d}
    (ℓ : SiteLabel S Kc Kl N μ ν r c₁) (e : S.Edge)
    (i : Fin 2) (ω : ℝ) :
    (↑(edgeLeadSamples ℓ e i ω) : Set (Rd d)) ⊆ S.box e := by
  fin_cases i
  · exact leadSamples_subset_box S e (ℓ e).1.lead0 (ℓ e).2.2.2.2.1
  · exact leadSamples_subset_box S e (ℓ e).1.lead1 (ℓ e).2.2.2.2.2.1

theorem edgeRetainedSamples_subset_vertexBall {d Kc Kl N : ℕ}
    {S : SiteData d} (hd : 2 ≤ d)
    (ℓ : SiteLabel S Kc Kl N μ ν r c₁) (e : S.Edge)
    (i : Fin 2) (ω : ℝ) :
    (↑(edgeRetainedSamples ℓ e i ω) : Set (Rd d)) ⊆
      closedBall (S.vertexPoint (S.retainedVertex e i))
        (S.mesh.δm / 2 + Real.sqrt d * S.boxHalfSide) := by
  intro x hx
  have hseg := segmentSamples_subset_segment
    (S.vertexPoint (S.retainedVertex e i)) (S.port e i) ω hx
  apply S.retained_near_endpoint hd e i
  fin_cases i
  · simpa [SiteData.retained, SiteData.retainedVertex] using hseg
  · simpa [SiteData.retained, SiteData.retainedVertex, segment_symm] using hseg

/-- The margin available around an edge midpoint is much larger than the
reserved box itself. -/
theorem edgeCenter_quarterBall_interior {d : ℕ} (S : SiteData d)
    (hd : 2 ≤ d) (e : S.Edge) :
    closedBall (S.edgeCenter e) (S.mesh.δm / 4) ⊆ interior (siteC d) := by
  intro x hx
  have hroot : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr
    (by exact_mod_cast (show 1 ≤ d by omega))
  have htri := dist_triangle x (S.edgeCenter e)
    (S.vertexPoint (S.edgeLeft e))
  have hcenter := S.edgeCenter_dist_left e
  have hdist : dist x (S.vertexPoint (S.edgeLeft e)) ≤
      Real.sqrt d * S.mesh.δm := by
    have hx' := mem_closedBall.mp hx
    rw [hcenter] at htri
    have hprod : S.mesh.δm ≤ Real.sqrt d * S.mesh.δm := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hroot) S.mesh.δm_pos.le]
    linarith [S.mesh.δm_pos]
  exact (siteMesh_geometry S hd).vertex_ball_C (S.edgeLeft e)
    (mem_closedBall.mpr hdist)

theorem q4_vertex_radius_interior {d : ℕ} (S : SiteData d)
    (hd : 2 ≤ d) (v : S.Vertex) :
    closedBall (S.vertexPoint v) (Real.sqrt d * S.mesh.δm) ⊆
      interior (siteC d) := (siteMesh_geometry S hd).vertex_ball_C v

theorem q4_centerBall_near_left {d : ℕ} (S : SiteData d)
    (e : S.Edge) {x : Rd d}
    (hx : x ∈ closedBall (S.edgeCenter e) (Real.sqrt d * S.boxHalfSide)) :
    dist x (S.vertexPoint (S.edgeLeft e)) ≤
      S.mesh.δm / 2 + Real.sqrt d * S.boxHalfSide := by
  have htri := dist_triangle x (S.edgeCenter e)
    (S.vertexPoint (S.edgeLeft e))
  rw [S.edgeCenter_dist_left e] at htri
  have hx' := mem_closedBall.mp hx
  linarith

/-- Each network ball centre is close to one endpoint of its edge. -/
theorem edgeBallSpecs_center_near_vertex {d Kc Kl N : ℕ}
    (S : SiteData d) (hd : 2 ≤ d)
    {μ ν r c₁ g ω : ℝ} (hμ : 0 ≤ μ)
    (ℓ : SiteLabel S Kc Kl N μ ν r c₁) (e : S.Edge)
    (p : Rd d × ℝ) (hp : p ∈ edgeBallSpecs ℓ e g ω) :
    ∃ v : S.Vertex, dist p.1 (S.vertexPoint v) ≤
      S.mesh.δm / 2 + Real.sqrt d * S.boxHalfSide := by
  have hcell := edgeCellSites_subset_box hμ ℓ e
  have hbox (x : Rd d) (hx : x ∈ S.box e) :
      dist x (S.vertexPoint (S.edgeLeft e)) ≤
        S.mesh.δm / 2 + Real.sqrt d * S.boxHalfSide :=
    mem_closedBall.mp (S.box_near_left hd e hx)
  have hlead (i : Fin 2) (x : Rd d) (hx : x ∈ edgeLeadSamples ℓ e i ω) :
      dist x (S.vertexPoint (S.edgeLeft e)) ≤
        S.mesh.δm / 2 + Real.sqrt d * S.boxHalfSide := by
    fin_cases i
    · exact q4_centerBall_near_left S e
        (leadSamples_subset_centerBall S hd e (ℓ e).1.lead0
          (ℓ e).2.2.2.2.1 hx)
    · exact q4_centerBall_near_left S e
        (leadSamples_subset_centerBall S hd e (ℓ e).1.lead1
          (ℓ e).2.2.2.2.2.1 hx)
  have hret (i : Fin 2) (x : Rd d) (hx : x ∈ edgeRetainedSamples ℓ e i ω) :
      dist x (S.vertexPoint (S.retainedVertex e i)) ≤
        S.mesh.δm / 2 + Real.sqrt d * S.boxHalfSide :=
    mem_closedBall.mp (edgeRetainedSamples_subset_vertexBall hd ℓ e i ω hx)
  simp only [edgeBallSpecs, Finset.mem_union] at hp
  rcases hp with (((((hCh | hG0) | hG1) | hR0) | hR1) | hL0) | hL1
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hCh
    exact ⟨S.edgeLeft e, hbox x (hcell.1 hx)⟩
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hG0
    exact ⟨S.edgeLeft e, hbox x (hcell.2 0 hx)⟩
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hG1
    exact ⟨S.edgeLeft e, hbox x (hcell.2 1 hx)⟩
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hR0
    exact ⟨S.retainedVertex e 0, hret 0 x hx⟩
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hR1
    exact ⟨S.retainedVertex e 1, hret 1 x hx⟩
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hL0
    exact ⟨S.edgeLeft e, hlead 0 x hx⟩
  · obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hL1
    exact ⟨S.edgeLeft e, hlead 1 x hx⟩

/-- The site order leaves a full mesh-scale margin around every ball. -/
theorem siteConsts_network_radius_margin {d : ℕ} (S : SiteData d)
    (hd : 2 ≤ d) (Cnet v : ℝ) (hv : 0 < v)
    (hA : SiteConstsA S (siteConsts S Cnet v))
    (hC : SiteConstsC S (siteConsts S Cnet v) v) :
    let C := siteConsts S Cnet v
    S.mesh.δm / 2 + Real.sqrt d * S.boxHalfSide + C.g + C.ς ≤
        Real.sqrt d * S.mesh.δm ∧
      S.mesh.δm / 2 + Real.sqrt d * S.boxHalfSide + C.ω + C.ς ≤
        Real.sqrt d * S.mesh.δm := by
  let C := siteConsts S Cnet v
  have hroot : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr
    (by exact_mod_cast (show 1 ≤ d by omega))
  have hω : 0 < C.ω := by
    change 0 < siteOmegaCoeff d * C.ν ^ 4
    exact mul_pos (siteOmegaCoeff_pos d (by omega))
      (pow_pos (siteConsts_ν_pos S hd Cnet v) _)
  have hdiag := S.box_halfDiagonal_le hd
  have hL : S.boxHalfSide ≤ S.mesh.δm / 64 := by
    have hLpos := S.boxHalfSide_pos hd
    nlinarith [mul_nonneg (sub_nonneg.mpr hroot) hLpos.le]
  have hrL := siteConsts_r_le_box S hd Cnet v hv
  have hgr : C.g ≤ C.r / 8 := hA.2.2.1
  have hωr : C.ω ≤ C.r / 8 := by
    have hωraw := (le_min_iff.mp hA.2.2.2.1).1
    have hrootpos : 0 < 8 * Real.sqrt d := by nlinarith
    have hmul := (le_div_iff₀ hrootpos).mp hωraw
    nlinarith [mul_nonneg (sub_nonneg.mpr hroot) hω.le]
  have hςω : C.ς ≤ C.ω / 4 := hC.2.2.1
  have hG : C.g ≤ S.mesh.δm / 64 := by linarith
  have hW : C.ω ≤ S.mesh.δm / 64 := by linarith
  have hV : C.ς ≤ S.mesh.δm / 64 := by linarith
  have hδ := S.mesh.δm_pos
  have hδroot : S.mesh.δm ≤ Real.sqrt d * S.mesh.δm := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hroot) hδ.le]
  constructor <;> linarith

theorem siteConsts_star_radius_margin {d : ℕ} (S : SiteData d)
    (hd : 2 ≤ d) (Cnet v : ℝ) (hv : 0 < v)
    (hA : SiteConstsA S (siteConsts S Cnet v))
    (hC : SiteConstsC S (siteConsts S Cnet v) v) :
    let C := siteConsts S Cnet v
    S.mesh.δm / 2 + Real.sqrt d * S.boxHalfSide +
      C.g + C.ω + C.ς ≤ S.mesh.δm := by
  let C := siteConsts S Cnet v
  have hroot : 1 ≤ Real.sqrt d := Real.one_le_sqrt.mpr
    (by exact_mod_cast (show 1 ≤ d by omega))
  have hω : 0 < C.ω := by
    change 0 < siteOmegaCoeff d * C.ν ^ 4
    exact mul_pos (siteOmegaCoeff_pos d (by omega))
      (pow_pos (siteConsts_ν_pos S hd Cnet v) _)
  have hdiag := S.box_halfDiagonal_le hd
  have hL : S.boxHalfSide ≤ S.mesh.δm / 64 := by
    have hLpos := S.boxHalfSide_pos hd
    nlinarith [mul_nonneg (sub_nonneg.mpr hroot) hLpos.le]
  have hrL := siteConsts_r_le_box S hd Cnet v hv
  have hgr : C.g ≤ C.r / 8 := hA.2.2.1
  have hωr : C.ω ≤ C.r / 8 := by
    have hωraw := (le_min_iff.mp hA.2.2.2.1).1
    have hrootpos : 0 < 8 * Real.sqrt d := by nlinarith
    have hmul := (le_div_iff₀ hrootpos).mp hωraw
    nlinarith [mul_nonneg (sub_nonneg.mpr hroot) hω.le]
  have hςω : C.ς ≤ C.ω / 4 := hC.2.2.1
  have hG : C.g ≤ S.mesh.δm / 64 := by linarith
  have hW : C.ω ≤ S.mesh.δm / 64 := by linarith
  have hV : C.ς ≤ S.mesh.δm / 64 := by linarith
  linarith [S.mesh.δm_pos]

theorem labelBallSpecs_center_near_vertex {d Kc Kl N : ℕ}
    (S : SiteData d) (hd : 2 ≤ d)
    {μ ν r c₁ g ω : ℝ} (hμ : 0 ≤ μ)
    (ℓ : SiteLabel S Kc Kl N μ ν r c₁)
    (p : Rd d × ℝ) (hp : p ∈ labelBallSpecs ℓ g ω) :
    ∃ v : S.Vertex, dist p.1 (S.vertexPoint v) ≤
      S.mesh.δm / 2 + Real.sqrt d * S.boxHalfSide := by
  simp only [labelBallSpecs, Finset.mem_biUnion] at hp
  obtain ⟨e, _, hpe⟩ := hp
  exact edgeBallSpecs_center_near_vertex S hd hμ ℓ e p hpe

/-- The closed collar of the literal finite-ball network remains in the
collector interior. -/
theorem labelNet_cthickening_subset_interior {d : ℕ}
    (S : SiteData d) (hd : 2 ≤ d) (Cnet v : ℝ)
    (hCnet : 0 < Cnet) (hv : 0 < v) (hv1 : v ≤ 1)
    (hA : SiteConstsA S (siteConsts S Cnet v))
    (hC : SiteConstsC S (siteConsts S Cnet v) v)
    {Kc Kl : ℕ}
    (ℓ : SiteLabel S Kc Kl (siteConsts S Cnet v).N
      (siteConsts S Cnet v).μ (siteConsts S Cnet v).ν
      (siteConsts S Cnet v).r (Routing.gpC1 4)) :
    Metric.cthickening (siteConsts S Cnet v).ς
      (labelNet S (siteConsts S Cnet v) ℓ).U ⊆ interior (siteC d) := by
  let C := siteConsts S Cnet v
  let F := labelBallSpecs ℓ C.g C.ω
  have hω : 0 < C.ω := by
    change 0 < siteOmegaCoeff d * C.ν ^ 4
    exact mul_pos (siteOmegaCoeff_pos d (by omega))
      (pow_pos (siteConsts_ν_pos S hd Cnet v) _)
  have hμ : 0 ≤ C.μ := by
    change 0 ≤ C.ω ^ 2 / (2 * Real.sqrt d)
    positivity
  have hς : 0 ≤ C.ς :=
    (siteConsts_varsigma_pos S hd Cnet v hCnet hv hv1).le
  have hmargin := siteConsts_network_radius_margin S hd Cnet v hv hA hC
  have hball (p : Rd d × ℝ) (hp : p ∈ F) :
      closedBall p.1 (p.2 + C.ς) ⊆ interior (siteC d) := by
    obtain ⟨w, hw⟩ := labelBallSpecs_center_near_vertex S hd hμ ℓ p hp
    have hradius : p.2 = C.g ∨ p.2 = C.ω := by
      simp only [F, labelBallSpecs, Finset.mem_biUnion] at hp
      obtain ⟨e, _, hpe⟩ := hp
      exact edgeBallSpecs_radius ℓ e hpe
    have hbound : S.mesh.δm / 2 + Real.sqrt d * S.boxHalfSide +
        p.2 + C.ς ≤ Real.sqrt d * S.mesh.δm := by
      rcases hradius with hg | hω'
      · rw [hg]; exact hmargin.1
      · rw [hω']; exact hmargin.2
    intro x hx
    have htri := dist_triangle x p.1 (S.vertexPoint w)
    have hx' := mem_closedBall.mp hx
    have hdist : dist x (S.vertexPoint w) ≤ Real.sqrt d * S.mesh.δm := by
      linarith
    exact (q4_vertex_radius_interior S hd w) (mem_closedBall.mpr hdist)
  intro x hx
  have hUclosed := labelNet_isClosed S C ℓ
  rw [hUclosed.cthickening_eq_biUnion_closedBall hς] at hx
  obtain ⟨y, hyU, hxy⟩ := mem_iUnion₂.mp hx
  change y ∈ closedBallSpecs F at hyU
  obtain ⟨p, hp, hyp⟩ := mem_iUnion₂.mp hyU
  have htri := dist_triangle x y p.1
  have hxp : x ∈ closedBall p.1 (p.2 + C.ς) := by
    apply mem_closedBall.mpr
    have hxy' := mem_closedBall.mp hxy
    have hyp' := mem_closedBall.mp hyp
    linarith
  exact hball p hp hxp

theorem siteC_subset_siteA (d : ℕ) : siteC d ⊆ siteA d := by
  intro x hx
  simp only [siteC, siteA, annA, HigherDimLQGMetric.annCl,
    HigherDimLQGMetric.ann, mem_ofPred_eq, sub_zero] at hx ⊢
  constructor <;> linarith [hx.1, hx.2]

theorem labelNet_ball_subset_siteA {d : ℕ}
    (S : SiteData d) (hd : 2 ≤ d) (Cnet v : ℝ)
    (hCnet : 0 < Cnet) (hv : 0 < v) (hv1 : v ≤ 1)
    (hA : SiteConstsA S (siteConsts S Cnet v))
    (hC : SiteConstsC S (siteConsts S Cnet v) v)
    {Kc Kl : ℕ}
    (ℓ : SiteLabel S Kc Kl (siteConsts S Cnet v).N
      (siteConsts S Cnet v).μ (siteConsts S Cnet v).ν
      (siteConsts S Cnet v).r (Routing.gpC1 4))
    (p : Rd d × ℝ)
    (hp : p ∈ labelBallSpecs ℓ (siteConsts S Cnet v).g
      (siteConsts S Cnet v).ω) :
    closedBall p.1 p.2 ⊆ siteA d := by
  let C := siteConsts S Cnet v
  have hς : 0 ≤ C.ς :=
    (siteConsts_varsigma_pos S hd Cnet v hCnet hv hv1).le
  have hcollar := labelNet_cthickening_subset_interior S hd Cnet v
    hCnet hv hv1 hA hC ℓ
  intro x hx
  have hxU : x ∈ (labelNet S C ℓ).U := by
    change x ∈ closedBallSpecs (labelBallSpecs ℓ C.g C.ω)
    exact mem_iUnion₂.mpr ⟨p, hp, hx⟩
  exact siteC_subset_siteA d
    (interior_subset (hcollar (Metric.self_subset_cthickening _ hxU)))

end HigherDimLQGContinuity
