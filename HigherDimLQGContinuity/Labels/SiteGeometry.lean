import HigherDimLQGContinuity.Labels.SiteData
import HigherDimLQGContinuity.Labels.Cells

/-!
# Geometry of one site tree edge

The endpoint spacing and midpoint bounds reuse the lattice edge results of
`HigherDimLQGMetric.Routing.Mesh`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric
open HigherDimLFPP (Rd)
open scoped InnerProductSpace

namespace HigherDimLQGContinuity

theorem SiteData.boxHalfSide_pos {d : ℕ} (S : SiteData d) (hd : 2 ≤ d) :
    0 < S.boxHalfSide := by
  unfold SiteData.boxHalfSide
  have hdpos : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
  exact div_pos S.mesh.δm_pos (mul_pos (by norm_num) hdpos)

/-- Endpoints of each selected tree edge are lattice neighbours. -/
theorem SiteData.edgePoint_dist {d : ℕ} (S : SiteData d) (e : S.Edge) :
    dist (S.vertexPoint (S.edgeLeft e)) (S.vertexPoint (S.edgeRight e)) =
      S.mesh.δm := by
  exact HigherDimLQGMetric.dist_latticePoint_of_adj S.mesh.δm_pos
    (HigherDimLQGMetric.lemma41_tree_edge_adj S.mesh.tree_le e)

theorem SiteData.edgeCenter_dist_left {d : ℕ} (S : SiteData d) (e : S.Edge) :
    dist (S.edgeCenter e) (S.vertexPoint (S.edgeLeft e)) = S.mesh.δm / 2 := by
  rw [dist_eq_norm]
  exact HigherDimLQGMetric.Routing.norm_midpoint_sub_left (S.edgePoint_dist e)

/-- A reserved box lies in a small closed ball around its midpoint. -/
theorem SiteData.box_subset_center_ball {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (e : S.Edge) :
    S.box e ⊆ closedBall (S.edgeCenter e) (Real.sqrt d * S.boxHalfSide) := by
  intro x hx
  rw [mem_closedBall]
  apply q3_dist_le_sqrt_mul_of_coord_le x (S.edgeCenter e)
    (r := S.boxHalfSide) (S.boxHalfSide_pos hd).le
  exact hx

/-- The half-diagonal of a reserved box is at most `δ/64`. -/
theorem SiteData.box_halfDiagonal_le {d : ℕ} (S : SiteData d) (hd : 2 ≤ d) :
    Real.sqrt d * S.boxHalfSide ≤ S.mesh.δm / 64 := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast (show 1 ≤ d by omega)
  have hdpos : 0 < (d : ℝ) := by linarith
  have hroot : Real.sqrt d ≤ d := (Real.sqrt_le_self_iff).2 (Or.inr hdR)
  calc
    Real.sqrt d * S.boxHalfSide ≤ d * S.boxHalfSide :=
      mul_le_mul_of_nonneg_right hroot (S.boxHalfSide_pos hd).le
    _ = S.mesh.δm / 64 := by
      unfold SiteData.boxHalfSide
      field_simp

/-- Every small ball about an edge midpoint remains in the collector interior. -/
theorem SiteData.edgeCenter_ball_interior_C {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (e : S.Edge) {R : ℝ} (hR : R ≤ S.mesh.δm / 64) :
    closedBall (S.edgeCenter e) R ⊆ interior (siteC d) := by
  intro x hx
  have hroot : 1 ≤ Real.sqrt d := (Real.one_le_sqrt).2
    (by exact_mod_cast (show 1 ≤ d by omega))
  have hdistxc : dist x (S.edgeCenter e) ≤ R := mem_closedBall.mp hx
  have hdistcv := S.edgeCenter_dist_left e
  have hdistxv : dist x (S.vertexPoint (S.edgeLeft e)) ≤ Real.sqrt d * S.mesh.δm := by
    have htri := dist_triangle x (S.edgeCenter e) (S.vertexPoint (S.edgeLeft e))
    have hδ := S.mesh.δm_pos
    nlinarith [mul_nonneg (sub_nonneg.mpr hroot) hδ.le]
  exact siteMesh_vertex_ball_interior_C hd S.mesh.δm_pos (S.edgeLeft e).2
    (mem_closedBall.mpr hdistxv)

/-- (F4): each reserved box is contained in the collector interior. -/
theorem SiteData.box_subset_interior_C {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (e : S.Edge) : S.box e ⊆ interior (siteC d) :=
  (S.box_subset_center_ball hd e).trans
    (S.edgeCenter_ball_interior_C hd e (S.box_halfDiagonal_le hd))

/-- The central ball of radius `L`, required by the certificate interface. -/
theorem SiteData.center_ball_interior_C {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (e : S.Edge) :
    closedBall (S.edgeCenter e) S.boxHalfSide ⊆ interior (siteC d) := by
  have hroot : 1 ≤ Real.sqrt d := (Real.one_le_sqrt).2
    (by exact_mod_cast (show 1 ≤ d by omega))
  have hL : S.boxHalfSide ≤ Real.sqrt d * S.boxHalfSide := by
    nlinarith [S.boxHalfSide_pos hd]
  have hR : S.boxHalfSide ≤ S.mesh.δm / 64 :=
    hL.trans (S.box_halfDiagonal_le hd)
  exact S.edgeCenter_ball_interior_C hd e hR

/-- Distinct lattice edge midpoints are at least `5δ/8` apart. The common
endpoint case uses the nonacute angle proved in the pinned routing library. -/
theorem q3_lattice_midpoint_separated {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {m₁ m₁' m₂ m₂' : Fin d → ℤ}
    (h₁ : (HigherDimLQGMetric.Topology.latticeGraph d).Adj m₁ m₁')
    (h₂ : (HigherDimLQGMetric.Topology.latticeGraph d).Adj m₂ m₂')
    (hne : s(m₁, m₁') ≠ s(m₂, m₂')) :
    5 * δ / 8 ≤ dist
      (midpoint ℝ (HigherDimLQGMetric.Topology.latticePoint δ m₁)
        (HigherDimLQGMetric.Topology.latticePoint δ m₁'))
      (midpoint ℝ (HigherDimLQGMetric.Topology.latticePoint δ m₂)
        (HigherDimLQGMetric.Topology.latticePoint δ m₂')) := by
  open HigherDimLQGMetric.Topology in
  by_cases hc : ∃ n, (n = m₁ ∨ n = m₁') ∧ (n = m₂ ∨ n = m₂')
  · obtain ⟨n, hn₁, hn₂⟩ := hc
    obtain ⟨w₁, w₂, hw₁, hw₂, hw, e₁, e₂⟩ :=
      HigherDimLQGMetric.Routing.exists_normal_form_of_common_endpoint h₁ h₂ hne hn₁ hn₂
    rw [HigherDimLQGMetric.Routing.midpoint_eq_of_sym2_eq δ e₁,
      HigherDimLQGMetric.Routing.midpoint_eq_of_sym2_eq δ e₂]
    let v := HigherDimLQGMetric.Topology.latticePoint δ n
    let y₁ := midpoint ℝ v (HigherDimLQGMetric.Topology.latticePoint δ w₁)
    let y₂ := midpoint ℝ v (HigherDimLQGMetric.Topology.latticePoint δ w₂)
    have hinner := HigherDimLQGMetric.inner_latticePoint_sub_nonpos δ hw₁ hw₂ hw
    have hSq := HigherDimLQGMetric.Routing.sq_norm_add_sq_norm_le_of_inner_nonpos hinner
      (midpoint_mem_segment v (HigherDimLQGMetric.Topology.latticePoint δ w₁))
      (midpoint_mem_segment v (HigherDimLQGMetric.Topology.latticePoint δ w₂))
    have hdist₁ : ‖y₁ - v‖ = δ / 2 :=
      HigherDimLQGMetric.Routing.norm_midpoint_sub_left
        (HigherDimLQGMetric.dist_latticePoint_of_adj hδ hw₁)
    have hdist₂ : ‖y₂ - v‖ = δ / 2 :=
      HigherDimLQGMetric.Routing.norm_midpoint_sub_left
        (HigherDimLQGMetric.dist_latticePoint_of_adj hδ hw₂)
    have hsq' : (5 * δ / 8) ^ 2 ≤ (dist y₁ y₂) ^ 2 := by
      dsimp [y₁, y₂] at hSq hdist₁ hdist₂ ⊢
      rw [hdist₁, hdist₂, ← dist_eq_norm] at hSq
      nlinarith [sq_nonneg δ]
    exact (pow_le_pow_iff_left₀ (by positivity) dist_nonneg two_ne_zero).1 hsq'
  · have hno : ∀ n, (n = m₁ ∨ n = m₁') → (n = m₂ ∨ n = m₂') → False := by
      intro n hn₁ hn₂
      exact hc ⟨n, hn₁, hn₂⟩
    have hdist := HigherDimLQGMetric.le_dist_of_mem_latticeSegment hδ
      (Or.inr h₁) (Or.inr h₂) hno
      (midpoint_mem_segment _ _) (midpoint_mem_segment _ _)
    linarith

/-- Distinct reserved boxes have Euclidean clearance at least `δm/2`. -/
theorem SiteData.box_pair_separated {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (e f : S.Edge) (hef : e ≠ f)
    {x y : Rd d} (hx : x ∈ S.box e) (hy : y ∈ S.box f) :
    S.mesh.δm / 2 ≤ dist x y := by
  have h₁ := HigherDimLQGMetric.lemma41_tree_edge_adj S.mesh.tree_le e
  have h₂ := HigherDimLQGMetric.lemma41_tree_edge_adj S.mesh.tree_le f
  have hne := HigherDimLQGMetric.lemma41_tree_edges_ne e f hef
  have hcent : 5 * S.mesh.δm / 8 ≤ dist (S.edgeCenter e) (S.edgeCenter f) :=
    q3_lattice_midpoint_separated S.mesh.δm_pos h₁ h₂ hne
  have hxe : dist x (S.edgeCenter e) ≤ S.mesh.δm / 64 :=
    (mem_closedBall.mp (S.box_subset_center_ball hd e hx)).trans (S.box_halfDiagonal_le hd)
  have hyf : dist y (S.edgeCenter f) ≤ S.mesh.δm / 64 :=
    (mem_closedBall.mp (S.box_subset_center_ball hd f hy)).trans (S.box_halfDiagonal_le hd)
  have htri : dist (S.edgeCenter e) (S.edgeCenter f) ≤
      dist (S.edgeCenter e) x + dist x y + dist y (S.edgeCenter f) := by
    calc
      dist (S.edgeCenter e) (S.edgeCenter f) ≤
          dist (S.edgeCenter e) x + dist x (S.edgeCenter f) := dist_triangle _ _ _
      _ ≤ dist (S.edgeCenter e) x + (dist x y + dist y (S.edgeCenter f)) := by
        gcongr
        exact dist_triangle _ _ _
      _ = _ := by ring
  have hxe' : dist (S.edgeCenter e) x ≤ S.mesh.δm / 64 := by
    rw [dist_comm (S.edgeCenter e) x]
    exact hxe
  have hδ := S.mesh.δm_pos
  linarith [S.mesh.δm_pos]

/-- The oriented lattice direction has unit Euclidean norm. -/
theorem SiteData.edgeUnit_norm {d : ℕ} (S : SiteData d) (e : S.Edge) :
    ‖S.edgeUnit e‖ = 1 := by
  unfold SiteData.edgeUnit
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos S.mesh.δm_pos]
  have hnorm : ‖S.vertexPoint (S.edgeRight e) - S.vertexPoint (S.edgeLeft e)‖ =
      S.mesh.δm := by
    rw [← dist_eq_norm, dist_comm]
    exact S.edgePoint_dist e
  rw [hnorm]
  exact inv_mul_cancel₀ S.mesh.δm_pos.ne'

theorem SiteData.boxHalfSide_le_half {d : ℕ} (S : SiteData d) (hd : 2 ≤ d) :
    S.boxHalfSide ≤ S.mesh.δm / 2 := by
  have hroot : 1 ≤ Real.sqrt d := (Real.one_le_sqrt).2
    (by exact_mod_cast (show 1 ≤ d by omega))
  have hside := S.box_halfDiagonal_le hd
  nlinarith [S.boxHalfSide_pos hd]

/-- Vector displacement from the left endpoint to its port. -/
theorem SiteData.port_left_sub {d : ℕ} (S : SiteData d)
    (e : S.Edge) :
    S.port e 0 - S.vertexPoint (S.edgeLeft e) =
      (S.mesh.δm / 2 - S.boxHalfSide) • S.edgeUnit e := by
  have heq : (⅟2 : ℝ) •
        (S.vertexPoint (S.edgeRight e) - S.vertexPoint (S.edgeLeft e)) =
        (S.mesh.δm / 2) • S.edgeUnit e := by
      unfold SiteData.edgeUnit
      rw [smul_smul]
      congr 1
      field_simp [S.mesh.δm_pos.ne']
      norm_num
  calc
      S.port e 0 - S.vertexPoint (S.edgeLeft e) =
          (S.edgeCenter e - S.vertexPoint (S.edgeLeft e)) -
            S.boxHalfSide • S.edgeUnit e := by
        simp only [SiteData.port, ↓reduceIte]
        abel
      _ = (S.mesh.δm / 2) • S.edgeUnit e - S.boxHalfSide • S.edgeUnit e := by
        rw [SiteData.edgeCenter, midpoint_sub_left, heq]
      _ = (S.mesh.δm / 2 - S.boxHalfSide) • S.edgeUnit e := by
        rw [sub_smul]
/-- The left port is exactly `δ/2-L` from the left lattice vertex. -/
theorem SiteData.port_left_dist {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (e : S.Edge) :
    dist (S.port e 0) (S.vertexPoint (S.edgeLeft e)) =
      S.mesh.δm / 2 - S.boxHalfSide := by
  have hL := S.boxHalfSide_le_half hd
  rw [dist_eq_norm, S.port_left_sub e, norm_smul, S.edgeUnit_norm e, mul_one,
    Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hL)]

/-- Left retained segments remain within `δ/2-L` of their lattice vertex. -/
theorem SiteData.retained_left_subset_ball {d : ℕ} (S : SiteData d)
    (hd : 2 ≤ d) (e : S.Edge) :
    S.retained e 0 ⊆ closedBall (S.vertexPoint (S.edgeLeft e))
      (S.mesh.δm / 2 - S.boxHalfSide) := by
  intro x hx
  change x ∈ segment ℝ (S.vertexPoint (S.edgeLeft e)) (S.port e 0) at hx
  have hport : S.port e 0 ∈ closedBall (S.vertexPoint (S.edgeLeft e))
      (S.mesh.δm / 2 - S.boxHalfSide) := by
    rw [mem_closedBall]
    exact (S.port_left_dist hd e).le
  exact (convex_closedBall (S.vertexPoint (S.edgeLeft e))
    (S.mesh.δm / 2 - S.boxHalfSide)).segment_subset
      (mem_closedBall_self (by rw [← S.port_left_dist hd e]; exact dist_nonneg)) hport hx

private theorem q3_add_sub_comm {d : ℕ} (a b c : Rd d) : a + b - c = (a - c) + b := by
  abel

/-- Vector displacement from the right endpoint to its port. -/
theorem SiteData.port_right_sub {d : ℕ} (S : SiteData d)
    (e : S.Edge) :
    S.port e 1 - S.vertexPoint (S.edgeRight e) =
      (S.boxHalfSide - S.mesh.δm / 2) • S.edgeUnit e := by
  have heq : (⅟2 : ℝ) •
        (S.vertexPoint (S.edgeLeft e) - S.vertexPoint (S.edgeRight e)) =
        -(S.mesh.δm / 2) • S.edgeUnit e := by
      unfold SiteData.edgeUnit
      rw [smul_smul]
      have hs : -(S.mesh.δm / 2) * S.mesh.δm⁻¹ = -(⅟2 : ℝ) := by
        field_simp [S.mesh.δm_pos.ne']
        norm_num
      rw [hs, neg_smul, ← smul_neg, neg_sub]
  calc
      S.port e 1 - S.vertexPoint (S.edgeRight e) =
          (S.edgeCenter e - S.vertexPoint (S.edgeRight e)) +
            S.boxHalfSide • S.edgeUnit e := by
        simp only [SiteData.port, Fin.isValue]
        exact q3_add_sub_comm _ _ _
      _ = -(S.mesh.δm / 2) • S.edgeUnit e + S.boxHalfSide • S.edgeUnit e := by
        rw [SiteData.edgeCenter, midpoint_sub_right, heq]
      _ = (S.boxHalfSide - S.mesh.δm / 2) • S.edgeUnit e := by
        rw [sub_smul, neg_smul]
        abel
/-- The right port is exactly `δ/2-L` from the right lattice vertex. -/
theorem SiteData.port_right_dist {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (e : S.Edge) :
    dist (S.port e 1) (S.vertexPoint (S.edgeRight e)) =
      S.mesh.δm / 2 - S.boxHalfSide := by
  have hL := S.boxHalfSide_le_half hd
  rw [dist_eq_norm, S.port_right_sub e, norm_smul, S.edgeUnit_norm e, mul_one,
    Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr hL)]
  ring

/-- The left port lies on its parent lattice edge. -/
theorem SiteData.port_left_mem_edge {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (e : S.Edge) :
    S.port e 0 ∈ segment ℝ (S.vertexPoint (S.edgeLeft e))
      (S.vertexPoint (S.edgeRight e)) := by
  rw [segment_eq_image']
  let t : ℝ := (S.mesh.δm / 2 - S.boxHalfSide) / S.mesh.δm
  refine ⟨t, ⟨?_, ?_⟩, ?_⟩
  · dsimp [t]
    exact div_nonneg (sub_nonneg.mpr (S.boxHalfSide_le_half hd)) S.mesh.δm_pos.le
  · dsimp [t]
    have hL := S.boxHalfSide_pos hd
    apply (div_le_iff₀ S.mesh.δm_pos).2
    linarith [S.mesh.δm_pos]
  · have ht : t • (S.vertexPoint (S.edgeRight e) -
        S.vertexPoint (S.edgeLeft e)) =
        (S.mesh.δm / 2 - S.boxHalfSide) • S.edgeUnit e := by
      unfold SiteData.edgeUnit
      rw [smul_smul]
      congr 1
    change S.vertexPoint (S.edgeLeft e) + t •
      (S.vertexPoint (S.edgeRight e) - S.vertexPoint (S.edgeLeft e)) = S.port e 0
    rw [ht, ← S.port_left_sub e]
    abel

/-- The right port lies on its parent lattice edge. -/
theorem SiteData.port_right_mem_edge {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (e : S.Edge) :
    S.port e 1 ∈ segment ℝ (S.vertexPoint (S.edgeLeft e))
      (S.vertexPoint (S.edgeRight e)) := by
  rw [segment_eq_image']
  let t : ℝ := (S.mesh.δm / 2 + S.boxHalfSide) / S.mesh.δm
  refine ⟨t, ⟨?_, ?_⟩, ?_⟩
  · dsimp [t]
    exact div_nonneg (by linarith [S.mesh.δm_pos, S.boxHalfSide_pos hd])
      S.mesh.δm_pos.le
  · dsimp [t]
    apply (div_le_iff₀ S.mesh.δm_pos).2
    linarith [S.boxHalfSide_le_half hd]
  · have ht : t • (S.vertexPoint (S.edgeRight e) -
        S.vertexPoint (S.edgeLeft e)) =
        (S.mesh.δm / 2 + S.boxHalfSide) • S.edgeUnit e := by
      unfold SiteData.edgeUnit
      rw [smul_smul]
      congr 1
    have hwhole : S.vertexPoint (S.edgeRight e) -
        S.vertexPoint (S.edgeLeft e) = S.mesh.δm • S.edgeUnit e := by
      unfold SiteData.edgeUnit
      rw [smul_smul]
      simp [S.mesh.δm_pos.ne']
    have hport := S.port_right_sub e
    -- the right endpoint equals the left endpoint plus the full edge vector
    have hsum : S.vertexPoint (S.edgeRight e) =
        S.vertexPoint (S.edgeLeft e) + S.mesh.δm • S.edgeUnit e := by
      rw [← hwhole]
      abel
    rw [hsum] at hport
    change S.vertexPoint (S.edgeLeft e) + t •
      (S.vertexPoint (S.edgeRight e) - S.vertexPoint (S.edgeLeft e)) = S.port e 1
    rw [ht]
    calc
      _ = (S.vertexPoint (S.edgeLeft e) + S.mesh.δm • S.edgeUnit e) +
            (S.boxHalfSide - S.mesh.δm / 2) • S.edgeUnit e := by
          rw [add_assoc, ← add_smul]
          congr 1
          ring_nf
      _ = S.port e 1 := by
          calc
            _ = (S.port e 1 -
                (S.vertexPoint (S.edgeLeft e) + S.mesh.δm • S.edgeUnit e)) +
                (S.vertexPoint (S.edgeLeft e) + S.mesh.δm • S.edgeUnit e) := by
                  rw [hport]
                  abel
            _ = _ := sub_add_cancel _ _

/-- A retained half is a subsegment of its parent lattice edge. -/
theorem SiteData.retained_subset_edge {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (e : S.Edge) (i : Fin 2) :
    S.retained e i ⊆ segment ℝ (S.vertexPoint (S.edgeLeft e))
      (S.vertexPoint (S.edgeRight e)) := by
  fin_cases i
  · exact (convex_segment _ _).segment_subset (left_mem_segment (𝕜 := ℝ) _ _)
      (S.port_left_mem_edge hd e)
  · exact (convex_segment _ _).segment_subset (S.port_right_mem_edge hd e)
      (right_mem_segment (𝕜 := ℝ) _ _)

/-- A reserved box is at least `δ/4` from a retained segment of a different edge. -/
theorem SiteData.box_other_retained_separated {d : ℕ} (S : SiteData d)
    (hd : 2 ≤ d) (e f : S.Edge) (hef : e ≠ f) (i : Fin 2)
    {x y : Rd d} (hx : x ∈ S.box e) (hy : y ∈ S.retained f i) :
    S.mesh.δm / 4 ≤ dist x y := by
  have h₁ := HigherDimLQGMetric.lemma41_tree_edge_adj S.mesh.tree_le e
  have h₂ := HigherDimLQGMetric.lemma41_tree_edge_adj S.mesh.tree_le f
  have hne := HigherDimLQGMetric.lemma41_tree_edges_ne e f hef
  have hcent : S.mesh.δm / 2 ≤ dist (S.edgeCenter e) y :=
    HigherDimLQGMetric.le_dist_midpoint_latticeSegment S.mesh.δm_pos
      h₁ h₂ hne (S.retained_subset_edge hd f i hy)
  have hbox : dist x (S.edgeCenter e) ≤ S.mesh.δm / 64 :=
    (mem_closedBall.mp (S.box_subset_center_ball hd e hx)).trans (S.box_halfDiagonal_le hd)
  have htri := dist_triangle (S.edgeCenter e) x y
  have hbox' : dist (S.edgeCenter e) x ≤ S.mesh.δm / 64 := by
    rw [dist_comm (S.edgeCenter e) x]
    exact hbox
  linarith [S.mesh.δm_pos]

/-- One coordinate of an oriented lattice edge is exactly one mesh unit. -/
theorem SiteData.edge_axis {d : ℕ} (S : SiteData d) (e : S.Edge) :
    ∃ i : Fin d,
      (S.vertexPoint (S.edgeRight e)) i -
        (S.vertexPoint (S.edgeLeft e)) i = S.mesh.δm ∨
      (S.vertexPoint (S.edgeRight e)) i -
        (S.vertexPoint (S.edgeLeft e)) i = -S.mesh.δm := by
  have h := HigherDimLQGMetric.lemma41_tree_edge_adj S.mesh.tree_le e
  change ∃ i,
      ((S.edgeRight e).1 i = (S.edgeLeft e).1 i + 1 ∨
        (S.edgeLeft e).1 i = (S.edgeRight e).1 i + 1) ∧
      ∀ j, j ≠ i → (S.edgeRight e).1 j = (S.edgeLeft e).1 j at h
  obtain ⟨i, hi, _⟩ := h
  refine ⟨i, ?_⟩
  simp only [SiteData.vertexPoint, HigherDimLQGMetric.Routing.latticePoint_apply]
  rcases hi with hi | hi
  · left
    have hi' : ((S.edgeRight e).1 i : ℝ) = ((S.edgeLeft e).1 i : ℝ) + 1 := by
      exact_mod_cast hi
    rw [hi']
    ring
  · right
    have hi' : ((S.edgeLeft e).1 i : ℝ) = ((S.edgeRight e).1 i : ℝ) + 1 := by
      exact_mod_cast hi
    rw [hi']
    ring

/-- The selected edge direction has a coordinate of magnitude one. -/
theorem SiteData.edgeUnit_axis {d : ℕ} (S : SiteData d) (e : S.Edge) :
    ∃ i : Fin d, (S.edgeUnit e) i = 1 ∨ (S.edgeUnit e) i = -1 := by
  obtain ⟨i, hi | hi⟩ := S.edge_axis e
  · refine ⟨i, Or.inl ?_⟩
    unfold SiteData.edgeUnit
    simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    rw [hi]
    exact inv_mul_cancel₀ S.mesh.δm_pos.ne'
  · refine ⟨i, Or.inr ?_⟩
    unfold SiteData.edgeUnit
    simp only [PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul]
    rw [hi]
    field_simp [S.mesh.δm_pos.ne']

/-- A ray reaches an axis-aligned box for the first time at the specified face. -/
private theorem q3_segment_box_face {d : ℕ} {v m p u x : Rd d}
    {a L : ℝ} (ha : L < a)
    (haxis : ∃ i : Fin d, u i = 1 ∨ u i = -1)
    (hm : m - v = a • u) (hp : p - v = (a - L) • u)
    (hx : x ∈ segment ℝ v p)
    (hbox : ∀ i, |x i - m i| ≤ L) : x = p := by
  rw [segment_eq_image'] at hx
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := hx
  obtain ⟨i, hi⟩ := haxis
  have hcoord : (v + t • (p - v)) i - m i = (t * (a - L) - a) * u i := by
    have hvec : (v + t • (p - v)) - m = (t * (a - L) - a) • u := by
      calc
        _ = t • (p - v) - (m - v) := by abel
        _ = t • ((a - L) • u) - a • u := by rw [hp, hm]
        _ = (t * (a - L) - a) • u := by rw [smul_smul, sub_smul]
    have hi' := congrArg (fun z : Rd d => z i) hvec
    simpa only [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul] using hi'
  have hb := hbox i
  rw [hcoord] at hb
  have hlow : -L ≤ (t * (a - L) - a) * u i := (abs_le.mp hb).1
  have hu : u i = 1 ∨ u i = -1 := hi
  have hparam : t = 1 := by
    by_contra hne
    have htlt : t < 1 := lt_of_le_of_ne ht1 hne
    have hprod : 0 < (a - L) * (1 - t) :=
      mul_pos (sub_pos.mpr ha) (sub_pos.mpr htlt)
    rcases hu with hu | hu
    · rw [hu] at hlow
      nlinarith
    · have hhigh : (t * (a - L) - a) * u i ≤ L := (abs_le.mp hb).2
      rw [hu] at hhigh
      nlinarith
  subst t
  simp

theorem SiteData.edgeCenter_sub_left_vec {d : ℕ} (S : SiteData d) (e : S.Edge) :
    S.edgeCenter e - S.vertexPoint (S.edgeLeft e) =
      (S.mesh.δm / 2) • S.edgeUnit e := by
  rw [SiteData.edgeCenter, midpoint_sub_left]
  unfold SiteData.edgeUnit
  rw [smul_smul]
  congr 1
  field_simp [S.mesh.δm_pos.ne']
  norm_num

theorem SiteData.edgeCenter_sub_right_vec {d : ℕ} (S : SiteData d) (e : S.Edge) :
    S.edgeCenter e - S.vertexPoint (S.edgeRight e) =
      (S.mesh.δm / 2) • (-S.edgeUnit e) := by
  have hwhole : S.vertexPoint (S.edgeRight e) - S.vertexPoint (S.edgeLeft e) =
      S.mesh.δm • S.edgeUnit e := by
    unfold SiteData.edgeUnit
    rw [smul_smul]
    simp [S.mesh.δm_pos.ne']
  calc
    _ = (S.edgeCenter e - S.vertexPoint (S.edgeLeft e)) -
          (S.vertexPoint (S.edgeRight e) - S.vertexPoint (S.edgeLeft e)) := by abel
    _ = (S.mesh.δm / 2) • S.edgeUnit e - S.mesh.δm • S.edgeUnit e := by
      rw [S.edgeCenter_sub_left_vec e, hwhole]
    _ = (S.mesh.δm / 2) • (-S.edgeUnit e) := by
      rw [smul_neg, ← neg_smul, ← sub_smul]
      congr 1
      ring

/-- Both ports belong to the closed reserved coordinate box. -/
theorem SiteData.port_mem_box {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (e : S.Edge) (j : Fin 2) : S.port e j ∈ S.box e := by
  intro i
  have hcoord : |(S.edgeUnit e) i| ≤ 1 := by
    have h := HigherDimLQGMetric.Routing.abs_coord_sub_le_dist
      (S.edgeUnit e) 0 i
    simpa [S.edgeUnit_norm e, Real.dist_eq] using h
  have hL := (S.boxHalfSide_pos hd).le
  fin_cases j
  · simpa [SiteData.port, abs_mul, abs_of_nonneg hL] using
      mul_le_mul_of_nonneg_left hcoord hL
  · simpa [SiteData.port, abs_mul, abs_of_nonneg hL] using
      mul_le_mul_of_nonneg_left hcoord hL

/-- The own-edge box meets the left retained half exactly at its port. -/
theorem SiteData.box_inter_retained_left {d : ℕ} (S : SiteData d)
    (hd : 2 ≤ d) (e : S.Edge) :
    S.box e ∩ S.retained e 0 = {S.port e 0} := by
  ext x
  constructor
  · rintro ⟨hbox, hseg⟩
    change x ∈ segment ℝ (S.vertexPoint (S.edgeLeft e)) (S.port e 0) at hseg
    have ha : S.boxHalfSide < S.mesh.δm / 2 := by
      have hside := S.boxHalfSide_le_half hd
      have hdiag := S.box_halfDiagonal_le hd
      have hroot : 1 ≤ Real.sqrt d := (Real.one_le_sqrt).2
        (by exact_mod_cast (show 1 ≤ d by omega))
      nlinarith [S.mesh.δm_pos, S.boxHalfSide_pos hd]
    have h := q3_segment_box_face ha (S.edgeUnit_axis e)
      (S.edgeCenter_sub_left_vec e) (S.port_left_sub e) hseg hbox
    exact Set.mem_singleton_iff.mpr h
  · intro hx
    have hx' : x = S.port e 0 := Set.mem_singleton_iff.mp hx
    subst x
    exact ⟨S.port_mem_box hd e 0, right_mem_segment (𝕜 := ℝ) _ _⟩

/-- The own-edge box meets the right retained half exactly at its port. -/
theorem SiteData.box_inter_retained_right {d : ℕ} (S : SiteData d)
    (hd : 2 ≤ d) (e : S.Edge) :
    S.box e ∩ S.retained e 1 = {S.port e 1} := by
  ext x
  constructor
  · rintro ⟨hbox, hseg⟩
    change x ∈ segment ℝ (S.port e 1) (S.vertexPoint (S.edgeRight e)) at hseg
    rw [segment_symm ℝ] at hseg
    have ha : S.boxHalfSide < S.mesh.δm / 2 := by
      have hdiag := S.box_halfDiagonal_le hd
      have hroot : 1 ≤ Real.sqrt d := (Real.one_le_sqrt).2
        (by exact_mod_cast (show 1 ≤ d by omega))
      nlinarith [S.mesh.δm_pos, S.boxHalfSide_pos hd]
    have haxis : ∃ i : Fin d,
        (-S.edgeUnit e) i = 1 ∨ (-S.edgeUnit e) i = -1 := by
      obtain ⟨i, hi | hi⟩ := S.edgeUnit_axis e
      · exact ⟨i, Or.inr (by simp [hi])⟩
      · exact ⟨i, Or.inl (by simp [hi])⟩
    have hp : S.port e 1 - S.vertexPoint (S.edgeRight e) =
        (S.mesh.δm / 2 - S.boxHalfSide) • (-S.edgeUnit e) := by
      rw [S.port_right_sub e, smul_neg, ← neg_smul]
      congr 1
      ring
    have h := q3_segment_box_face ha haxis
      (S.edgeCenter_sub_right_vec e) hp hseg hbox
    exact Set.mem_singleton_iff.mpr h
  · intro hx
    have hx' : x = S.port e 1 := Set.mem_singleton_iff.mp hx
    subst x
    exact ⟨S.port_mem_box hd e 1, left_mem_segment (𝕜 := ℝ) _ _⟩

/-- Right retained segments remain within `δ/2-L` of their lattice vertex. -/
theorem SiteData.retained_right_subset_ball {d : ℕ} (S : SiteData d)
    (hd : 2 ≤ d) (e : S.Edge) :
    S.retained e 1 ⊆ closedBall (S.vertexPoint (S.edgeRight e))
      (S.mesh.δm / 2 - S.boxHalfSide) := by
  intro x hx
  change x ∈ segment ℝ (S.port e 1) (S.vertexPoint (S.edgeRight e)) at hx
  have hport : S.port e 1 ∈ closedBall (S.vertexPoint (S.edgeRight e))
      (S.mesh.δm / 2 - S.boxHalfSide) := by
    rw [mem_closedBall]
    exact (S.port_right_dist hd e).le
  exact (convex_closedBall (S.vertexPoint (S.edgeRight e))
    (S.mesh.δm / 2 - S.boxHalfSide)).segment_subset
      hport (mem_closedBall_self (by rw [← S.port_right_dist hd e]; exact dist_nonneg)) hx

/-- The lattice vertex to which a retained half-edge attaches. -/
def SiteData.retainedVertex {d : ℕ} (S : SiteData d) (e : S.Edge)
    (i : Fin 2) : S.Vertex :=
  if i = 0 then S.edgeLeft e else S.edgeRight e

theorem SiteData.retained_subset_vertex_ball {d : ℕ} (S : SiteData d)
    (hd : 2 ≤ d) (e : S.Edge) (i : Fin 2) :
    S.retained e i ⊆ closedBall (S.vertexPoint (S.retainedVertex e i))
      (S.mesh.δm / 2 - S.boxHalfSide) := by
  fin_cases i
  · simpa [SiteData.retainedVertex] using S.retained_left_subset_ball hd e
  · simpa [SiteData.retainedVertex] using S.retained_right_subset_ball hd e

/-- Retained halves attached to different lattice vertices stay at least `2L`
apart, whether or not their parent edges share a lattice vertex. -/
theorem SiteData.retained_pair_separated {d : ℕ} (S : SiteData d)
    (hd : 2 ≤ d) (e f : S.Edge) (i j : Fin 2)
    (hv : S.retainedVertex e i ≠ S.retainedVertex f j)
    {x y : Rd d} (hx : x ∈ S.retained e i) (hy : y ∈ S.retained f j) :
    2 * S.boxHalfSide ≤ dist x y := by
  have hcoord : (S.retainedVertex e i).1 ≠ (S.retainedVertex f j).1 := by
    intro h
    exact hv (Subtype.ext h)
  have hvertices : S.mesh.δm ≤
      dist (S.vertexPoint (S.retainedVertex e i))
        (S.vertexPoint (S.retainedVertex f j)) :=
    HigherDimLQGMetric.le_dist_latticePoint S.mesh.δm_pos hcoord
  have hxe : dist x (S.vertexPoint (S.retainedVertex e i)) ≤
      S.mesh.δm / 2 - S.boxHalfSide :=
    mem_closedBall.mp (S.retained_subset_vertex_ball hd e i hx)
  have hyf : dist y (S.vertexPoint (S.retainedVertex f j)) ≤
      S.mesh.δm / 2 - S.boxHalfSide :=
    mem_closedBall.mp (S.retained_subset_vertex_ball hd f j hy)
  have hxe' : dist (S.vertexPoint (S.retainedVertex e i)) x ≤
      S.mesh.δm / 2 - S.boxHalfSide := by
    rw [dist_comm (S.vertexPoint (S.retainedVertex e i)) x]
    exact hxe
  have htri : dist (S.vertexPoint (S.retainedVertex e i))
      (S.vertexPoint (S.retainedVertex f j)) ≤
        dist (S.vertexPoint (S.retainedVertex e i)) x + dist x y +
          dist y (S.vertexPoint (S.retainedVertex f j)) := by
    calc
      _ ≤ dist (S.vertexPoint (S.retainedVertex e i)) x +
          dist x (S.vertexPoint (S.retainedVertex f j)) := dist_triangle _ _ _
      _ ≤ dist (S.vertexPoint (S.retainedVertex e i)) x +
          (dist x y + dist y (S.vertexPoint (S.retainedVertex f j))) := by
        gcongr
        exact dist_triangle _ _ _
      _ = _ := by ring
  linarith

theorem SiteData.edgeCenter_dist_right {d : ℕ} (S : SiteData d) (e : S.Edge) :
    dist (S.edgeCenter e) (S.vertexPoint (S.edgeRight e)) = S.mesh.δm / 2 := by
  rw [dist_eq_norm]
  exact HigherDimLQGMetric.Routing.norm_midpoint_sub_right (S.edgePoint_dist e)

/-- (F4)/(mesh geometry d): a reserved box lies near either endpoint. -/
theorem SiteData.box_near_left {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (e : S.Edge) : S.box e ⊆
      closedBall (S.vertexPoint (S.edgeLeft e))
        (S.mesh.δm / 2 + Real.sqrt d * S.boxHalfSide) := by
  intro x hx
  have hxc : dist x (S.edgeCenter e) ≤ Real.sqrt d * S.boxHalfSide :=
    mem_closedBall.mp (S.box_subset_center_ball hd e hx)
  have hcv := S.edgeCenter_dist_left e
  rw [mem_closedBall]
  calc
    _ ≤ dist x (S.edgeCenter e) + dist (S.edgeCenter e)
      (S.vertexPoint (S.edgeLeft e)) := dist_triangle _ _ _
    _ ≤ Real.sqrt d * S.boxHalfSide + S.mesh.δm / 2 := add_le_add hxc hcv.le
    _ = S.mesh.δm / 2 + Real.sqrt d * S.boxHalfSide := add_comm _ _

theorem SiteData.box_near_right {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (e : S.Edge) : S.box e ⊆
      closedBall (S.vertexPoint (S.edgeRight e))
        (S.mesh.δm / 2 + Real.sqrt d * S.boxHalfSide) := by
  intro x hx
  have hxc : dist x (S.edgeCenter e) ≤ Real.sqrt d * S.boxHalfSide :=
    mem_closedBall.mp (S.box_subset_center_ball hd e hx)
  have hcv := S.edgeCenter_dist_right e
  rw [mem_closedBall]
  calc
    _ ≤ dist x (S.edgeCenter e) + dist (S.edgeCenter e)
      (S.vertexPoint (S.edgeRight e)) := dist_triangle _ _ _
    _ ≤ Real.sqrt d * S.boxHalfSide + S.mesh.δm / 2 := add_le_add hxc hcv.le
    _ = S.mesh.δm / 2 + Real.sqrt d * S.boxHalfSide := add_comm _ _

/-- (F4)/(mesh geometry d): each retained half lies in the stated
endpoint ball. -/
theorem SiteData.retained_near_endpoint {d : ℕ} (S : SiteData d) (hd : 2 ≤ d)
    (e : S.Edge) (i : Fin 2) :
    S.retained e i ⊆ closedBall (S.vertexPoint (S.retainedVertex e i))
      (S.mesh.δm / 2 + Real.sqrt d * S.boxHalfSide) := by
  intro x hx
  have h := S.retained_subset_vertex_ball hd e i hx
  rw [mem_closedBall] at h ⊢
  have hL := S.boxHalfSide_pos hd
  have hroot := Real.sqrt_nonneg (d : ℝ)
  exact h.trans (by nlinarith)

/-- The complete fixed mesh geometry of Part B, (a)–(d). -/
structure SiteMeshGeometry {d : ℕ} (S : SiteData d) : Prop where
  vertex_bounds : ∀ v : S.Vertex,
    3 / 2 + 2 * Real.sqrt d * S.mesh.δm ≤ ‖S.vertexPoint v‖ ∧
      ‖S.vertexPoint v‖ ≤ 5 / 2 - 2 * Real.sqrt d * S.mesh.δm
  vertex_ball_C : ∀ v : S.Vertex,
    closedBall (S.vertexPoint v) (Real.sqrt d * S.mesh.δm) ⊆ interior (siteC d)
  vertex_ball_A : ∀ v : S.Vertex,
    closedBall (S.vertexPoint v) (10 * Real.sqrt d * S.mesh.δm) ⊆ siteA d
  collector_cover : ∀ x ∈ siteC d,
    ∃ v : S.Vertex, dist x (S.vertexPoint v) ≤ 4 * Real.sqrt d * S.mesh.δm
  box_pair : ∀ (e f : S.Edge), e ≠ f → ∀ x ∈ S.box e, ∀ y ∈ S.box f,
    S.mesh.δm / 2 ≤ dist x y
  box_own : ∀ (e : S.Edge) (i : Fin 2),
    S.box e ∩ S.retained e i = {S.port e i}
  box_other : ∀ (e f : S.Edge), e ≠ f → ∀ (i : Fin 2),
    ∀ x ∈ S.box e, ∀ y ∈ S.retained f i, S.mesh.δm / 4 ≤ dist x y
  retained_pair : ∀ (e f : S.Edge) (i j : Fin 2),
    S.retainedVertex e i ≠ S.retainedVertex f j →
    ∀ x ∈ S.retained e i, ∀ y ∈ S.retained f j,
      2 * S.boxHalfSide ≤ dist x y
  box_near_left : ∀ e : S.Edge,
    S.box e ⊆ closedBall (S.vertexPoint (S.edgeLeft e))
      (S.mesh.δm / 2 + Real.sqrt d * S.boxHalfSide)
  box_near_right : ∀ e : S.Edge,
    S.box e ⊆ closedBall (S.vertexPoint (S.edgeRight e))
      (S.mesh.δm / 2 + Real.sqrt d * S.boxHalfSide)
  retained_near : ∀ (e : S.Edge) (i : Fin 2),
    S.retained e i ⊆ closedBall (S.vertexPoint (S.retainedVertex e i))
      (S.mesh.δm / 2 + Real.sqrt d * S.boxHalfSide)

/-- The mesh geometry with exact own-port incidence and quantitative clearance. -/
theorem siteMesh_geometry {d : ℕ} (S : SiteData d) (hd : 2 ≤ d) :
    SiteMeshGeometry S := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    exact siteMesh_vertex_norm_bounds S.mesh.δm_pos v.2
  · intro v
    exact siteMesh_vertex_ball_interior_C hd S.mesh.δm_pos v.2
  · intro v
    exact siteMesh_vertex_ball_A S.mesh.δm_pos S.mesh.δm_small v.2
  · intro x hx
    exact siteMesh_vertex_cover S.mesh.δm_pos S.mesh.δm_small hx
  · intro e f hef x hx y hy
    exact S.box_pair_separated hd e f hef hx hy
  · intro e i
    fin_cases i
    · exact S.box_inter_retained_left hd e
    · exact S.box_inter_retained_right hd e
  · intro e f hef i x hx y hy
    exact S.box_other_retained_separated hd e f hef i hx hy
  · intro e f i j hv x hx y hy
    exact S.retained_pair_separated hd e f i j hv hx hy
  · intro e
    exact S.box_near_left hd e
  · intro e
    exact S.box_near_right hd e
  · intro e i
    exact S.retained_near_endpoint hd e i

end HigherDimLQGContinuity
