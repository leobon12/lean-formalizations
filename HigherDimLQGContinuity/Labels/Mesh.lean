import HigherDimLQGContinuity.Core.Interfaces
import HigherDimLQGMetric.Events.AnnulusGeometry
import HigherDimLQGMetric.Topology.NonSepMesh
import HigherDimLQGMetric.Routing.Collector

/-!
# The finite connected site mesh

The site mesh is the lattice mesh of the buffered closed annulus in Part B.
Connectivity and finiteness are specialized from the pinned
`HigherDimLQGMetric` mesh theorems.
-/

set_option autoImplicit false

noncomputable section

open Set Metric
open HigherDimLFPP (Rd)

namespace HigherDimLQGContinuity

open HigherDimLQGMetric

/-- Buffered closed annulus used to select the site mesh. -/
def siteMeshRing (d : ℕ) (δ : ℝ) : Set (Rd d) :=
  annCl 0 (3 / 2 + 3 * Real.sqrt d * δ) (5 / 2 - 3 * Real.sqrt d * δ)

/-- The buffered annulus remains connected at the mesh scale. -/
theorem siteMeshRing_connected {d : ℕ} (hd : 2 ≤ d) {δ : ℝ}
    (hδ : 0 ≤ δ) (hsmall : 6 * Real.sqrt d * δ ≤ 1) :
    IsConnected (siteMeshRing d δ) := by
  have ha : 0 < 3 / 2 + 3 * Real.sqrt d * δ := by
    have : 0 ≤ Real.sqrt d * δ := mul_nonneg (Real.sqrt_nonneg _) hδ
    linarith
  have hab : 3 / 2 + 3 * Real.sqrt d * δ ≤ 5 / 2 - 3 * Real.sqrt d * δ := by
    linarith
  exact HigherDimLQGMetric.isConnected_annCl hd 0 ha hab

/-- The buffered annulus is bounded. -/
theorem siteMeshRing_bounded {d : ℕ} (δ : ℝ) :
    Bornology.IsBounded (siteMeshRing d δ) := by
  apply (isBounded_closedBall : Bornology.IsBounded
    (closedBall (0 : Rd d) (5 / 2 - 3 * Real.sqrt d * δ))).subset
  intro x hx
  exact hx.2

/-- A finite spanning tree exists in the site mesh. -/
theorem exists_siteMesh_tree {d : ℕ} (hd : 2 ≤ d) {δ : ℝ}
    (hδ : 0 < δ) (hsmall : 6 * Real.sqrt d * δ ≤ 1) :
    ∃ T ≤ HigherDimLQGMetric.Topology.meshGraph δ (siteMeshRing d δ), T.IsTree := by
  have hconn : (HigherDimLQGMetric.Topology.meshGraph δ (siteMeshRing d δ)).Connected :=
    HigherDimLQGMetric.Topology.meshGraph_connected hδ
      (siteMeshRing_connected hd hδ.le hsmall).isPreconnected
      (siteMeshRing_connected hd hδ.le hsmall).nonempty
  exact hconn.exists_isTree_le

/-- The site mesh vertex set is finite. -/
theorem siteMesh_vertices_finite {d : ℕ} {δ : ℝ} (hδ : 0 < δ) :
    (HigherDimLQGMetric.Topology.meshVertices δ (siteMeshRing d δ)).Finite :=
  HigherDimLQGMetric.Topology.meshVertices_finite hδ (siteMeshRing_bounded δ)

/-- Every mesh vertex lies two mesh diagonals inside the collector annulus. -/
theorem siteMesh_vertex_norm_bounds {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {m : Fin d → ℤ}
    (hm : m ∈ HigherDimLQGMetric.Topology.meshVertices δ (siteMeshRing d δ)) :
    3 / 2 + 2 * Real.sqrt d * δ ≤
        ‖HigherDimLQGMetric.Topology.latticePoint δ m‖ ∧
      ‖HigherDimLQGMetric.Topology.latticePoint δ m‖ ≤
        5 / 2 - 2 * Real.sqrt d * δ := by
  let v := HigherDimLQGMetric.Topology.latticePoint δ m
  obtain ⟨p, hp, hvp⟩ :=
    HigherDimLQGMetric.exists_mem_sphere_dist_le_of_mem_meshVertices hδ.le hm
  have h1 : ‖p‖ ≤ ‖v‖ + Real.sqrt d * δ := by
    apply norm_le_norm_add_const_of_dist_le
    rw [dist_comm p v]
    exact hvp
  have h2 : ‖v‖ ≤ ‖p‖ + Real.sqrt d * δ :=
    norm_le_norm_add_const_of_dist_le hvp
  have hp' : 3 / 2 + 3 * Real.sqrt d * δ ≤ ‖p‖ ∧
      ‖p‖ ≤ 5 / 2 - 3 * Real.sqrt d * δ := by
    simpa only [siteMeshRing, annCl, mem_ofPred_eq, sub_zero] using hp
  constructor <;> dsimp [v] at * <;> linarith

private theorem siteMesh_norm_bounds_of_closedBall {d : ℕ} {δ R : ℝ}
    (hδ : 0 < δ) {m : Fin d → ℤ}
    (hm : m ∈ HigherDimLQGMetric.Topology.meshVertices δ (siteMeshRing d δ))
    {x : Rd d}
    (hx : x ∈ closedBall (HigherDimLQGMetric.Topology.latticePoint δ m) R) :
    3 / 2 + 2 * Real.sqrt d * δ - R ≤ ‖x‖ ∧
      ‖x‖ ≤ 5 / 2 - 2 * Real.sqrt d * δ + R := by
  let v := HigherDimLQGMetric.Topology.latticePoint δ m
  have hv := siteMesh_vertex_norm_bounds hδ hm
  have hdist : dist x v ≤ R := mem_closedBall.mp hx
  have hdist' : dist v x ≤ R := by
    rw [dist_comm v x]
    exact hdist
  have h1 : ‖v‖ ≤ ‖x‖ + R := norm_le_norm_add_const_of_dist_le hdist'
  have h2 : ‖x‖ ≤ ‖v‖ + R := norm_le_norm_add_const_of_dist_le hdist
  constructor <;> dsimp [v] at * <;> linarith

/-- A mesh vertex has a full mesh-diagonal ball in the collector interior. -/
theorem siteMesh_vertex_ball_interior_C {d : ℕ} (hd : 2 ≤ d) {δ : ℝ} (hδ : 0 < δ)
    {m : Fin d → ℤ}
    (hm : m ∈ HigherDimLQGMetric.Topology.meshVertices δ (siteMeshRing d δ)) :
    closedBall (HigherDimLQGMetric.Topology.latticePoint δ m) (Real.sqrt d * δ) ⊆
      interior (siteC d) := by
  intro x hx
  have hb := siteMesh_norm_bounds_of_closedBall hδ hm hx
  have hsd : 0 < Real.sqrt d * δ := by
    have hdpos : 0 < (d : ℝ) := by exact_mod_cast (show 0 < d by omega)
    exact mul_pos (Real.sqrt_pos.2 hdpos) hδ
  have hAnn : x ∈ ann (0 : Rd d) (3 / 2) (5 / 2) := by
    simp only [ann, mem_ofPred_eq, sub_zero]
    constructor <;> linarith [hb.1, hb.2]
  have hsub : ann (0 : Rd d) (3 / 2) (5 / 2) ⊆ siteC d := by
    intro y hy
    exact ⟨hy.1.le, hy.2.le⟩
  have hopen : IsOpen (ann (0 : Rd d) (3 / 2) (5 / 2)) := isOpen_ann _ _ _
  exact (mem_interior_iff_mem_nhds).2
    (Filter.mem_of_superset (hopen.mem_nhds hAnn) hsub)

/-- A ten-diagonal ball at a mesh vertex lies in the site inspection annulus. -/
theorem siteMesh_vertex_ball_A {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (hsmall : Real.sqrt d * δ ≤ 1 / 40)
    {m : Fin d → ℤ}
    (hm : m ∈ HigherDimLQGMetric.Topology.meshVertices δ (siteMeshRing d δ)) :
    closedBall (HigherDimLQGMetric.Topology.latticePoint δ m)
      (10 * Real.sqrt d * δ) ⊆ siteA d := by
  intro x hx
  have hb := siteMesh_norm_bounds_of_closedBall hδ hm hx
  simp only [siteA, annA, ann, mem_ofPred_eq, sub_zero]
  constructor <;> linarith [hb.1, hb.2]

private theorem siteMesh_radial_rescale {d : ℕ} (x : Rd d) (hx : 0 < ‖x‖)
    {r : ℝ} (hr : 0 ≤ r) :
    ∃ p : Rd d, ‖p‖ = r ∧ dist x p = |‖x‖ - r| := by
  let p : Rd d := (r / ‖x‖) • x
  have hp : ‖p‖ = r := by
    dsimp [p]
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (div_nonneg hr hx.le)]
    exact div_mul_cancel₀ r hx.ne'
  refine ⟨p, hp, ?_⟩
  have hfactor : x - p = (1 - r / ‖x‖) • x := by
    dsimp [p]
    rw [sub_smul, one_smul]
  rw [dist_eq_norm, hfactor, norm_smul, Real.norm_eq_abs]
  calc
    |1 - r / ‖x‖| * ‖x‖ = |(1 - r / ‖x‖) * ‖x‖| := by
      rw [abs_mul, abs_of_pos hx]
    _ = |‖x‖ - r| := by
      congr 1
      field_simp

private theorem siteMesh_near_ring {d : ℕ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hsmall : Real.sqrt d * δ ≤ 1 / 40)
    {x : Rd d} (hx : x ∈ siteC d) :
    ∃ p ∈ siteMeshRing d δ, dist x p ≤ 3 * Real.sqrt d * δ := by
  have hsd : 0 ≤ Real.sqrt d * δ := mul_nonneg (Real.sqrt_nonneg _) hδ
  have hxnorm : 3 / 2 ≤ ‖x‖ ∧ ‖x‖ ≤ 5 / 2 := by
    simpa only [siteC, annCl, mem_ofPred_eq, sub_zero] using hx
  have hxpos : 0 < ‖x‖ := by linarith [hxnorm.1]
  let a : ℝ := 3 / 2 + 3 * Real.sqrt d * δ
  let b : ℝ := 5 / 2 - 3 * Real.sqrt d * δ
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have hb : 0 ≤ b := by dsimp [b]; linarith
  have hab : a ≤ b := by dsimp [a, b]; linarith
  by_cases hlo : ‖x‖ < a
  · obtain ⟨p, hpn, hxp⟩ := siteMesh_radial_rescale x hxpos ha
    refine ⟨p, ?_, ?_⟩
    · simpa only [siteMeshRing, annCl, mem_ofPred_eq, sub_zero, hpn] using
        (show a ≤ ‖p‖ ∧ ‖p‖ ≤ b by rw [hpn]; exact ⟨le_rfl, hab⟩)
    · rw [hxp, abs_of_nonpos (by linarith : ‖x‖ - a ≤ 0)]
      dsimp [a]
      linarith [hxnorm.1]
  · by_cases hhi : b < ‖x‖
    · obtain ⟨p, hpn, hxp⟩ := siteMesh_radial_rescale x hxpos hb
      refine ⟨p, ?_, ?_⟩
      · simpa only [siteMeshRing, annCl, mem_ofPred_eq, sub_zero, hpn] using
          (show a ≤ ‖p‖ ∧ ‖p‖ ≤ b by rw [hpn]; exact ⟨hab, le_rfl⟩)
      · rw [hxp, abs_of_nonneg (by linarith : 0 ≤ ‖x‖ - b)]
        dsimp [b]
        linarith [hxnorm.2]
    · refine ⟨x, ?_, ?_⟩
      · simpa only [siteMeshRing, annCl, mem_ofPred_eq, sub_zero] using
          (show a ≤ ‖x‖ ∧ ‖x‖ ≤ b by exact ⟨le_of_not_gt hlo, le_of_not_gt hhi⟩)
      · simp only [dist_self]
        positivity

/-- Every collector point is within four mesh diagonals of a mesh vertex. -/
theorem siteMesh_vertex_cover {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    (hsmall : Real.sqrt d * δ ≤ 1 / 40)
    {x : Rd d} (hx : x ∈ siteC d) :
    ∃ m : HigherDimLQGMetric.Topology.meshVertices δ (siteMeshRing d δ),
      dist x (HigherDimLQGMetric.Topology.latticePoint δ m.1) ≤
        4 * Real.sqrt d * δ := by
  obtain ⟨p, hp, hxp⟩ := siteMesh_near_ring hδ.le hsmall hx
  let m := HigherDimLQGMetric.Topology.floorCorner δ p
  have hm : m ∈ HigherDimLQGMetric.Topology.meshVertices δ (siteMeshRing d δ) :=
    HigherDimLQGMetric.floorCorner_mem_meshVertices hδ hp
  refine ⟨⟨m, hm⟩, ?_⟩
  have hpm : dist p (HigherDimLQGMetric.Topology.latticePoint δ m) ≤ Real.sqrt d * δ :=
    HigherDimLQGMetric.dist_latticePoint_floorCorner_le hδ p
  calc
    dist x (HigherDimLQGMetric.Topology.latticePoint δ m) ≤
        dist x p + dist p (HigherDimLQGMetric.Topology.latticePoint δ m) :=
      dist_triangle _ _ _
    _ ≤ 3 * Real.sqrt d * δ + Real.sqrt d * δ := add_le_add hxp hpm
    _ = 4 * Real.sqrt d * δ := by ring

end HigherDimLQGContinuity
