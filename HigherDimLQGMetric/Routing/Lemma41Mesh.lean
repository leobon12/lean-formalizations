import HigherDimLQGMetric.Routing.Lemma41Pair

/-!
# Mesh geometry for one routing edge

The routing regions supplied by the lattice mesh satisfy the geometric premises of the
two-connector construction.
-/

set_option autoImplicit false

open Set Topology LQGMetric.MetricGeometry HigherDimLFPP

namespace HigherDimLQGMetric

theorem lemma41_mesh_edgeRegions {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {m n : Fin d → ℤ} (hmn : (Topology.latticeGraph d).Adj m n)
    (ρ : Rd d × Rd d → ℝ) (γ : ℝ → Rd d)
    (hγbox : MapsTo γ (Icc (0 : ℝ) 1)
      (centralBox δ (Topology.latticePoint δ m) (Topology.latticePoint δ n)))
    {s t : ℝ} (hcuts : 0 < s ∧ s < t ∧ t < 1) :
    Lemma41EdgeRegions ρ γ s t
      (Topology.latticePoint δ m) (Topology.latticePoint δ n)
      (routingRegion δ (Topology.latticePoint δ m) (Topology.latticePoint δ n))
      (routingRegion δ (Topology.latticePoint δ n) (Topology.latticePoint δ m)) := by
  let v := Topology.latticePoint δ m
  let w := Topology.latticePoint δ n
  have hvw : dist v w = δ := dist_latticePoint_of_adj hδ hmn
  have hboxl : centralBox δ v w ⊆ routingRegion δ v w :=
    centralBox_subset_routingRegion hδ hvw
  have hboxr : centralBox δ v w ⊆ routingRegion δ w v :=
    centralBox_subset_routingRegion_swap hδ hvw
  have hboxballv : Disjoint (centralBox δ v w) (vertBall δ v) :=
    disjoint_centralBox_vertBall hδ hmn m
  have hboxballw : Disjoint (centralBox δ v w) (vertBall δ w) :=
    disjoint_centralBox_vertBall hδ hmn n
  refine {
    left_open := isOpen_routingRegion δ v w
    left_connected := isConnected_routingRegion hδ v w
    right_open := isOpen_routingRegion δ w v
    right_connected := isConnected_routingRegion hδ w v
    vertex_left := mem_routingRegion_self hδ v w
    vertex_right := mem_routingRegion_self hδ w v
    witness_left := hboxl (hγbox (by norm_num))
    witness_right := hboxr (hγbox (by norm_num))
    opposite_excluded := ?_
    left_vertex_off_witness := ?_
    right_vertex_off_witness := ?_
    cuts := hcuts }
  · intro hw
    exact (Set.disjoint_left.mp (disjoint_routingRegion_vertBall hδ hvw)) hw
      (mem_vertBall_self hδ w)
  · rintro ⟨u, hu, hγu⟩
    have hvbox : v ∈ centralBox δ v w := by
      change γ u = v at hγu
      have hmem : γ u ∈ centralBox δ v w := hγbox hu
      exact hγu ▸ hmem
    exact (Set.disjoint_left.mp hboxballv) hvbox
      (mem_vertBall_self hδ v)
  · rintro ⟨u, hu, hγu⟩
    have hwbox : w ∈ centralBox δ v w := by
      change γ u = w at hγu
      have hmem : γ u ∈ centralBox δ v w := hγbox hu
      exact hγu ▸ hmem
    exact (Set.disjoint_left.mp hboxballw) hwbox
      (mem_vertBall_self hδ w)

end HigherDimLQGMetric
