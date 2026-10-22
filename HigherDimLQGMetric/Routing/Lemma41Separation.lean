import HigherDimLQGMetric.Routing.Lemma41Crossing

/-! Separation of routing regions for different lattice edges. -/

set_option autoImplicit false

open Set HigherDimLFPP

namespace HigherDimLQGMetric

theorem lemma41_disjoint_routing_regions {d : ℕ} {δ : ℝ} (hδ : 0 < δ)
    {m m' a b : Fin d → ℤ}
    (h : (Topology.latticeGraph d).Adj m m')
    (h' : (Topology.latticeGraph d).Adj a b)
    (hne : s(m, m') ≠ s(a, b)) (hma : m ≠ a) :
    Disjoint
      (routingRegion δ (Topology.latticePoint δ m) (Topology.latticePoint δ m'))
      (routingRegion δ (Topology.latticePoint δ a) (Topology.latticePoint δ b)) := by
  apply Set.disjoint_left.mpr
  intro x hx hx'
  have hball : x ∈ vertBall δ (Topology.latticePoint δ m) :=
    routingRegion_inter_routingRegion_subset hδ h h' hne ⟨hx', hx⟩
  exact Set.disjoint_left.mp (disjoint_routingRegion_vertBall_of_ne hδ h' (Ne.symm hma))
    hx' hball

end HigherDimLQGMetric
