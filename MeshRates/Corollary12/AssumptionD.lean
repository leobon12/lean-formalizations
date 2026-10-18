import MeshRates.Statement.Corollary12
import MeshRates.Theorem11Qualitative
import BouRabeeGwynne.ApproximationGeometry

/-! MR Corollary 1.2, first assertion (MR §7): the mesh hypothesis alone verifies BRG
Assumption D. (4.1) comes from (1.3); (4.2) is MR Theorem 1.1 (9) with `U = B`. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace BouRabeeGwynne.MeshRates

theorem corollary12_assumptionD : MeshRatesCorollary12AssumptionDStatement := by
  intro d hd G N happrox D₀ _hD₀ hbdd hcollar
  have hK : IsCompact (closure D₀) := hbdd.isCompact_closure
  obtain ⟨δ, hδ, hsub⟩ := hK.exists_cthickening_subset_open isOpen_interior hcollar
  rw [Metric.cthickening_closure] at hsub
  refine ⟨δ, hδ, fun r _hr x _hx => ?_⟩
  set B := Metric.closedBall x r ∩ Metric.cthickening δ D₀
  have hBclosed : IsClosed B := Metric.isClosed_closedBall.inter Metric.isClosed_cthickening
  have hBcollar : HasAmbientCollar B G.domain := by
    show closure B ⊆ interior G.domain
    rw [hBclosed.closure_eq]
    exact Set.inter_subset_right.trans hsub
  have hBbdd : Bornology.IsBounded B := Metric.isBounded_closedBall.subset Set.inter_subset_left
  refine ⟨fun η hη => ?_, fun h hh => ?_⟩
  · filter_upwards [N.eventually_vertex_dist_le happrox hη] with n hn z hz
    exact hn z (interior_subset (hsub hz.2))
  · exact theorem11_qualitative d hd G B hBbdd hBcollar (N.mesh_tendsto_zero happrox) h hh

end BouRabeeGwynne.MeshRates
