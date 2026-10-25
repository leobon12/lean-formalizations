import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Analysis.Normed.Group.Pointwise
import SupercriticalLQGUniqueness.B2.PfeAxioms.Section4BufferedFinite

 


set_option autoImplicit false
noncomputable section

open Set Topology Metric
open scoped Pointwise

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

theorem exists_connected_compact_buffer
    (U : TopologicalSpace.Opens ℂ) (hU : IsConnected (U : Set ℂ))
    (x y : U) :
    ∃ V : TopologicalSpace.Opens ℂ,
      IsConnected (V : Set ℂ) ∧ IsCompact (closure (V : Set ℂ)) ∧
        closure (V : Set ℂ) ⊆ U ∧ (x : ℂ) ∈ V ∧ (y : ℂ) ∈ V := by
  let j : JoinedIn (U : Set ℂ) (x : ℂ) (y : ℂ) :=
    (U.isOpen.isConnected_iff_isPathConnected.mp hU).joinedIn
      (x : ℂ) x.property (y : ℂ) y.property
  let K : Set ℂ := Set.range j.somePath
  have hK : IsCompact K := isCompact_range j.somePath.continuous
  have hKconn : IsConnected K := isConnected_range j.somePath.continuous
  have hKU : K ⊆ U := by
    rintro z ⟨t, rfl⟩
    exact j.somePath_mem t
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open U.isOpen hKU
  let V : TopologicalSpace.Opens ℂ :=
    ⟨thickening δ K, isOpen_thickening⟩
  have hVconn : IsConnected (V : Set ℂ) := by
    change IsConnected (thickening δ K)
    rw [← add_ball_zero, ← Set.add_image_prod]
    exact (hKconn.prod (Metric.isConnected_ball hδ)).image
      (fun p : ℂ × ℂ => p.1 + p.2) continuous_add.continuousOn
  have hVc : IsCompact (closure (V : Set ℂ)) :=
    (hK.cthickening (r := δ)).of_isClosed_subset isClosed_closure
      (closure_thickening_subset_cthickening δ K)
  have hVU : closure (V : Set ℂ) ⊆ U :=
    (closure_thickening_subset_cthickening δ K).trans hδU
  have hxK : (x : ℂ) ∈ K := ⟨0, by simp⟩
  have hyK : (y : ℂ) ∈ K := ⟨1, by simp⟩
  exact ⟨V, hVconn, hVc, hVU,
    (self_subset_thickening hδ K) hxK,
    (self_subset_thickening hδ K) hyK⟩

end SupercriticalLQGUniqueness.B2.PfeAxioms
