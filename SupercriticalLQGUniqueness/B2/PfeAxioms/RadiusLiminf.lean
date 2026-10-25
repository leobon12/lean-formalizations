import SupercriticalLQGUniqueness.B2.PfeAxioms.InternalRadiusCompact

 










set_option autoImplicit false
noncomputable section

open Set Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeAxioms

 


theorem liminf_setDistance_pos_of_compact_separator
    {G : ℕ → LSCMetric} {D : LSCMetric}
    (hG : Tendsto G atTop (𝓝 D))
    {K L A B : Set ℂ}
    (hK : IsCompact K) (hL : IsCompact L)
    (hneK : K.Nonempty) (hneL : L.Nonempty)
    (hKL : Disjoint K L)
    (hAK : A ⊆ K) (hBL : B ⊆ L) :
    0 < liminf (fun n => ⨅ p ∈ A ×ˢ B, G n p) atTop := by
  obtain ⟨r, hr0, hr⟩ :=
    eventually_compact_setDistance_pos hG hK hL hneK hneL hKL
  have hAB : ∀ᶠ n in atTop, r ≤ ⨅ p ∈ A ×ˢ B, G n p := by
    filter_upwards [hr] with n hn
    refine le_iInf fun p => le_iInf fun hp => ?_
    exact hn p ⟨hAK hp.1, hBL hp.2⟩
  exact hr0.trans_le (Filter.le_liminf_of_le (by isBoundedDefault) hAB)

 


theorem liminf_boundary_radius_pos
    {G : ℕ → LSCMetric} {D : LSCMetric}
    (hG : Tendsto G atTop (𝓝 D))
    {Y : Set ℂ} (hY : Bornology.IsBounded Y)
    (hfront : (frontier Y).Nonempty)
    {x : ℂ} {ε : ℝ} (hε : 0 < ε)
    (hsep : 2 * ε < Metric.infDist x (frontier Y)) :
    0 < liminf (fun n =>
      ⨅ p ∈ Metric.ball x ε ×ˢ Metric.thickening ε (frontier Y),
        G n p) atTop := by
  let K : Set ℂ := Metric.closedBall x ε
  let L : Set ℂ := Metric.cthickening ε (frontier Y)
  have hfrontCompact : IsCompact (frontier Y) :=
    Metric.isCompact_of_isClosed_isBounded isClosed_frontier
      (hY.closure.subset frontier_subset_closure)
  have hK : IsCompact K := isCompact_closedBall x ε
  have hL : IsCompact L := hfrontCompact.cthickening
  have hneK : K.Nonempty := ⟨x, Metric.mem_closedBall_self hε.le⟩
  have hneL : L.Nonempty := by
    obtain ⟨w, hw⟩ := hfront
    exact ⟨w, Metric.self_subset_cthickening _ hw⟩
  have hKL : Disjoint K L := by
    apply Set.disjoint_left.mpr
    intro u hu hv
    change u ∈ Metric.cthickening ε (frontier Y) at hv
    rw [isClosed_frontier.cthickening_eq_biUnion_closedBall hε.le] at hv
    simp only [Set.mem_iUnion] at hv
    obtain ⟨w, hw, huw⟩ := hv
    have hwfar : Metric.infDist x (frontier Y) ≤ dist x w :=
      Metric.infDist_le_dist_of_mem hw
    have hxu : dist x u ≤ ε := by
      simpa only [K, Metric.mem_closedBall, dist_comm] using hu
    have huw' : dist u w ≤ ε := Metric.mem_closedBall.mp huw
    have htri : dist x w ≤ dist x u + dist u w := dist_triangle x u w
    linarith
  apply liminf_setDistance_pos_of_compact_separator hG hK hL hneK hneL hKL
  · exact Metric.ball_subset_closedBall
  · exact Metric.thickening_subset_cthickening ε (frontier Y)

end SupercriticalLQGUniqueness.B2.PfeAxioms
