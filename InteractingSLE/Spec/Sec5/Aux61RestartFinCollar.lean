import InteractingSLE.Spec.Sec5.Aux61RestartFinTarget

/-!
# The physical collar at the original right strip end

Packet PROVE-AUX61-R1. The target is `1` in Q. Before the first original upper
contact, the finite interior own prefix cannot contain `1`. If the counterflow
retains positive clearance there, a physical half-disc avoids both histories.
For a selected component whose closure contains this target, the entire
half-disc lies in that component. No counterflow-side junction is used.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open QuantumZipper (H)

namespace InteractingSLE.Sec5.Aux61Restart

/-- Protection of the original right target by the counterflow and the finite
own interior prefix gives a physical target collar in the retained domain. -/
theorem exists_original_right_target_collar {K : Set ℂ} {η : ℝ → ℂ} {r : ℝ}
    (hc : ContinuousOn η (Icc 0 r)) (h0 : η 0 = 0)
    (hH : MapsTo η (Ioc 0 r) H) (hK : (1 : ℂ) ∉ closure K) :
    ∃ δ > 0, ball (1 : ℂ) δ ∩ H ⊆ retainedDomain K η r := by
  have hP := (isCompact_Icc.image_of_continuousOn hc).isClosed
  have hnot : (1 : ℂ) ∉ η '' Icc 0 r := by
    rintro ⟨t, ht, heq⟩
    rcases ht.1.eq_or_lt with heq0 | ht0
    · rw [← heq0, h0] at heq
      exact zero_ne_one heq
    · have h := hH ⟨ht0, ht.2⟩
      rw [heq] at h
      exact (lt_irrefl (0 : ℝ)) (by simpa only [QuantumZipper.H, mem_ofPred_eq, one_im] using h)
  obtain ⟨δ, hδ, hfree⟩ := Metric.mem_nhds_iff.1
    ((isClosed_closure.union hP).isOpen_compl.mem_nhds
      (show (1 : ℂ) ∉ closure K ∪ η '' Icc 0 r from fun h => h.elim hK hnot))
  refine ⟨δ, hδ, fun z hz => ⟨hz.2, ?_⟩⟩
  rintro (hzK | hzP)
  · exact hfree hz.1 (Or.inl (subset_closure hzK))
  · exact hfree hz.1 (Or.inr hzP)

/-- A free target half-disc lies in the selected component if the original
target is in its closure. This is the component marking supplied by the source. -/
theorem target_collar_subset_component {K : Set ℂ} {η : ℝ → ℂ} {r : ℝ} {b : ℂ}
    {δ : ℝ} (hδ : 0 < δ)
    (hfree : ball (1 : ℂ) δ ∩ H ⊆ retainedDomain K η r)
    (hmark : (1 : ℂ) ∈ closure (restartComponent K η r b)) :
    ball (1 : ℂ) δ ∩ H ⊆ restartComponent K η r b := by
  obtain ⟨z, hzD, hzdist⟩ := Metric.mem_closure_iff.1 hmark δ hδ
  have hzball : z ∈ ball (1 : ℂ) δ := by
    rw [mem_ball, dist_comm]
    exact hzdist
  have hzH : z ∈ H := (connectedComponentIn_subset _ _ hzD).1
  rw [restartComponent, connectedComponentIn_eq hzD]
  exact (convex_ball_inter_H (1 : ℂ) δ).isPreconnected.subset_connectedComponentIn
    ⟨hzball, hzH⟩ hfree

/-- The actual original-target collar follows from counterflow protection and
the selected component's original-target mark. Both missing geometric facts
are stated at the physical original target `1`, not at `junR`. -/
theorem exists_original_right_target_component_collar {K : Set ℂ} {η : ℝ → ℂ}
    {r : ℝ} {b : ℂ} (hc : ContinuousOn η (Icc 0 r)) (h0 : η 0 = 0)
    (hH : MapsTo η (Ioc 0 r) H) (hK : (1 : ℂ) ∉ closure K)
    (hmark : (1 : ℂ) ∈ closure (restartComponent K η r b)) :
    ∃ δ > 0, ball (1 : ℂ) δ ∩ H ⊆ restartComponent K η r b := by
  obtain ⟨δ, hδ, hfree⟩ := exists_original_right_target_collar hc h0 hH hK
  exact ⟨δ, hδ, target_collar_subset_component hδ hfree hmark⟩

end InteractingSLE.Sec5.Aux61Restart
