/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61RestartBdryWindow
import InteractingSLE.Spec.Sec7.PocketJordan
import InteractingSLE.Foundations.Topology.PathComplement.Torhorst

/-! # Boundary control for a retained component in a bounded coordinate -/

set_option autoImplicit false
noncomputable section
open Set Filter Topology Metric Complex
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley cayleyInv)

namespace InteractingSLE.Sec5.Aux61GInst

/-- Removing a compact prefix adds only that prefix to a component boundary. -/
theorem frontier_component_diff_subset {U K : Set ℂ} (hU : IsOpen U) (hK : IsClosed K) (b : ℂ) :
    frontier (connectedComponentIn (U \ K) b) ⊆ frontier U ∪ K := by
  intro z hz
  by_cases hzK : z ∈ K
  · exact Or.inr hzK
  · refine Or.inl ?_
    rw [hU.frontier_eq]
    refine ⟨closure_mono ((connectedComponentIn_subset _ _).trans sdiff_subset)
      (frontier_subset_closure hz), ?_⟩
    intro hzU
    exact frontier_connectedComponentIn_subset_compl (hU.sdiff hK) b hz ⟨hzU, hzK⟩

/-- Carrying components through a continuous map with a continuous inverse. -/
theorem image_component_of_leftInverse {U : Set ℂ} {f g : ℂ → ℂ}
    (hf : ContinuousOn f U) (hg : ContinuousOn g (f '' U))
    (hgf : LeftInvOn g f U) {b : ℂ} (hb : b ∈ U) :
    f '' connectedComponentIn U b = connectedComponentIn (f '' U) (f b) := by
  refine (hf.image_connectedComponentIn_subset hb).antisymm ?_
  intro z hz
  have hzU : z ∈ f '' U := connectedComponentIn_subset _ _ hz
  obtain ⟨w, hw, hwz⟩ := hzU
  have hh := hg.image_connectedComponentIn_subset (mem_image_of_mem f hb)
  have he : g '' (f '' U) = U := hgf.image_image
  rw [he, hgf hb] at hh
  have hwC : w ∈ connectedComponentIn U b := by
    have hmem := hh (mem_image_of_mem g hz)
    rw [← hwz, hgf hw] at hmem
    exact hmem
  exact ⟨w, hwC, hwz⟩

/-- The bounded model of a filled compact path has boundary only on the
circle and the path. This is the boundary step in the existing extension proof. -/
theorem frontier_cayley_fill_subset {K : Set ℂ} (hK : IsCompact K) :
    frontier (cayley '' (H \ fillH K)) ⊆ sphere (0 : ℂ) 1 ∪ cayley '' K := by
  have hDo := Sec7.Lemma71F.isOpen_cayley_image (isOpen_H_diff_fillH hK.isBounded) sdiff_subset
  rw [hDo.frontier_eq]
  rintro w ⟨hwc, hwD⟩
  have hwB : w ∈ closedBall (0 : ℂ) 1 := closure_minimal
    (Sec7.Lemma71F.cayley_image_subset_ball sdiff_subset |>.trans ball_subset_closedBall)
    isClosed_closedBall hwc
  by_cases hs : ‖w‖ = 1
  · exact Or.inl (mem_sphere_zero_iff_norm.2 hs)
  have hwb : w ∈ ball (0 : ℂ) 1 :=
    mem_ball_zero_iff.2 (lt_of_le_of_ne (mem_closedBall_zero_iff.1 hwB) hs)
  have hw1 := Sec7.Lemma71F.ne_one_of_mem_ball hwb
  have hzw := QuantumZipper.CA.cayley_cayleyInv hw1
  have hzc : cayleyInv w ∈ closure (H \ fillH K) := by
    have hi : LeftInvOn cayleyInv cayley (H \ fillH K) := fun z hz =>
      cayleyInv_cayley_of_mem_Hbar (QuantumZipper.H_subset_Hbar hz.1)
    have hm := mem_closure_image
      (QuantumZipper.CA.continuousOn_cayleyInv.continuousAt (isOpen_ne.mem_nhds hw1)) hwc
    rwa [hi.image_image] at hm
  have hzfr : cayleyInv w ∈ frontier (H \ fillH K) := by
    rw [(isOpen_H_diff_fillH hK.isBounded).frontier_eq]
    exact ⟨hzc, fun hz => hwD ⟨_, hz, hzw⟩⟩
  rcases frontier_H_diff_fillH_subset hK.isBounded hzfr with hr | hk
  · exfalso
    have hzH := QuantumZipper.CA.cayleyInv_mem_H hwb
    exact (ne_of_gt hzH) hr
  · exact Or.inr ⟨_, hK.isClosed.closure_eq ▸ hk, hzw⟩

end InteractingSLE.Sec5.Aux61GInst
