/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCG8DetRelMain
import InteractingSLE.Foundations.Loewner.HullKernel

/-!
# G8: a union identity from separation in the cut chart

Packet PROVE-G8-DET. Disjoint closures of two hulls after mapping out their
common initial hull imply that their physical union is already filled. The
Janiszewski union theorem and conformal inverse transport supply the topology.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Function
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.RLC.G8Det.Late

/-- Filling ignores points outside the upper half-plane. -/
theorem fillH_inter_H (S : Set ℂ) : fillH (S ∩ H) = fillH S := by
  have hsplit : S = (S ∩ H) ∪ (S \ H) := by ext z; simp only [mem_union, mem_inter_iff, Set.mem_sdiff]; tauto
  conv_rhs => rw [hsplit]
  exact (Restart.fillH_union_of_forall_notMem_H (fun z hz => hz.2)).symm

/-- Minimality of filling inside a half-plane hull, including real trace points. -/
theorem fillH_subset_of_inter_H_subset {S C : Set ℂ} (hC : IsHPHull C) (hSC : S ∩ H ⊆ C) :
    fillH S ⊆ C := by
  rw [← fillH_inter_H S, ← hC.fillH_eq]
  exact fillH_mono hSC

/-- Mapping out a common subhull transports the complement of a union to
the complement of the union of its two image hulls. -/
theorem image_compl_union {K P Q : Set ℂ} {g : ℂ → ℂ}
    (hg : IsMapOut K g) (hKP : K ⊆ P) (hPH : P ⊆ H) (hQH : Q ⊆ H) :
    g '' (H \ (P ∪ Q)) = H \ (g '' (P \ K) ∪ g '' (Q \ K)) := by
  rw [← hg.H_diff_image (hKP.trans subset_union_left) (union_subset hPH hQH),
    union_sdiff_distrib, image_union]

/-- Pull Janiszewski's hull union back through the map of a common subhull. -/
theorem isHPHull_union_of_disjoint_images {K P Q : Set ℂ} {g : ℂ → ℂ}
    (hK : IsHPHull K) (hP : IsHPHull P) (hQ : IsHPHull Q)
    (hKP : K ⊆ P) (hKQ : K ⊆ Q) (hg : IsMapOut K g)
    (hd : Disjoint (closure (g '' (P \ K))) (closure (g '' (Q \ K)))) :
    IsHPHull (P ∪ Q) := by
  have hIP := hg.isHPHull_image hK hP hKP
  have hIQ := hg.isHPHull_image hK hQ hKQ
  have hI := hIP.union_of_disjoint_closure hIQ hd
  let D := H \ (P ∪ Q)
  let E := H \ (g '' (P \ K) ∪ g '' (Q \ K))
  let F := invFunOn g (H \ K)
  have hDsub : D ⊆ H \ K := fun z hz => ⟨hz.1, fun h => hz.2 (Or.inl (hKP h))⟩
  have himg : g '' D = E := image_compl_union hg hKP hP.1 hQ.1
  have hFinv : ∀ z ∈ H \ K, F (g z) = z := hg.1.2.invOn_invFunOn.1
  have hFE : F '' E = D := by
    rw [← himg, image_image]
    exact (image_congr fun z hz => hFinv z (hDsub hz)).trans (image_id D)
  have hF := isConformalBijection_invFunOn hK.isOpen hg.1
  have hsc := isSimplyConnected_of_isConformalBijection hI.isOpen
    (show SupercriticalConformalCovariance.IsConformalBijection F E (F '' E) from
      ⟨hF.1.mono sdiff_subset, (hF.2.injOn.mono sdiff_subset).bijOn_image⟩) hI.2.2.2
  rw [hFE] at hsc
  refine ⟨union_subset hP.1 hQ.1, hP.2.1.union hQ.2.1, ?_, hsc⟩
  have he : H \ (P ∪ Q) = (H \ P) ∩ (H \ Q) := by
    ext z; simp only [Set.mem_sdiff, mem_union, mem_inter_iff, not_or]; tauto
  rw [he]
  exact hP.isOpen.inter hQ.isOpen

/-- If the union of two filled sets is a hull, filling their union adds
no further pocket. -/
theorem fillH_union_eq_of_isHPHull {S T : Set ℂ}
    (hU : IsHPHull (fillH S ∪ fillH T)) : fillH (S ∪ T) = fillH S ∪ fillH T := by
  apply Subset.antisymm
  · refine fillH_subset_of_inter_H_subset hU ?_
    rintro z ⟨hzS | hzT, hzH⟩
    · exact Or.inl (mem_fillH_of_mem_closure hzH (subset_closure hzS))
    · exact Or.inr (mem_fillH_of_mem_closure hzH (subset_closure hzT))
  · exact union_subset (fillH_mono subset_union_left) (fillH_mono subset_union_right)

/-- The filled union identity is a consequence of closed image-hull
separation; it need not be included as a separate geometric hypothesis. -/
theorem fillH_union_eq_of_disjoint_images {S T K : Set ℂ} {g : ℂ → ℂ}
    (hK : IsHPHull K) (hS : IsHPHull (fillH S)) (hT : IsHPHull (fillH T))
    (hKS : K ⊆ fillH S) (hKT : K ⊆ fillH T) (hg : IsMapOut K g)
    (hd : Disjoint (closure (g '' (fillH S \ K))) (closure (g '' (fillH T \ K)))) :
    fillH (S ∪ T) = fillH S ∪ fillH T :=
  fillH_union_eq_of_isHPHull (isHPHull_union_of_disjoint_images hK hS hT hKS hKT hg hd)

end InteractingSLE.RLC.G8Det.Late
