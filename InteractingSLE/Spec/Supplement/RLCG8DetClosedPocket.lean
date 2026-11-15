/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCG8DetSepMain
import InteractingSLE.Spec.Supplement.GB6Disjoint

/-!
# G8: no common filled pocket beyond the old own hull

Packet PROVE-G8-DET. A bounded old joint pocket cannot enter a new filling
without either a new trace contact or a retained boundary point in that
filling. The proof uses connected components and relative closedness.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open scoped NNReal ENNReal
open QuantumZipper (H)

namespace InteractingSLE.RLC.G8Det.Closed

/-- Exclusion of both new trace contacts and retained boundary points
excludes every old joint pocket from the new own filling. -/
theorem fillH_inter_subset {F B T : Set ℂ} (hF : IsCompact F) (hB : IsCompact B)
    (hT : IsCompact T) (hQ : IsHPHull (fillH T))
    (hnew : Disjoint (T \ F) (fillH (F ∪ B)))
    (hret : Disjoint (fillH T \ fillH F) B) :
    fillH (F ∪ B) ∩ fillH T ⊆ fillH F := by
  rintro z ⟨hzJ, hzQ⟩
  by_contra hzP
  have hzH : z ∈ H := fillH_subset_H _ hzQ
  have hzF : z ∉ F := fun h => hzP (mem_fillH_of_mem_closure hzH (subset_closure h))
  have hzB : z ∉ B := fun h => Set.disjoint_left.1 hret ⟨hzQ, hzP⟩ h
  have hzT : z ∉ T := fun h => Set.disjoint_left.1 hnew ⟨h, hzF⟩ hzJ
  have hFB := hF.union hB
  let O := connectedComponentIn (H \ (F ∪ B)) z
  have hzO : z ∈ O := mem_connectedComponentIn ⟨hzH, fun h => h.elim hzF hzB⟩
  have hOb : IsBounded O := Supp8.GB6.isBounded_connectedComponentIn_of_mem_fillH hFB.isClosed
    hzJ (fun h => h.elim hzF hzB)
  have hOJ : O ⊆ fillH (F ∪ B) := Supp8.GB6.connectedComponentIn_subset_fillH hFB.isClosed hOb
  have hOT : O ⊆ H \ T := by
    intro w hw
    have hwd := connectedComponentIn_subset (H \ (F ∪ B)) z hw
    refine ⟨hwd.1, fun h => ?_⟩
    have hwF : w ∉ F := fun hF => hwd.2 (Or.inl hF)
    exact Set.disjoint_left.1 hnew ⟨h, hwF⟩ (hOJ hw)
  have hOQ : O ⊆ fillH T :=
    (isPreconnected_connectedComponentIn.subset_connectedComponentIn hzO hOT).trans
      (Supp8.GB6.connectedComponentIn_subset_fillH hT.isClosed
        (Supp8.GB6.isBounded_connectedComponentIn_of_mem_fillH hT.isClosed hzQ hzT))
  have hOo : IsOpen O := (QuantumZipper.isOpen_H.sdiff hFB.isClosed).connectedComponentIn
  have hcl : closure O ∩ (H \ fillH F) ⊆ O := by
    rintro w ⟨hwcl, hwD⟩
    have hwQ : w ∈ fillH T := hQ.mem_of_mem_closure hwD.1 (closure_mono hOQ hwcl)
    have hwF : w ∉ F := fun h => hwD.2 (mem_fillH_of_mem_closure hwD.1 (subset_closure h))
    have hwB : w ∉ B := fun h => Set.disjoint_left.1 hret ⟨hwQ, hwD.2⟩ h
    exact Supp8.GB6.mem_connectedComponentIn_of_mem_closure hFB.isClosed hwcl hwD.1
      (fun h => h.elim hwF hwB)
  have hDsub : H \ fillH F ⊆ O :=
    (HalfPlaneSep.isPreconnected_H_diff_fillH hF.isClosed hF.isBounded).subset_of_closure_inter_subset
      hOo ⟨z, ⟨hzH, hzP⟩, hzO⟩ hcl
  exact HalfPlaneSep.not_isBounded_H_diff_fillH hF.isClosed hF.isBounded (hOb.subset hDsub)

end InteractingSLE.RLC.G8Det.Closed
