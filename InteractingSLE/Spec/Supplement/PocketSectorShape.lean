/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.PocketShapeFinAssembly
import InteractingSLE.Spec.Supplement.GW3SidedProof

/-!
# Pocket shapes through the existing sector map

PROVE-POCKETSHAPE continuation. Reuse `GW3SidedProof.sectorMap` to move complete
simple flows into the open half-plane. Frontier, boundedness, and shape identities
are transported without any additional geometric hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Bornology Metric Function
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.PocketSector

open GW4Reg GW3SidedProof

/-- The existing sector-map construction applies to complete simple flows. -/
theorem isSimpleProper_sector {α : ℝ≥0 → ℂ} (hα : GB11.IsCompleteSimpleFlow α) :
    Sec7.Lemma71I.IsSimpleProper (sectorMap ∘ α) :=
  isSimpleProper_sectorMap_comp ⟨hα.1, hα.2.1, hα.2.2.2.1, hα.2.2.2.2⟩ hα.2.2.1

/-- A strictly interior proper flow is also a complete simple flow in the original sense. -/
theorem isCompleteSimpleFlow_of_isSimpleProper {α : ℝ≥0 → ℂ}
    (hα : Sec7.Lemma71I.IsSimpleProper α) : GB11.IsCompleteSimpleFlow α := by
  refine ⟨hα.1, hα.2.1, hα.2.2.1, ?_, hα.2.2.2.2⟩
  intro t
  rcases eq_zero_or_pos t with ht | ht
  · rw [ht, hα.2.2.1]
    exact (show (0 : ℝ) ≤ 0 from le_rfl)
  · exact (show 0 < (α t).im from hα.2.2.2.1 t ht).le

/-- Boundedness is preserved and reflected by the sector map. -/
theorem isBounded_sector_image_iff {C : Set ℂ} : IsBounded (sectorMap '' C) ↔ IsBounded C := by
  constructor
  · intro hb
    obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 hb
    apply isBounded_iff_forall_norm_le.2
    refine ⟨(max M 0) ^ 2, fun z hz => ?_⟩
    have hbound := (hM _ ⟨z, hz, rfl⟩).trans (le_max_left M 0)
    rw [← norm_sectorMap_sq z]
    exact pow_le_pow_left₀ (norm_nonneg _) hbound 2
  · intro hb
    obtain ⟨M, hM⟩ := isBounded_iff_forall_norm_le.1 hb
    apply isBounded_iff_forall_norm_le.2
    refine ⟨max M 0 + 1, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    have hsq := norm_sectorMap_sq z
    have hbound := (hM z hz).trans (le_max_left M 0)
    have hnonneg := norm_nonneg (sectorMap z)
    have hM0 := le_max_right M 0
    nlinarith only [hsq, hbound, hnonneg, hM0]

/-- A point of the closure of a sector image maps back into the original closure. -/
theorem sectorInv_mem_closure {C : Set ℂ} {w : ℂ} (hw : w ∈ closure (sectorMap '' C)) :
    sectorInv w ∈ closure C := by
  have h := continuous_sectorInv.continuousAt.continuousWithinAt.mem_closure_image hw
  rw [image_image] at h
  simpa only [comp_def, sectorInv_sectorMap, image_id'] using h

/-- The sector image of a closure point of a half-plane set is a closure point. -/
theorem sectorMap_mem_closure {C : Set ℂ} (hCH : C ⊆ H) {z : ℂ} (hz : z ∈ closure C) :
    sectorMap z ∈ closure (sectorMap '' C) := by
  have hCb : closure C ⊆ Hbar := by
    exact closure_minimal (fun z hz => (show 0 < z.im from hCH hz).le)
      QuantumZipper.isClosed_Hbar
  exact ((continuousOn_sectorMap z (hCb hz)).mono
    (fun x hx => (show 0 < x.im from hCH hx).le)).mem_closure_image hz

variable {αR αL : ℝ≥0 → ℂ}

/-- Between-components are carried to between-components by the existing sector theorem. -/
theorem image_mem_between (hR : GB11.IsCompleteSimpleFlow αR) (hL : GB11.IsCompleteSimpleFlow αL)
    {C : Set ℂ} (hC : C ∈ betweenComponents (range αR) (range αL)) :
    sectorMap '' C ∈ betweenComponents (range (sectorMap ∘ αR)) (range (sectorMap ∘ αL)) :=
  image_mem_betweenComponents ⟨hR.1, hR.2.1, hR.2.2.2.1, hR.2.2.2.2⟩ hR.2.2.1
    ⟨hL.1, hL.2.1, hL.2.2.2.1, hL.2.2.2.2⟩ hL.2.2.1 hC

/-- The full frontier identity for a between-component under the sector map. -/
theorem frontier_sector_image (hR : GB11.IsCompleteSimpleFlow αR) (hL : GB11.IsCompleteSimpleFlow αL)
    {C : Set ℂ} (hC : C ∈ betweenComponents (range αR) (range αL)) :
    frontier (sectorMap '' C) = sectorMap '' frontier C := by
  have hCH : C ⊆ H := fun z hz => (Sec7.Prop74B.subset_of_mem_betweenComponents hC hz).1
  have hCo := isOpen_of_mem_betweenComponents
    (isClosed_range_of_isCompleteSimpleFlow hR) (isClosed_range_of_isCompleteSimpleFlow hL) hC
  have hIo := isOpen_of_mem_betweenComponents
    (isClosed_range_of_isSimpleProper (isSimpleProper_sector hR))
    (isClosed_range_of_isSimpleProper (isSimpleProper_sector hL)) (image_mem_between hR hL hC)
  apply Subset.antisymm
  · intro w hw
    have hsub : sectorMap '' C ⊆ closedSector := by
      rintro _ ⟨z, hz, rfl⟩
      exact sectorMap_mem_closedSector (show 0 < z.im from hCH hz).le
    have hwS : w ∈ closedSector := closure_minimal hsub isClosed_closedSector hw.1
    refine ⟨sectorInv w, ?_, sectorMap_sectorInv hwS⟩
    rw [hCo.frontier_eq]
    refine ⟨sectorInv_mem_closure hw.1, fun hz => ?_⟩
    apply hw.2
    simpa only [hIo.interior_eq] using
      (show w ∈ sectorMap '' C from ⟨sectorInv w, hz, sectorMap_sectorInv hwS⟩)
  · rintro _ ⟨z, hz, rfl⟩
    rw [hIo.frontier_eq]
    refine ⟨sectorMap_mem_closure hCH hz.1, ?_⟩
    rintro ⟨z', hz', he⟩
    apply hz.2
    simpa only [hCo.interior_eq] using (sectorMap_injective he ▸ hz')

/-- A shape is preserved by moving the walls and the component into the sector. -/
theorem shape_sector_image (hR : GB11.IsCompleteSimpleFlow αR) (hL : GB11.IsCompleteSimpleFlow αL)
    {C : Set ℂ} (hC : C ∈ betweenComponents (range αR) (range αL))
    {s t : ℝ≥0} {u v : ℝ≥0∞} (hs : IsPocketShape αR αL C s t u v) :
    IsPocketShape (sectorMap ∘ αR) (sectorMap ∘ αL) (sectorMap '' C) s t u v := by
  have hCH : C ⊆ H := fun z hz => (Sec7.Prop74B.subset_of_mem_betweenComponents hC hz).1
  refine ⟨congrArg sectorMap hs.contact, sectorMap_mem_closure hCH hs.mem_closure_exit,
    hs.lt, hs.top_iff, fun hu hb => hs.unbounded hu (isBounded_sector_image_iff.1 hb), ?_, ?_⟩
  · intro hu
    obtain ⟨he, hcl, hb⟩ := hs.entry hu
    exact ⟨congrArg sectorMap he, sectorMap_mem_closure hCH hcl, isBounded_sector_image_iff.2 hb⟩
  · rw [frontier_sector_image hR hL hC]
    rintro _ ⟨z, hz, rfl⟩
    rcases hs.frontier_subset hz with ⟨r, hr, rfl⟩ | ⟨q, hq, rfl⟩
    · exact Or.inl ⟨r, hr, rfl⟩
    · exact Or.inr ⟨q, hq, rfl⟩

/-- A shape in the sector gives a shape of the original component, with the same parameters. -/
theorem shape_of_sector_image (hR : GB11.IsCompleteSimpleFlow αR) (hL : GB11.IsCompleteSimpleFlow αL)
    {C : Set ℂ} (hC : C ∈ betweenComponents (range αR) (range αL))
    {s t : ℝ≥0} {u v : ℝ≥0∞}
    (hs : IsPocketShape (sectorMap ∘ αR) (sectorMap ∘ αL) (sectorMap '' C) s t u v) :
    IsPocketShape αR αL C s t u v := by
  have hexit : αR s ∈ closure C := by
    simpa only [comp_apply, sectorInv_sectorMap] using sectorInv_mem_closure hs.mem_closure_exit
  refine ⟨sectorMap_injective hs.contact, hexit, hs.lt, hs.top_iff,
    fun hu hb => hs.unbounded hu (isBounded_sector_image_iff.2 hb), ?_, ?_⟩
  · intro hu
    obtain ⟨he, hcl, hb⟩ := hs.entry hu
    refine ⟨sectorMap_injective he, ?_, isBounded_sector_image_iff.1 hb⟩
    simpa only [comp_apply, sectorInv_sectorMap] using sectorInv_mem_closure hcl
  · intro z hz
    have hz' : sectorMap z ∈ frontier (sectorMap '' C) := by
      rw [frontier_sector_image hR hL hC]
      exact ⟨z, hz, rfl⟩
    rcases hs.frontier_subset hz' with ⟨r, hr, he⟩ | ⟨q, hq, he⟩
    · exact Or.inl ⟨r, hr, sectorMap_injective he⟩
    · exact Or.inr ⟨q, hq, sectorMap_injective he⟩

end InteractingSLE.Theorem14.PocketSector
