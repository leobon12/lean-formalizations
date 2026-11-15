/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.PocketShapeFinJordan

/-!
# Shape existence for bounded two-arc Jordan components

PROVE-POCKETSHAPE continuation. This proves the bounded alternative of the original
geometry hypothesis, allowing real boundary connectors on both complete simple flows.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Bornology
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.PocketShapeFin

open GW4Reg

/-- Two wall intervals with the stated contacts and full frontier give a bounded shape. -/
theorem isPocketShape_of_frontier_intervals {αR αL : ℝ≥0 → ℂ} {C : Set ℂ}
    (hCb : IsBounded C) {s t u v : ℝ≥0} (hsu : s < u)
    (h0 : αR s = αL t) (h1 : αR u = αL v)
    (hfr : frontier C = αR '' Icc s u ∪ αL '' Icc t v) :
    IsPocketShape αR αL C s t (u : ℝ≥0∞) (v : ℝ≥0∞) := by
  have hsfr : αR s ∈ frontier C := hfr ▸ Or.inl ⟨s, ⟨le_rfl, hsu.le⟩, rfl⟩
  have hufr : αR u ∈ frontier C := hfr ▸ Or.inl ⟨u, ⟨hsu.le, le_rfl⟩, rfl⟩
  refine ⟨h0, frontier_subset_closure hsfr, ENNReal.coe_lt_coe.2 hsu,
    by simp only [ENNReal.coe_ne_top, iff_self], fun hu => (ENNReal.coe_ne_top hu).elim, ?_, ?_⟩
  · intro hu
    simpa only [ENNReal.toNNReal_coe] using
      (show αR u = αL v ∧ αR u ∈ closure C ∧ IsBounded C from
        ⟨h1, frontier_subset_closure hufr, hCb⟩)
  · rw [hfr]
    exact union_subset_union
      (image_mono fun r hr => ⟨hr.1, ENNReal.coe_le_coe.2 hr.2⟩)
      (image_mono fun r hr => ⟨hr.1, ENNReal.coe_le_coe.2 hr.2⟩)

/-- Recover the two exact wall intervals of a connected Jordan partition with ordered contacts. -/
theorem frontier_intervals_of_connected_partition {αR αL : ℝ≥0 → ℂ}
    (hR : GB11.IsCompleteSimpleFlow αR) (hL : GB11.IsCompleteSimpleFlow αL)
    {A B : Set ℂ} (hAR : A ⊆ range αR) (hBL : B ⊆ range αL)
    {a e : ℂ} (hAB : A ∩ B = {a, e})
    (hAc : IsPreconnected A) (hAp : IsPreconnected (A \ {a, e}))
    (hBc : IsPreconnected B) (hBp : IsPreconnected (B \ {a, e}))
    {s t u v : ℝ≥0} (hsu : s < u) (htv : t < v)
    (hsa : αR s = a) (hua : αR u = e) (hta : αL t = a) (hva : αL v = e) :
    A = αR '' Icc s u ∧ B = αL '' Icc t v := by
  have haAB : a ∈ A ∩ B := by rw [hAB]; exact Or.inl rfl
  have heAB : e ∈ A ∩ B := by rw [hAB]; exact Or.inr rfl
  exact ⟨eq_image_Icc_of_connected_endpoints
      (GB11Chart.isClosedEmbedding_of_isCompleteSimpleFlow hR).isEmbedding hAR hAc hsu
      (hsa.symm ▸ haAB.1) (hua.symm ▸ heAB.1) (by rwa [hsa, hua]),
    eq_image_Icc_of_connected_endpoints
      (GB11Chart.isClosedEmbedding_of_isCompleteSimpleFlow hL).isEmbedding hBL hBc htv
      (hta.symm ▸ haAB.2) (hva.symm ▸ heAB.2) (by rwa [hta, hva])⟩

/-- Every bounded two-arc Jordan component of ordered complete simple flows has a shape.
The endpoint parameters are finite. This uses the original closed-half-plane hypothesis. -/
theorem exists_isPocketShape_of_twoArcJordan
    {αR αL : ℝ≥0 → ℂ} (hR : GB11.IsCompleteSimpleFlow αR) (hL : GB11.IsCompleteSimpleFlow αL)
    (hord : ∀ s s' t t' : ℝ≥0, αR s = αL t → αR s' = αL t' → (s < s' ↔ t < t'))
    {C : Set ℂ} (hG : GW3.IsTwoArcJordanComponent (range αR) (range αL) C) :
    ∃ s t u v : ℝ≥0, IsPocketShape αR αL C s t (u : ℝ≥0∞) (v : ℝ≥0∞) := by
  obtain ⟨hCo, hCc, -, hCb, hJ, A, B, a, e, hA, hB, hfr, hAB, hae, hAR, hBL, hAn, hBn⟩ := hG
  obtain ⟨⟨hAc, hAp⟩, ⟨hBc, hBp⟩⟩ :=
    connected_parts_of_jordan hCo hCc hCb hJ hA hB hfr hAB hae hAn hBn
  have haAB : a ∈ A ∩ B := by rw [hAB]; exact Or.inl rfl
  have heAB : e ∈ A ∩ B := by rw [hAB]; exact Or.inr rfl
  obtain ⟨s, hsa⟩ := hAR haAB.1
  obtain ⟨u, hue⟩ := hAR heAB.1
  obtain ⟨t, hta⟩ := hBL haAB.2
  obtain ⟨v, hve⟩ := hBL heAB.2
  have h0 : αR s = αL t := hsa.trans hta.symm
  have h1 : αR u = αL v := hue.trans hve.symm
  have hne : s ≠ u := fun he => hae (hsa.symm.trans ((congrArg αR he).trans hue))
  rcases lt_or_gt_of_ne hne with hsu | hus
  · have htv : t < v := (hord s u t v h0 h1).1 hsu
    obtain ⟨heA, heB⟩ := frontier_intervals_of_connected_partition hR hL hAR hBL hAB hAc hAp hBc hBp
      hsu htv hsa hue hta hve
    refine ⟨s, t, u, v, isPocketShape_of_frontier_intervals hCb hsu h0 h1 ?_⟩
    rw [hfr, heA, heB]
  · have hvt : v < t := (hord u s v t h1 h0).1 hus
    have hAB' : A ∩ B = {e, a} := hAB.trans (pair_comm a e)
    obtain ⟨heA, heB⟩ := frontier_intervals_of_connected_partition hR hL hAR hBL hAB' hAc
      (by simpa only [pair_comm e a] using hAp) hBc (by simpa only [pair_comm e a] using hBp)
      hus hvt hue hsa hve hta
    refine ⟨u, v, s, t, isPocketShape_of_frontier_intervals hCb hus h1 h0 ?_⟩
    rw [hfr, heA, heB]

end InteractingSLE.Theorem14.PocketShapeFin
