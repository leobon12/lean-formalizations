/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.PocketRimAssembly
import InteractingSLE.WangWu.PlanarDescent

/-!
# The marked Cayley pocket of a bounded shape

PROVE-POCKETSHAPE continuation. The finite wall endpoints of a bounded shape
give the marked-pocket data required by the existing chart-orientation theorem.
No global side condition on the other wall is used.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Bornology Metric Function
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley)

namespace InteractingSLE.Theorem14.PocketCompass

open GW4Reg WangWu WangWu.Descent Sec7.Lemma71I Sec7.Lemma71K

/-- A bounded half-plane domain has exactly the Cayley image of its finite frontier. -/
theorem frontier_cayley_eq_of_isBounded {C : Set ℂ} (hCo : IsOpen C) (hCH : C ⊆ H)
    (hb : IsBounded C) : frontier (cayley '' C) = cayley '' frontier C := by
  have hHb : closure C ⊆ Hbar := fun z hz => Sec7.Lemma71F.im_nonneg_of_mem_closure hCH hz
  have hcompact : IsCompact (cayley '' closure C) := hb.isCompact_closure.image_of_continuousOn
    (fun z hz => (continuousAt_cayley_of_mem_Hbar (hHb hz)).continuousWithinAt)
  have hcl : closure (cayley '' C) ⊆ cayley '' closure C :=
    closure_minimal (image_mono subset_closure) hcompact.isClosed
  apply Subset.antisymm
  · intro w hw
    obtain ⟨z, hz, rfl⟩ := hcl (frontier_subset_closure hw)
    refine ⟨z, ?_, rfl⟩
    rw [hCo.frontier_eq]
    exact ⟨hz, fun hzC => disjoint_left.1 (disjoint_frontier_iff_isOpen.2
      (Sec7.Lemma71F.isOpen_cayley_image hCo hCH)) hw ⟨z, hzC, rfl⟩⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact Sec7.Lemma71F.cayley_mem_frontier hCo hCH hz

/-- The right-wall times in the closure of a bounded shape are precisely between its endpoints. -/
theorem right_parameter_mem_Icc_of_bounded_shape {R L : ℝ≥0 → ℂ}
    (hR : GB11.IsCompleteSimpleFlow R) (hL : GB11.IsCompleteSimpleFlow L)
    (hord : ∀ s s' t t' : ℝ≥0, R s = L t → R s' = L t' → (s < s' ↔ t < t'))
    {C : Set ℂ} (hC : C ∈ betweenComponents (range R) (range L))
    {s t : ℝ≥0} {u v : ℝ≥0∞} (hs : IsPocketShape R L C s t u v) (hu : u ≠ ⊤)
    {r : ℝ≥0} (hr : R r ∈ closure C) : r ∈ Icc s u.toNNReal := by
  have hCo := isOpen_of_mem_betweenComponents (isClosed_range_of_isCompleteSimpleFlow hR)
    (isClosed_range_of_isCompleteSimpleFlow hL) hC
  have hfr : R r ∈ frontier C := by
    rw [hCo.frontier_eq]
    exact ⟨hr, fun h => (Sec7.Prop74B.subset_of_mem_betweenComponents hC h).2 (Or.inl ⟨r, rfl⟩)⟩
  refine ⟨?_, PocketShapeFin.right_parameter_le_entry hR hL hord hC hs hu hr⟩
  rcases hs.frontier_subset hfr with ⟨q, hq, he⟩ | ⟨q, -, he⟩
  · exact hR.2.1 he ▸ hq.1
  · exact (PocketShapeDet.contact_bounds_of_mem_closure hR hL hord hC hs he.symm hr).1

/-- Finite wall intervals agree in the original and disc clocks. -/
theorem wallPt_image_discTime_Icc (R : ℝ≥0 → ℂ) {s u : ℝ≥0} (_hsu : s ≤ u) :
    wallPt R '' Icc (discTime (s : ℝ)) (discTime (u : ℝ)) = cayley '' (R '' Icc s u) := by
  apply Subset.antisymm
  · rintro _ ⟨q, hq, rfl⟩
    have hq0 : 0 ≤ q := (discTime_nonneg s.2).trans hq.1
    have hq1 : q < 1 := hq.2.trans_lt (discTime_lt_one u.2)
    refine ⟨R (arcTime q).toNNReal, ⟨(arcTime q).toNNReal, ⟨?_, ?_⟩, rfl⟩, ?_⟩
    · change (s : ℝ) ≤ ((arcTime q).toNNReal : ℝ)
      rw [Real.coe_toNNReal _ (arcTime_nonneg ⟨hq0, hq1⟩)]
      exact arcTime_ge s.2 hq.1 hq1
    · exact Real.toNNReal_le_iff_le_coe.2 (arcTime_le u.2 hq0 hq.2)
    · exact (toDisc_of_lt (γ := realPath R) hq1).symm
  · rintro _ ⟨_, ⟨r, hr, rfl⟩, rfl⟩
    refine ⟨discTime (r : ℝ), ⟨?_, ?_⟩, Sec7.PocketCoord.toDisc_realPath_discTime R r⟩
    · rcases eq_or_lt_of_le hr.1 with h | h
      · exact (congrArg (fun a : ℝ≥0 => discTime (a : ℝ)) h).le
      · exact (WangWu.discTime_lt_discTime s.2 (by exact_mod_cast h)).le
    · rcases eq_or_lt_of_le hr.2 with h | h
      · exact (congrArg (fun a : ℝ≥0 => discTime (a : ℝ)) h).le
      · exact (WangWu.discTime_lt_discTime r.2 (by exact_mod_cast h)).le

/-- A bounded shape supplies the complete marked-pocket data, at its actual wall endpoints. -/
theorem isMarkedPocket_of_bounded_shape {R L : ℝ≥0 → ℂ}
    (hR : GB11.IsCompleteSimpleFlow R) (hL : GB11.IsCompleteSimpleFlow L)
    (hord : ∀ s s' t t' : ℝ≥0, R s = L t → R s' = L t' → (s < s' ↔ t < t'))
    {C : Set ℂ} (hC : C ∈ betweenComponents (range R) (range L))
    {s t : ℝ≥0} {u v : ℝ≥0∞} (hs : IsPocketShape R L C s t u v) (hu : u ≠ ⊤) :
    IsMarkedPocket R C (discTime (s : ℝ)) (discTime (u.toNNReal : ℝ)) := by
  obtain ⟨hv, hsu, -⟩ := PocketShapeDet.finite_parameters hord hs hu
  have hCo := isOpen_of_mem_betweenComponents (isClosed_range_of_isCompleteSimpleFlow hR)
    (isClosed_range_of_isCompleteSimpleFlow hL) hC
  have hCH : C ⊆ H := fun z hz => (Sec7.Prop74B.subset_of_mem_betweenComponents hC hz).1
  have hb : IsBounded C := (hs.entry hu).2.2
  have hfr := PocketShapeDet.frontier_eq_of_bounded_shape hR hL hord hC hs hu
  have hfc := frontier_cayley_eq_of_isBounded hCo hCH hb
  have hwall : ∀ {q : ℝ}, q ∈ Icc (0 : ℝ) 1 → wallPt R q ∈ closure (cayley '' C) →
      q ∈ Icc (discTime (s : ℝ)) (discTime (u.toNNReal : ℝ)) := by
    intro q hq hqC
    have hq1 : q < 1 := lt_of_le_of_ne hq.2 fun h =>
      PocketRim.one_not_mem_closure_cayley_of_isBounded hCH hb (by simpa only [h, wallPt, toDisc_one] using hqC)
    have hrC : R (arcTime q).toNNReal ∈ closure C :=
      PocketRim.mem_closure_of_cayley_mem_closure hCH (hR.2.2.2.1 _) (by
        simpa only [wallPt, toDisc_of_lt hq1, realPath] using hqC)
    have hr := right_parameter_mem_Icc_of_bounded_shape hR hL hord hC hs hu hrC
    have hqimage : wallPt R q ∈ wallPt R '' Icc (discTime (s : ℝ)) (discTime (u.toNNReal : ℝ)) := by
      rw [wallPt_image_discTime_Icc R hsu.le]
      exact ⟨_, ⟨_, hr, rfl⟩, (toDisc_of_lt (γ := realPath R) hq1).symm⟩
    obtain ⟨q', hq', he⟩ := hqimage
    have hprops := GW3.wallPt_props (GW4Reg.isProperCurve_of_isCompleteSimpleFlow hR) hR.2.2.1
    have heq := hprops.2.1 ⟨(discTime_nonneg s.2).trans hq'.1,
      hq'.2.trans (discTime_lt_one u.toNNReal.2).le⟩ hq he
    exact heq ▸ hq'
  have hends : ∀ r ∈ Icc s u.toNNReal, cayley (R r) ∈ frontier (cayley '' C) := by
    intro r hr
    rw [hfc, hfr]
    exact ⟨R r, Or.inl ⟨r, hr, rfl⟩, rfl⟩
  have hJ := PocketShapeDet.isJordanCurve_of_bounded_shape hR hL hord hC hs hu
  have hJH : R '' Icc s u.toNNReal ∪ L '' Icc t v.toNNReal ⊆ Hbar := by
    rintro _ (⟨r, -, rfl⟩ | ⟨r, -, rfl⟩)
    · exact hR.2.2.2.1 r
    · exact hL.2.2.2.1 r
  refine ⟨discTime_nonneg s.2, WangWu.discTime_lt_discTime s.2 (by exact_mod_cast hsu),
    (discTime_lt_one u.toNNReal.2).le, ?_, ?_, ?_, ?_, ?_⟩
  · apply Subset.antisymm
    · exact fun q hq => hwall hq.1 hq.2
    · intro q hq
      have hq01 : q ∈ Icc (0 : ℝ) 1 := ⟨(discTime_nonneg s.2).trans hq.1,
        hq.2.trans (discTime_lt_one u.toNNReal.2).le⟩
      refine ⟨hq01, ?_⟩
      have hm : wallPt R q ∈ cayley '' (R '' Icc s u.toNNReal) := by
        rw [← wallPt_image_discTime_Icc R hsu.le]
        exact ⟨q, hq, rfl⟩
      obtain ⟨_, ⟨r, hr, rfl⟩, he⟩ := hm
      exact he ▸ frontier_subset_closure (hends r hr)
  · rw [hfc, hfr]
    exact Foundations.Schoenflies.isJordanCurve_image hJ
      (fun z hz => (continuousAt_cayley_of_mem_Hbar (hJH hz)).continuousWithinAt)
      (cayley_injOn_Hbar.mono hJH)
  · simpa only [wallPt, Sec7.PocketCoord.toDisc_realPath_discTime] using hends s ⟨le_rfl, hsu.le⟩
  · simpa only [wallPt, Sec7.PocketCoord.toDisc_realPath_discTime] using hends u.toNNReal ⟨hsu.le, le_rfl⟩
  · intro he
    have hprops := GW3.wallPt_props (GW4Reg.isProperCurve_of_isCompleteSimpleFlow hR) hR.2.2.1
    exact (WangWu.discTime_lt_discTime s.2 (by exact_mod_cast hsu)).ne
      (hprops.2.1 (Ico_subset_Icc_self (discTime_mem_Ico s.2))
        (Ico_subset_Icc_self (discTime_mem_Ico u.toNNReal.2)) he)

end InteractingSLE.Theorem14.PocketCompass
