/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.PocketCompassChart

/-!
# Bounded pocket orientation from winding

PROVE-POCKETSHAPE. A bounded shaped component has a chart whose positive real
boundary parameters increase along the right wall. Comparison of component
charts then proves the previously outstanding bounded orientation statement.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Bornology Metric Function
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)
open QuantumZipper.CA (cayley cayleyInv)

universe u

namespace InteractingSLE.Theorem14.PocketCompass

open GW4Reg GW4BarrierSelf WangWu Sec7.Lemma71I Sec7.Lemma71K

/-- A bounded interior pocket shape has a chart with increasing positive boundary times. -/
theorem exists_ordered_chart_of_bounded_shape {R L : ℝ≥0 → ℂ}
    (hR : IsSimpleProper R) (hL : IsSimpleProper L)
    (hord : ∀ s s' t t' : ℝ≥0, R s = L t → R s' = L t' → (s < s' ↔ t < t'))
    {C : Set ℂ} (hC : C ∈ betweenComponents (range R) (range L))
    {s t : ℝ≥0} {u v : ℝ≥0∞} (hs : IsPocketShape R L C s t u v) (hu : u ≠ ⊤) :
    ∃ c : Chart, IsComponentChart (range R) (range L) C c ∧
      ∀ (x y : ℝ) (r q : ℝ≥0), 0 < x → x < y →
        Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 (R r)) →
        Tendsto c.2.1 (𝓝[H] (y : ℂ)) (𝓝 (R q)) → r < q := by
  have hRb := PocketSector.isCompleteSimpleFlow_of_isSimpleProper hR
  have hLb := PocketSector.isCompleteSimpleFlow_of_isSimpleProper hL
  have hCo := isOpen_of_mem_betweenComponents (isClosed_range_of_isCompleteSimpleFlow hRb)
    (isClosed_range_of_isCompleteSimpleFlow hLb) hC
  have hsub := Sec7.Prop74B.subset_of_mem_betweenComponents hC
  have hCH : C ⊆ H := fun z hz => (hsub hz).1
  have hCR : Disjoint C (range R) := disjoint_left.2 fun z hz hr => (hsub hz).2 (Or.inl hr)
  obtain ⟨z, hz, -, -, hCz⟩ := id hC
  have hCc : IsConnected C := hCz ▸ isConnected_connectedComponentIn_iff.2 hz
  let a := discTime (s : ℝ)
  let b := discTime (u.toNNReal : ℝ)
  have hM : IsMarkedPocket R C a b := isMarkedPocket_of_bounded_shape hRb hLb hord hC hs hu
  obtain ⟨ha0, hab, hb1, -, hJ, hpa, hpb, hpq⟩ := id hM
  obtain ⟨Ψ, hU⟩ := Sec7.PocketJordan.exists_isBdryUniformizer
    (Sec7.Lemma71F.isOpen_cayley_image hCo hCH) (Sec7.Lemma71F.isConnected_cayley_image hCc hCH)
    (Sec7.Lemma71F.isBounded_cayley_image hCH) hJ hpa hpb hpq
  have hside : cayley '' C ⊆ crossSide (wallPt R) 1 := by
    obtain ⟨-, -, hside⟩ := PocketRim.cayley_between_component hR hL hC
    exact fun z hz => (hside hz).1
  have hpos := re_pos_of_markedPocket_crossSide hR hCo hCc.isPreconnected hCH hCR hM hside hU
  have hfr : frontier (cayley '' C) ⊆ wallPt R '' Icc a b ∪ cayley '' range L := by
    rw [frontier_cayley_eq_of_isBounded hCo hCH (hs.entry hu).2.2,
      PocketShapeDet.frontier_eq_of_bounded_shape hRb hLb hord hC hs hu, image_union]
    have hsu := (PocketShapeDet.finite_parameters hord hs hu).2.1
    change cayley '' (R '' Icc s u.toNNReal) ∪ cayley '' (L '' Icc t v.toNNReal) ⊆ _
    rw [← wallPt_image_discTime_Icc R hsu.le]
    exact union_subset_union subset_rfl (image_mono (image_subset_range _ _))
  obtain ⟨c, hc, hright⟩ := exists_chart_of_marked_uniformizer hR
    (fun z hz => by obtain ⟨r, rfl⟩ := hz; exact hLb.2.2.2.1 r) hCo hCH hCR hM hfr hU hpos
  have hmono := strictMonoOn_marked_right hR hCo hCH hCR hM hU hpos
  refine ⟨c, hc, fun x y r q hx hxy hxr hyq => ?_⟩
  obtain ⟨sx, hsx, hlimx, hvalx⟩ := hright x hx
  obtain ⟨sy, hsy, hlimy, hvaly⟩ := hright y (hx.trans hxy)
  have hsx01 : sx ∈ Ico (0 : ℝ) 1 := ⟨ha0.trans hsx.1.le, hsx.2.trans_le hb1⟩
  have hsy01 : sy ∈ Ico (0 : ℝ) 1 := ⟨ha0.trans hsy.1.le, hsy.2.trans_le hb1⟩
  have hxR : cayleyInv (wallPt R sx) = R (arcTime sx).toNNReal := by
    rw [wallPt, toDisc_of_lt hsx01.2, realPath, cayleyInv_cayley_of_mem_Hbar (hRb.2.2.2.1 _)]
  have hyR : cayleyInv (wallPt R sy) = R (arcTime sy).toNNReal := by
    rw [wallPt, toDisc_of_lt hsy01.2, realPath, cayleyInv_cayley_of_mem_Hbar (hRb.2.2.2.1 _)]
  have hr : r = (arcTime sx).toNNReal := by
    have : (𝓝[H] (x : ℂ)).NeBot := FiniteEndpoint.neBot_nhdsWithin_H (by simp)
    exact hR.2.1 (tendsto_nhds_unique hxr (hxR ▸ hlimx))
  have hq : q = (arcTime sy).toNNReal := by
    have : (𝓝[H] (y : ℂ)).NeBot := FiniteEndpoint.neBot_nhdsWithin_H (by simp)
    exact hR.2.1 (tendsto_nhds_unique hyq (hyR ▸ hlimy))
  have hss : sx < sy := lt_of_not_ge fun he => by
    have hm := hmono.monotoneOn (Ioo_subset_Ico_self hsy) (Ioo_subset_Ico_self hsx) he
    rw [hvalx, hvaly, Complex.ofReal_re, Complex.ofReal_re] at hm
    exact not_le_of_gt hxy hm
  rw [hr, hq]
  change ((arcTime sx).toNNReal : ℝ) < ((arcTime sy).toNNReal : ℝ)
  rw [Real.coe_toNNReal _ (arcTime_nonneg hsx01), Real.coe_toNNReal _ (arcTime_nonneg hsy01)]
  exact strictMonoOn_arcTime hsx01 hsy01 hss

/-- The one-chart bounded orientation input is discharged. -/
theorem oneInteriorChartBoundaryOrderStatement : PocketRim.OneInteriorChartBoundaryOrderStatement := by
  intro R L hR hL hord C hC s t u v hs hu _
  exact exists_ordered_chart_of_bounded_shape hR hL hord hC hs hu

/-- Positive boundary order for strictly interior walls, for every component chart. -/
theorem interiorBoundedPositiveBoundaryOrderStatement :
    PocketSector.InteriorBoundedPositiveBoundaryOrderStatement :=
  PocketRim.oneInteriorChartBoundaryOrderStatement_iff.1 oneInteriorChartBoundaryOrderStatement

/-- Positive boundary order also holds for the original walls with real connectors. -/
theorem boundedPositiveBoundaryOrderStatement : PocketShapeFin.BoundedPositiveBoundaryOrderStatement :=
  PocketSector.boundedPositiveBoundaryOrderStatement_iff_interior.2 interiorBoundedPositiveBoundaryOrderStatement

/-- A bounded shaped pocket's chart cannot send its closing endpoint to zero. -/
theorem boundedChartEntryExclusionStatement : PocketShapeDet.BoundedChartEntryExclusionStatement :=
  PocketShapeFin.boundedChartEntryExclusionStatement_of_positive_order boundedPositiveBoundaryOrderStatement

/-- Every shaped pocket's chart has its zero-limit at the opening endpoint. -/
theorem chart_zero_eq_exit {R L : ℝ≥0 → ℂ}
    (hR : GB11.IsCompleteSimpleFlow R) (hL : GB11.IsCompleteSimpleFlow L)
    (hord : ∀ s s' t t' : ℝ≥0, R s = L t → R s' = L t' → (s < s' ↔ t < t'))
    {C : Set ℂ} (hC : C ∈ betweenComponents (range R) (range L))
    {s t : ℝ≥0} {u v : ℝ≥0∞} (hs : IsPocketShape R L C s t u v)
    {c : Chart} (hc : IsComponentChart (range R) (range L) C c)
    {p : ℂ} (hp : Tendsto c.2.1 (𝓝[H] 0) (𝓝 p)) : p = R s := by
  rcases PocketShapeDet.chart_zero_eq_endpoint hR hL hord hC hs hc hp with he | ⟨hu, he⟩
  · exact he
  · exact (boundedChartEntryExclusionStatement R L hR hL hord C hC s t u v hs hu c hc (he ▸ hp)).elim

/-- Shape existence is now the sole input to the deterministic source target. -/
theorem pocketShapeDetStatement_of_discGapSide (hSide : PocketRim.DiscGapSideStatement) :
    GW4Leaf.PocketShapeDetStatement :=
  PocketRim.pocketShapeDetStatement_of_local_inputs hSide oneInteriorChartBoundaryOrderStatement

/-- The same single planar input suffices for the almost-sure source target. -/
theorem walkPocketShapeRegStatement_of_discGapSide (hSide : PocketRim.DiscGapSideStatement)
    (hCO : WalkContactOrderRegStatement.{u}) (hNC : WalkCont.WalkNoCommonContinuumRegStatement.{u})
    (hSB : SB.SBFrontierRegStatement.{u}) (hA : GW2aContainmentStatement.{u})
    (hGeom : GW3Sided.GW3GeometryRegStatement.{u}) : WalkPocketShapeRegStatement.{u} :=
  PocketRim.walkPocketShapeRegStatement_of_local_inputs hSide oneInteriorChartBoundaryOrderStatement
    hCO hNC hSB hA hGeom

end InteractingSLE.Theorem14.PocketCompass
