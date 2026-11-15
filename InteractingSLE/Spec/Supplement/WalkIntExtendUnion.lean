/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntExtendSupport

/-!
# Proper boundary extensions for filled unions

The joint frontier in H lies on one of the two individual frontiers.
Their compact ULC supports therefore give a support for the joint chart.
The existing conformal extension theorem and the inverse displacement
bound supply the proper extension used by the walk reference family.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology Metric Complex
open QuantumZipper (H Hbar)

namespace InteractingSLE.Theorem14.WalkIntExtend

open WalkIntCanon

/-- Compact ULC supports persist when two half-plane hulls are filled
together. No finiteness assumption on the intersection is needed. -/
def CompactBoundarySupport.union {cR cL c : Chart}
    {MR : HullModel cR} {ML : HullModel cL} (M : HullModel c)
    (SR : CompactBoundarySupport MR) (SL : CompactBoundarySupport ML)
    (hM : M.hull = fillH (MR.hull ∪ ML.hull)) : CompactBoundarySupport M := by
  have hRK : MR.hull ⊆ M.hull := fun z hz => by
    rw [hM]
    exact mem_fillH_of_mem_closure (MR.isHull.1 hz) (subset_closure (Or.inl hz))
  have hLK : ML.hull ⊆ M.hull := fun z hz => by
    rw [hM]
    exact mem_fillH_of_mem_closure (ML.isHull.1 hz) (subset_closure (Or.inr hz))
  refine ⟨SR.carrier ∪ SL.carrier, SR.compact.union SL.compact,
    union_subset SR.upper SL.upper,
    QuantumZipper.CA.Topo.ULC.union_of_isCompact_of_isClosed
      SR.compact SL.compact.isClosed SR.ulc SL.ulc, ?_, ?_, ?_⟩
  · rw [union_union_distrib_left]
    exact SR.attached.union (0 : ℂ) (Or.inl (by simp)) (Or.inl (by simp)) SL.attached
  · rintro z ⟨hzfr, hzH⟩
    have hzcl := frontier_subset_closure hzfr
    rw [hM] at hzfr
    have hs := frontier_H_diff_fillH_subset (MR.isHull.2.1.union ML.isHull.2.1) hzfr
    rcases hs with hzero | hs
    · exact ((ne_of_gt (show 0 < z.im from hzH)) hzero).elim
    rw [closure_union] at hs
    rcases hs with hs | hs
    · apply Or.inl
      apply SR.frontier
      refine ⟨?_, hzH⟩
      rw [MR.isHull.isOpen.frontier_eq]
      exact ⟨closure_mono (sdiff_subset_sdiff_right hRK) hzcl,
        fun hz => hz.2 (MR.isHull.mem_of_mem_closure hzH hs)⟩
    · apply Or.inr
      apply SL.frontier
      refine ⟨?_, hzH⟩
      rw [ML.isHull.isOpen.frontier_eq]
      exact ⟨closure_mono (sdiff_subset_sdiff_right hLK) hzcl,
        fun hz => hz.2 (ML.isHull.mem_of_mem_closure hzH hs)⟩
  · rintro z ⟨hz, hzH⟩
    rcases hz with hz | hz
    · exact hRK (SR.hull ⟨hz, hzH⟩)
    · exact hLK (SL.hull ⟨hz, hzH⟩)

/-- The existing ULC extension theorem gives a proper inverse extension
when the inverse also has bounded displacement in H. -/
theorem hasProperBdryExt_of_compactBoundarySupport {c : Chart} (M : HullModel c)
    (S : CompactBoundarySupport M) (hc : c.IsConformal)
    (hbound : ∃ B : ℝ, ∀ z ∈ H, ‖c.2.1 z - z‖ ≤ B) :
    GW1P.HasProperBdryExt c := by
  obtain ⟨B, hB⟩ := hbound
  have hInf : Tendsto c.2.1 (Bornology.cobounded ℂ ⊓ 𝓟 H)
      (Bornology.cobounded ℂ) := by
    refine tendsto_norm_atTop_iff_cobounded.1 ?_
    refine tendsto_atTop_mono' _ ?_ (tendsto_atTop_add_const_right _ (-B)
      (tendsto_norm_cobounded_atTop.mono_left inf_le_left))
    filter_upwards [mem_inf_of_right (mem_principal_self H)] with z hz
    have h1 := hB z hz
    have h2 := norm_le_norm_add_norm_sub' z (c.2.1 z)
    rw [norm_sub_rev] at h2
    linarith
  have hfront : frontier (H \ M.hull) ⊆ {z : ℂ | z.im = 0} ∪ S.carrier := by
    intro z hz
    by_cases hzH : z ∈ H
    · exact Or.inr (S.frontier ⟨hz, hzH⟩)
    · left
      have hbar : z ∈ Hbar := closure_minimal
        (sdiff_subset.trans QuantumZipper.H_subset_Hbar) QuantumZipper.isClosed_Hbar
        (frontier_subset_closure hz)
      exact le_antisymm (not_lt.1 hzH) hbar
  have hdis : Disjoint (H \ M.hull) S.carrier :=
    Set.disjoint_left.2 fun z hz hs => hz.2 (S.hull ⟨hs, hz.1⟩)
  have hbij := hc.isConformalBijection
  rw [M.dom_eq] at hbij
  obtain ⟨F, hEq, hFc, -, -⟩ := exists_continuousOn_extension_of_ulc M.isHull.isOpen
    sdiff_subset hfront hdis S.compact S.upper S.ulc S.attached hbij hInf
  have hlim : ∀ p ∈ Hbar, Tendsto c.2.1 (𝓝[H] p) (𝓝 (F p)) := by
    intro p hp
    exact (((hFc p hp).mono QuantumZipper.H_subset_Hbar).tendsto).congr'
      (eventually_nhdsWithin_of_forall fun _ hz => hEq hz)
  refine ⟨F, B, hlim, fun p hp => ?_⟩
  have := GW1P.neBot_nhdsWithin_H hp
  apply le_of_tendsto
    (((hlim p hp).sub (tendsto_nhdsWithin_of_tendsto_nhds tendsto_id)).norm)
  exact eventually_nhdsWithin_of_forall fun z hz => hB z hz

/-- Filling two proper prefix hulls preserves proper inverse extension
for every conformal joint chart with bounded inverse displacement. -/
theorem hasProperBdryExt_of_filled_union {cR cL c : Chart}
    (MR : HullModel cR) (ML : HullModel cL) (M : HullModel c)
    (hR : cR.IsConformal) (hL : cL.IsConformal)
    (hRp : GW1P.HasProperBdryExt cR) (hLp : GW1P.HasProperBdryExt cL)
    (hc : c.IsConformal) (hbound : ∃ B : ℝ, ∀ z ∈ H, ‖c.2.1 z - z‖ ≤ B)
    (hM : M.hull = fillH (MR.hull ∪ ML.hull)) : GW1P.HasProperBdryExt c := by
  obtain ⟨SR⟩ := exists_compactBoundarySupport MR hR hRp
  obtain ⟨SL⟩ := exists_compactBoundarySupport ML hL hLp
  exact hasProperBdryExt_of_compactBoundarySupport M (SR.union M SL hM) hc hbound

end InteractingSLE.Theorem14.WalkIntExtend
