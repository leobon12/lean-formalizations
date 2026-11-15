/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7EndFaceTails
import InteractingSLE.Spec.Sec7.R7EndFaceLocal
import InteractingSLE.Spec.Sec7.R7EndFaceClipping

/-!
# Unbounded allowed components of the actual infinite-end mixed pockets

PROVE-R7-GAPEQ. Both orientations follow from the contained wall, the clipped
certified frontier, and the already proved Jordan disc topology.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H fwdHull)
open scoped NNReal

namespace InteractingSLE.Sec7.R7EndFace

open Sec6 WangWu Lemma71I PocketCoord PocketJordan R7StopIn

/-- Physical incidence with the infinite end: every surviving component containing
an allowed point is unbounded. -/
def AllowedUnboundedComponents (W : ℝ → ℝ) (C F : Set ℂ) (τ : ℝ) : Prop :=
  ∀ s : ℝ, τ ≤ s → ∀ z ∈ C ∩ (H \ fwdHull W s), z ∉ F →
    ¬ IsBounded (connectedComponentIn (C ∩ (H \ fwdHull W s)) z)

/-- Actual left-outer infinite-end geometry, with no component-incidence premise. -/
theorem allowedUnboundedComponents_leftOuter {R M L : ℝ≥0 → ℂ} {r : ℝ≥0} {τ : ℝ}
    (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0)
    (hM : IsSimpleProper M) (hO : IsOrderedArcs (realPath R) (realPath M) (realPath L))
    (hcR : NoCommonArc M R) (hcL : NoCommonArc M L)
    (houter : range L ⊆ leftSideOf (range M) ∪ range M)
    {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hτ0 : 0 ≤ τ) (hτ : η τ = cfArcRInf R L r 0)
    (hrevR : IsWallReverseVisit R η) (hrevM : IsWallReverseVisit M η) :
    AllowedUnboundedComponents W (cfPocket R L r) (negInv '' leftSideOf (range M)) τ := by
  have hC := h.isCfPocketInf h0
  obtain ⟨B, hBc, hBt, hBH, hBcl, hBrev, hB0, hBmem⟩ :=
    exists_closed_midBarrierInf h h0 hM hO hcR hcL hη.1 hrevM
  obtain ⟨hFo, hFfr⟩ := forbidden_left hM
  obtain ⟨-, hv, huv, -⟩ := h.changeCorner_props
  have hv0 : 0 < rightHi R L r := h0 ▸ huv
  have hfr : frontier (cfPocket R L r) ⊆
      negInv '' leftSideOf (range M) ∪ (cfArcRInf R L r '' Ici 0 ∪ B '' Ici 0) := by
    rw [hC.frontier_eq]
    rintro z (⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩)
    · exact Or.inr (Or.inl ⟨v, hv, rfl⟩)
    · rcases cfArcLInf_mem_of_outer h h0 houter hB0 hBmem hv with hF | hB
      exacts [Or.inl hF, Or.inr (Or.inr hB)]
  intro s hτs
  apply unbounded_component_of_proper_barriers hη hW hW0 (hτ0.trans hτs) hC.isOpen
    (fun _ hp => isLocConnWithin_cfPocket h hp) hFo hC.cont₁ hBc hC.tendsto₁ hBt
    hC.mem_H₁ hBH
    (fun z hz => frontier_subset_closure (by rw [hC.frontier_eq]; exact Or.inl hz)) hBcl
    (rev_inf_of_wall h.right hη.1 hrevR hv0 hv.2) hBrev
    ⟨τ, ⟨hτ0, hτs⟩, hτ⟩ ⟨τ, ⟨hτ0, hτs⟩, hτ.trans hB0.symm⟩ hfr
  exact fun z hz => Or.inr (hBmem z hz.1.1 hz.2 (hFfr z hz.1.2 hz.2))

/-- Actual right-outer infinite-end geometry, keeping the right-labeled entrance. -/
theorem allowedUnboundedComponents_rightOuter {R M L : ℝ≥0 → ℂ} {r : ℝ≥0} {τ : ℝ}
    (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0)
    (hM : IsSimpleProper M) (hO : IsOrderedArcs (realPath R) (realPath M) (realPath L))
    (hcR : NoCommonArc M R) (hcL : NoCommonArc M L)
    (houter : range R ⊆ rightSideOf (range M) ∪ range M)
    {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hτ0 : 0 ≤ τ) (hτ : η τ = cfArcRInf R L r 0)
    (hrevL : IsWallReverseVisit L η) (hrevM : IsWallReverseVisit M η) :
    AllowedUnboundedComponents W (cfPocket R L r) (negInv '' rightSideOf (range M)) τ := by
  have hC := h.isCfPocketInf h0
  obtain ⟨B, hBc, hBt, hBH, hBcl, hBrev, hB0, hBmem⟩ :=
    exists_closed_midBarrierInf h h0 hM hO hcR hcL hη.1 hrevM
  obtain ⟨hFo, hFfr⟩ := forbidden_right hM
  obtain ⟨-, -, -, -, hv, huv, -⟩ := h.changeCorner_props
  have hv0 : 0 < leftHi R L r := h.leftLo_eq_zero_of_rightLo_eq_zero h0 ▸ huv
  have hfr : frontier (cfPocket R L r) ⊆
      negInv '' rightSideOf (range M) ∪ (cfArcLInf R L r '' Ici 0 ∪ B '' Ici 0) := by
    rw [hC.frontier_eq]
    rintro z (⟨v, hv, rfl⟩ | ⟨v, hv, rfl⟩)
    · rcases cfArcRInf_mem_of_outer h h0 houter hB0 hBmem hv with hF | hB
      exacts [Or.inl hF, Or.inr (Or.inr hB)]
    · exact Or.inr (Or.inl ⟨v, hv, rfl⟩)
  intro s hτs
  apply unbounded_component_of_proper_barriers hη hW hW0 (hτ0.trans hτs) hC.isOpen
    (fun _ hp => isLocConnWithin_cfPocket h hp) hFo hC.cont₂ hBc hC.tendsto₂ hBt
    hC.mem_H₂ hBH
    (fun z hz => frontier_subset_closure (by rw [hC.frontier_eq]; exact Or.inr hz)) hBcl
    (rev_inf_of_wall h.left hη.1 hrevL hv0 hv.2) hBrev
    ⟨τ, ⟨hτ0, hτs⟩, hτ.trans hC.seed.symm⟩ ⟨τ, ⟨hτ0, hτs⟩, hτ.trans hB0.symm⟩ hfr
  exact fun z hz => Or.inr (hBmem z hz.1.1 hz.2 (hFfr z hz.1.2 hz.2))

end InteractingSLE.Sec7.R7EndFace
