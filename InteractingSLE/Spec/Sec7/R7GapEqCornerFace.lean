/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7GapEqCornerLift

/-!
# A selected chart face is a surviving pocket component

PROVE-R7-GAPEQ. Boundary avoidance and one interior witness identify a selected face;
connectedness of all of the surviving pocket is unnecessary. A boundary access to the target
gives adherence, and excluding forbidden outer bulges gives active-visit confinement.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H Hbar fwdHull fwdMap)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Sec7.R7GapEqCorner

open Sec6

/-- A connected open face with no boundary inside `C` maps onto one component of `C ∩ D_r`.
The reverse inclusion uses `g_r` and preconnectedness, so allows other surviving components. -/
theorem image_face_eq_component {W : ℝ → ℝ} {η : ℝ → ℂ} {r : ℝ} {C F : Set ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (hr : 0 ≤ r)
    (hF : IsOpen F) (hFp : IsPreconnected F) (hFH : F ⊆ H)
    (hFC : MapsTo (trMap W 0 r) F C)
    (hbd : ∀ w ∈ frontier F, w ∈ H → trMap W 0 r w ∉ C)
    {p : ℂ} (hp : p ∈ F) :
    trMap W 0 r '' F = connectedComponentIn (C ∩ (H \ fwdHull W r)) (trMap W 0 r p) := by
  let Q := connectedComponentIn (C ∩ (H \ fwdHull W r)) (trMap W 0 r p)
  have hf : ContinuousOn (trMap W 0 r) H :=
    (YuanSimpleApprox.trMap_continuousOn hη hW hW0 le_rfl hr).mono
      QuantumZipper.H_subset_Hbar
  have hsub : trMap W 0 r '' F ⊆ C ∩ (H \ fwdHull W r) := by
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨hFC hw, trMap_zero_mem_domain hW hW0 hr (hFH hw)⟩
  have hforward : trMap W 0 r '' F ⊆ Q :=
    (hFp.image _ (hf.mono hFH)).subset_connectedComponentIn ⟨p, hp, rfl⟩ hsub
  have hQsub : Q ⊆ C ∩ (H \ fwdHull W r) := connectedComponentIn_subset _ _
  have hg : ContinuousOn (fwdMap W r) (H \ fwdHull W r) :=
    (QuantumZipper.FwdHolo.differentiableOn_fwdMap hW hr).continuousOn
  have hGpre : IsPreconnected (fwdMap W r '' Q) :=
    isPreconnected_connectedComponentIn.image _ (hg.mono fun _ hw => (hQsub hw).2)
  have hGfr : Disjoint (fwdMap W r '' Q) (frontier F) := by
    refine Set.disjoint_left.2 ?_
    rintro _ ⟨z, hz, rfl⟩ hw
    have hzD := (hQsub hz).2
    have hn := hbd _ hw (QuantumZipper.FwdHolo.mapsTo_fwdMap hW hr hzD)
    rw [trMap_zero_fwdMap hW hW0 hr hzD] at hn
    exact hn (hQsub hz).1
  have hpG : p ∈ fwdMap W r '' Q :=
    ⟨trMap W 0 r p, hforward ⟨p, hp, rfl⟩, fwdMap_trMap_zero hW hW0 hr (hFH hp)⟩
  have hGF : fwdMap W r '' Q ⊆ F :=
    subset_of_isPreconnected_of_disjoint_frontier hGpre hF ⟨p, hpG, hp⟩ hGfr
  refine Subset.antisymm hforward ?_
  intro z hz
  exact ⟨fwdMap W r z, hGF ⟨z, hz, rfl⟩, trMap_zero_fwdMap hW hW0 hr (hQsub hz).2⟩

/-- The face image need only avoid the pocket boundary and have one interior witness;
the boundary of the face must itself map outside the pocket. -/
theorem image_innerSide_eq_component {W : ℝ → ℝ} {η : ℝ → ℂ} {r : ℝ} {C Γ : Set ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (hr : 0 ≤ r)
    (hC : IsOpen C) (hΓ : LQGMetric.JordanMap.IsJordanCurve Γ) (hΓH : Γ ⊆ Hbar)
    (hfr : ∀ w ∈ innerSide Γ, trMap W 0 r w ∉ frontier C)
    (hbd : ∀ w ∈ Γ, w ∈ H → trMap W 0 r w ∉ C)
    {p : ℂ} (hp : p ∈ innerSide Γ) (hpC : trMap W 0 r p ∈ C) :
    MapsTo (trMap W 0 r) (innerSide Γ) C ∧
      trMap W 0 r '' innerSide Γ =
        connectedComponentIn (C ∩ (H \ fwdHull W r)) (trMap W 0 r p) := by
  obtain ⟨-, -, hfront, -, hFo, -, -, hFp, -⟩ := jordan_sides hΓ hΓH
  have hFH := innerSide_subset_H hΓ hΓH
  have hf := (YuanSimpleApprox.trMap_continuousOn hη hW hW0 le_rfl hr).mono
    (hFH.trans QuantumZipper.H_subset_Hbar)
  have hFC : MapsTo (trMap W 0 r) (innerSide Γ) C :=
    mapsTo_of_isPreconnected hC hFp hf hfr hp hpC
  exact ⟨hFC, image_face_eq_component hη hW hW0 hr hFo hFp hFH hFC
    (fun w hw => hbd w (hfront ▸ hw)) hp⟩

/-- An interior point on the chart boundary landing at the target supplies target adherence.
This is an access, rather than an identification of all prime ends at the physical point. -/
theorem target_mem_closure_face_image {W : ℝ → ℝ} {η : ℝ → ℂ} {r : ℝ} {Γ : Set ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (hr : 0 ≤ r)
    (hΓ : LQGMetric.JordanMap.IsJordanCurve Γ) (hΓH : Γ ⊆ Hbar)
    {z x : ℂ} (hz : z ∈ Γ) (hzH : z ∈ H) (hzx : trMap W 0 r z = x) :
    x ∈ closure (trMap W 0 r '' innerSide Γ) := by
  have hfront := (jordan_sides hΓ hΓH).2.2.1
  have hzfr : z ∈ frontier (innerSide Γ) := by rwa [hfront]
  have hzcl : z ∈ closure (innerSide Γ) := frontier_subset_closure hzfr
  have hsub : innerSide Γ ⊆ Hbar := (innerSide_subset_H hΓ hΓH).trans QuantumZipper.H_subset_Hbar
  rw [← hzx]
  exact ((YuanSimpleApprox.trMap_continuousOn hη hW hW0 le_rfl hr z
    (QuantumZipper.H_subset_Hbar hzH)).mono hsub).mem_closure_image hzcl

/-- Active interior visits lie in the selected face when every other pocket preimage is in a
forbidden bulge. The trace-avoidance hypothesis is the usual outer-wall exclusion. -/
theorem ownFuture_mem_face_of_forbidden_bulges {W : ℝ → ℝ} {η : ℝ → ℂ} {r : ℝ}
    {C F B : Set ℂ} (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hr : 0 ≤ r) (havoid : ∀ t, r ≤ t → η t ∉ B)
    (hbulge : ∀ w ∈ H, trMap W 0 r w ∈ C → w ∉ F → trMap W 0 r w ∈ B) :
    ∀ t, r ≤ t → η t ∈ C → trMap W r t 0 ∈ H → trMap W r t 0 ∈ F := by
  intro t ht htC htH
  by_contra hn
  have he := traceMapOut_trMap_zero hη hW hW0 hr ht
  have hB := hbulge _ htH (he.symm ▸ htC) hn
  rw [he] at hB
  exact havoid t ht hB

end InteractingSLE.Sec7.R7GapEqCorner
