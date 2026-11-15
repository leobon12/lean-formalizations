/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7InfinityChartEnd

/-!
# A compactified face maps onto a physical component

PROVE-R7-GAPEQ. Transport the existing open-face component theorem through the
half-plane automorphism. Only the boundary geometry and an interior witness are needed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H Hbar fwdHull fwdMap)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Sec7.R7InfinityChart

open Sec6 R7GapEqCorner

/-- The inverse image of a half-plane face is its relative preimage under the
compactifying automorphism. -/
theorem inverse_face_eq {a : ℝ} {F : Set ℂ} (hFH : F ⊆ H) :
    psiMapInv a '' F = H ∩ psiMap a ⁻¹' F := by
  ext w
  constructor
  · rintro ⟨ζ, hζ, rfl⟩
    exact ⟨psiMapInv_mem_H (hFH hζ), by rwa [mem_preimage, psiMap_psiMapInv]⟩
  · rintro ⟨-, hw⟩
    exact ⟨psiMap a w, hw, psiMapInv_psiMap w⟩

/-- Relative openness and the boundary identification transfer through the
compactifying automorphism at all points of the half-plane. -/
theorem inverse_face_topology {a : ℝ} {Γ : Set ℂ}
    (hΓ : LQGMetric.JordanMap.IsJordanCurve Γ) (hΓH : Γ ⊆ Hbar) :
    IsOpen (psiMapInv a '' innerSide Γ) ∧
      IsPreconnected (psiMapInv a '' innerSide Γ) ∧
      ∀ w ∈ frontier (psiMapInv a '' innerSide Γ), w ∈ H → psiMap a w ∈ Γ := by
  obtain ⟨-, -, hfront, -, hFo, -, -, hFp, -⟩ := jordan_sides hΓ hΓH
  have hFH := innerSide_subset_H hΓ hΓH
  have hψH : ContinuousOn (psiMap a) H := continuousOn_psiMap.mono
    (fun w hw he => not_mem_H_ofReal a (he ▸ hw))
  have hFopen : IsOpen (psiMapInv a '' innerSide Γ) := by
    rw [inverse_face_eq hFH]
    exact hψH.isOpen_inter_preimage QuantumZipper.isOpen_H hFo
  have hFinv : ContinuousOn (psiMapInv a) (innerSide Γ) := continuousOn_psiMapInv.mono
    (fun ζ hζ he => by
      have hh := hFH hζ
      rw [show ζ = 0 from he] at hh
      exact lt_irrefl _ (show (0 : ℝ) < (0 : ℂ).im from hh))
  refine ⟨hFopen, hFp.image _ hFinv, ?_⟩
  intro w hw hwH
  have hc := hψH.continuousAt (QuantumZipper.isOpen_H.mem_nhds hwH)
  have hm := hc.continuousWithinAt.mem_closure_image (frontier_subset_closure hw)
  rw [image_image] at hm
  have hid : (fun ζ => psiMap a (psiMapInv a ζ)) = id := funext psiMap_psiMapInv
  rw [hid, image_id] at hm
  rw [← hfront, hFo.frontier_eq]
  refine ⟨hm, fun hin => ?_⟩
  have hwF : w ∈ psiMapInv a '' innerSide Γ := ⟨psiMap a w, hin, psiMapInv_psiMap w⟩
  exact (hFopen.frontier_eq ▸ hw).2 hwF

/-- Boundary avoidance and an interior witness identify the whole physical face
image with one component. This is the existing component theorem in the inverse chart. -/
theorem image_compact_face_eq_component {W : ℝ → ℝ} {η : ℝ → ℂ}
    {s a : ℝ} {C Γ : Set ℂ} {p : ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (hs : 0 ≤ s)
    (hCo : IsOpen C) (hΓ : LQGMetric.JordanMap.IsJordanCurve Γ) (hΓH : Γ ⊆ Hbar)
    (hfr : ∀ ζ ∈ innerSide Γ, trMap W 0 s (psiMapInv a ζ) ∉ frontier C)
    (hbd : ∀ ζ ∈ Γ, ζ ∈ H → trMap W 0 s (psiMapInv a ζ) ∉ C)
    (hp : p ∈ innerSide Γ) (hpC : trMap W 0 s (psiMapInv a p) ∈ C) :
    MapsTo (fun ζ => trMap W 0 s (psiMapInv a ζ)) (innerSide Γ) C ∧
      (fun ζ => trMap W 0 s (psiMapInv a ζ)) '' innerSide Γ =
        connectedComponentIn (C ∩ (H \ fwdHull W s)) (trMap W 0 s (psiMapInv a p)) := by
  let F := psiMapInv a '' innerSide Γ
  obtain ⟨hFo, hFp, hFbd⟩ := inverse_face_topology (a := a) hΓ hΓH
  have hFH : F ⊆ H := by rintro _ ⟨ζ, hζ, rfl⟩; exact psiMapInv_mem_H (innerSide_subset_H hΓ hΓH hζ)
  have hf : ContinuousOn (trMap W 0 s) F :=
    (YuanSimpleApprox.trMap_continuousOn hη hW hW0 le_rfl hs).mono
      (hFH.trans QuantumZipper.H_subset_Hbar)
  have hFC : MapsTo (trMap W 0 s) F C := mapsTo_of_isPreconnected hCo hFp hf
    (by rintro _ ⟨ζ, hζ, rfl⟩; exact hfr ζ hζ) ⟨p, hp, rfl⟩ hpC
  have hbdF : ∀ w ∈ frontier F, w ∈ H → trMap W 0 s w ∉ C := by
    intro w hw hwH
    have hwp : w ≠ a := fun he => not_mem_H_ofReal a (he ▸ hwH)
    have hn := hbd _ (hFbd w hw hwH) ((psiMap_mem_H_iff hwp).2 hwH)
    rwa [psiMapInv_psiMap] at hn
  refine ⟨fun ζ hζ => hFC ⟨ζ, hζ, rfl⟩, ?_⟩
  have heq := image_face_eq_component hη hW hW0 hs hFo hFp hFH hFC hbdF ⟨p, hp, rfl⟩
  rwa [image_image] at heq

/-- The remaining interior side selection is explicit: the inner face avoids the
physical frontier and has one point in the pocket. -/
def InfiniteFaceSides (W : ℝ → ℝ) (C : Set ℂ) (s a : ℝ) (Γ : Set ℂ) : Prop :=
  (∀ ζ ∈ innerSide Γ, trMap W 0 s (psiMapInv a ζ) ∉ frontier C) ∧
    ∃ p ∈ innerSide Γ, trMap W 0 s (psiMapInv a p) ∈ C

/-- The previous whole-component chart hypothesis follows from the two local side
inputs; its unboundedness and physical image identity are now theorems. -/
theorem infiniteFaceChart_of_sides {W : ℝ → ℝ} {η : ℝ → ℂ} {s a : ℝ} {C Γ : Set ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (hs : 0 ≤ s)
    (hCo : IsOpen C) (hΓ : LQGMetric.JordanMap.IsJordanCurve Γ) (hΓH : Γ ⊆ Hbar)
    (h0 : (0 : ℂ) ∈ Γ)
    (hbd : ∀ ζ ∈ Γ, ζ ∈ H → trMap W 0 s (psiMapInv a ζ) ∉ C)
    (hsides : InfiniteFaceSides W C s a Γ) :
    ∃ q : ℂ, R7EndFace.InfiniteFaceChart W C s a Γ q := by
  obtain ⟨p, hp, hpC⟩ := hsides.2
  obtain ⟨-, himg⟩ := image_compact_face_eq_component hη hW hW0 hs hCo hΓ hΓH
    hsides.1 hbd hp hpC
  refine ⟨trMap W 0 s (psiMapInv a p), hΓ, hΓH, h0, ⟨hpC, ?_⟩, ?_, himg⟩
  · exact trMap_zero_mem_domain hW hW0 hs (psiMapInv_mem_H (innerSide_subset_H hΓ hΓH hp))
  · rw [← himg]
    exact not_isBounded_physical_innerSide hW hW0 hs hΓ hΓH h0

/-- Conversely, the old whole-component chart supplies both side-selection fields.
Thus the new residual does not strengthen the previous geometric input. -/
theorem infiniteFaceSides_of_chart {W : ℝ → ℝ} {s a : ℝ} {C Γ : Set ℂ} {q : ℂ}
    (hCo : IsOpen C) (hchart : R7EndFace.InfiniteFaceChart W C s a Γ q) :
    InfiniteFaceSides W C s a Γ := by
  have hFC : MapsTo (fun ζ => trMap W 0 s (psiMapInv a ζ)) (innerSide Γ) C := by
    intro ζ hζ
    have hm : trMap W 0 s (psiMapInv a ζ) ∈
        connectedComponentIn (C ∩ (H \ fwdHull W s)) q :=
      hchart.2.2.2.2.2 ▸ mem_image_of_mem _ hζ
    exact (connectedComponentIn_subset _ _ hm).1
  obtain ⟨⟨p, hp, hEq⟩, -⟩ := jordan_sides hchart.1 hchart.2.1
  have hpI : p ∈ innerSide Γ := hEq ▸ mem_connectedComponentIn hp
  exact ⟨fun ζ hζ hfr => (hCo.frontier_eq ▸ hfr).2 (hFC hζ), p, hpI, hFC hpI⟩

/-- With the constructed boundary data, the two residual side inputs are exactly
equivalent to the former chart assertion. -/
theorem infiniteFaceSides_iff_chart {W : ℝ → ℝ} {η : ℝ → ℂ} {s a : ℝ} {C Γ : Set ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0) (hs : 0 ≤ s)
    (hCo : IsOpen C) (hΓ : LQGMetric.JordanMap.IsJordanCurve Γ) (hΓH : Γ ⊆ Hbar)
    (h0 : (0 : ℂ) ∈ Γ)
    (hbd : ∀ ζ ∈ Γ, ζ ∈ H → trMap W 0 s (psiMapInv a ζ) ∉ C) :
    InfiniteFaceSides W C s a Γ ↔ ∃ q : ℂ, R7EndFace.InfiniteFaceChart W C s a Γ q := by
  exact ⟨infiniteFaceChart_of_sides hη hW hW0 hs hCo hΓ hΓH h0 hbd,
    fun ⟨q, hq⟩ => infiniteFaceSides_of_chart hCo hq⟩

end InteractingSLE.Sec7.R7InfinityChart
