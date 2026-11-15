/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7InfinityChartMixed
import InteractingSLE.Spec.Sec7.OuterInCollarInf

/-!
# Exterior access in a compactified current chart

PROVE-R7-GAPEQ. A single real exterior access outside the compact boundary selects
the outer Jordan side. Physical closure exclusion then follows by local continuity.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H Hbar fwdHull fwdMap)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Sec7.R7InfinityAccess

open Sec6

/-- One real access outside the curve selects the entire preconnected exterior's
compact lift. This does not assume that the compact lift is unbounded. -/
theorem compact_lift_exterior_subset_outerSide {W : ℝ → ℝ} {s a : ℝ} {Γ E : Set ℂ}
    (hW : Continuous W) (hW0 : W 0 = 0) (hs : 0 ≤ s)
    (hΓ : LQGMetric.JordanMap.IsJordanCurve Γ) (hΓH : Γ ⊆ Hbar)
    (hE : IsPreconnected E) (hED : E ⊆ H \ fwdHull W s)
    (hbd : ∀ ζ ∈ Γ, ζ ∈ H → trMap W 0 s (psiMapInv a ζ) ∉ E)
    (haccess : ∃ x : ℝ, (x : ℂ) ∈ closure (psiMap a '' (fwdMap W s '' E)) ∧ (x : ℂ) ∉ Γ) :
    psiMap a '' (fwdMap W s '' E) ⊆ outerSide Γ := by
  have hgH : ∀ z ∈ E, fwdMap W s z ∈ H :=
    fun z hz => QuantumZipper.FwdHolo.mapsTo_fwdMap hW hs (hED hz)
  have hc : ContinuousOn (fun z => psiMap a (fwdMap W s z)) E :=
    continuousOn_psiMap.comp
      ((QuantumZipper.FwdHolo.differentiableOn_fwdMap hW hs).continuousOn.mono hED)
      (fun z hz he => not_mem_H_ofReal a (he ▸ hgH z hz))
  have hpre : IsPreconnected (psiMap a '' (fwdMap W s '' E)) := by
    rw [image_image]
    exact hE.image _ hc
  have hsub : psiMap a '' (fwdMap W s '' E) ⊆ Γᶜ := by
    rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩ hζ
    have hH := (psiMap_mem_H_iff
      (fun he => not_mem_H_ofReal a (he ▸ hgH z hz))).2 (hgH z hz)
    have hn := hbd _ hζ hH
    rw [psiMapInv_psiMap, trMap_zero_fwdMap hW hW0 hs (hED hz)] at hn
    exact hn hz
  obtain ⟨x, hx, hxΓ⟩ := haccess
  have hxO := ofReal_mem_outerSide hΓ hΓH hxΓ
  have hOo := (jordan_sides hΓ hΓH).2.2.2.2.2.1
  obtain ⟨w, hwO, hw⟩ := mem_closure_iff.1 hx _ hOo hxO
  have hcomp := hpre.subset_connectedComponentIn hw hsub
  rw [outerSide, connectedComponentIn_eq hwO]
  exact hcomp

/-- The compact inner face cannot land in the physical closure of an exterior
whose compact lift lies on the outer side. -/
theorem compact_inner_not_mem_closure_exterior {W : ℝ → ℝ} {s a : ℝ} {Γ E : Set ℂ}
    (hW : Continuous W) (hW0 : W 0 = 0) (hs : 0 ≤ s)
    (hΓ : LQGMetric.JordanMap.IsJordanCurve Γ) (hΓH : Γ ⊆ Hbar)
    (hEO : psiMap a '' (fwdMap W s '' E) ⊆ outerSide Γ) :
    ∀ ζ ∈ innerSide Γ, trMap W 0 s (psiMapInv a ζ) ∉ closure E := by
  intro ζ hζ hcl
  have hζH := innerSide_subset_H hΓ hΓH hζ
  have hwH := psiMapInv_mem_H (p := a) hζH
  have hzD := trMap_zero_mem_domain hW hW0 hs hwH
  have hg : ContinuousAt (fwdMap W s) (trMap W 0 s (psiMapInv a ζ)) :=
    (QuantumZipper.FwdHolo.differentiableOn_fwdMap hW hs).continuousOn.continuousAt
      (QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW hs |>.mem_nhds hzD)
  have hψ : ContinuousAt (psiMap a) (fwdMap W s (trMap W 0 s (psiMapInv a ζ))) := by
    rw [fwdMap_trMap_zero hW hW0 hs hwH]
    exact continuousOn_psiMap.continuousAt (isOpen_compl_singleton.mem_nhds
      (fun he => not_mem_H_ofReal a (he ▸ hwH)))
  have hm := (hψ.comp hg).continuousWithinAt.mem_closure_image (s := E) hcl
  simp only [Function.comp_def] at hm
  rw [fwdMap_trMap_zero hW hW0 hs hwH, psiMap_psiMapInv,
    ← image_image (psiMap a) (fwdMap W s)] at hm
  have hd := (disjoint_innerSide_outerSide (J := Γ)).closure_right
    (jordan_sides hΓ hΓH).2.2.2.2.1
  exact Set.disjoint_left.1 hd hζ (closure_mono hEO hm)

/-- Physical adherence to the untouched exterior supplies an access in the
domain, outside the closed pocket, on the compact outer side. -/
theorem mem_closure_compact_exterior_access {W : ℝ → ℝ} {s a : ℝ} {C Γ E : Set ℂ} {x : ℂ}
    (hx : x ∈ closure E) (hED : E ⊆ H \ fwdHull W s)
    (hEC : E ⊆ (closure C)ᶜ) (hEO : psiMap a '' (fwdMap W s '' E) ⊆ outerSide Γ) :
    x ∈ closure ((H \ fwdHull W s) ∩ (closure C)ᶜ ∩
      ((fun z => psiMap a (fwdMap W s z)) ⁻¹' outerSide Γ)) := by
  apply closure_mono _ hx
  intro z hz
  exact ⟨⟨hED hz, hEC hz⟩, hEO ⟨_, ⟨z, hz, rfl⟩, rfl⟩⟩

end InteractingSLE.Sec7.R7InfinityAccess
