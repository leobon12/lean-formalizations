/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7InfinityAccessFrontier

/-!
# A finite exterior access supplies the compact face's pocket witness

PROVE-R7-GAPEQ. Transport the existing local side argument to the compact chart.
The access is at a surviving outer-tail point, rather than at the target infinity.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H Hbar fwdHull fwdMap)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Sec7.R7InfinityAccess

open Sec6

/-- Exterior local connectivity at a finite surviving boundary point forces a
physical pocket witness in the compact inner face. -/
theorem exists_compact_inner_pocket_of_exterior_access {W : ℝ → ℝ} {η : ℝ → ℂ} {s a : ℝ}
    {C Γ : Set ℂ} (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hs : 0 ≤ s) (hCo : IsOpen C) (hΓ : LQGMetric.JordanMap.IsJordanCurve Γ)
    (hΓH : Γ ⊆ Hbar)
    (hbd : ∀ ζ ∈ Γ, ζ ∈ H → trMap W 0 s (psiMapInv a ζ) ∈ frontier C)
    (hfr : ∀ ζ ∈ innerSide Γ, trMap W 0 s (psiMapInv a ζ) ∉ frontier C)
    {y : ℂ} (hy : y ∈ Γ) (hyH : y ∈ H)
    (hloc : IsLocConnWithin (closure C)ᶜ (trMap W 0 s (psiMapInv a y)))
    (haccess : trMap W 0 s (psiMapInv a y) ∈ closure
      ((H \ fwdHull W s) ∩ (closure C)ᶜ ∩
        ((fun z => psiMap a (fwdMap W s z)) ⁻¹' outerSide Γ))) :
    ∃ p ∈ innerSide Γ, trMap W 0 s (psiMapInv a p) ∈ C := by
  by_contra hn
  push Not at hn
  have hIE : (fun ζ => trMap W 0 s (psiMapInv a ζ)) '' innerSide Γ ⊆ (closure C)ᶜ := by
    rintro _ ⟨ζ, hζ, rfl⟩ hcl
    exact hfr ζ hζ ⟨hcl, by rw [hCo.interior_eq]; exact hn ζ hζ⟩
  have hyInvH := psiMapInv_mem_H (p := a) hyH
  have hxD := trMap_zero_mem_domain hW hW0 hs hyInvH
  obtain ⟨ε, hε, hεD⟩ := Metric.isOpen_iff.1
    (QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW hs) _ hxD
  obtain ⟨S, hS, hSc, hSN⟩ := hloc ε hε
  have hSD : S ⊆ H \ fwdHull W s := fun _ hz => hεD (hS hz).2
  obtain ⟨δ, hδ, hδS⟩ := Metric.mem_nhdsWithin_iff.1 hSN
  obtain ⟨p, hpT, hpd⟩ := Metric.mem_closure_iff.1 haccess δ hδ
  have hpS : p ∈ S := hδS ⟨by rwa [mem_ball, dist_comm], hpT.1.2⟩
  have hgH : ∀ z ∈ S, fwdMap W s z ∈ H :=
    fun z hz => QuantumZipper.FwdHolo.mapsTo_fwdMap hW hs (hSD hz)
  have hκc : ContinuousOn (fun z => psiMap a (fwdMap W s z)) S :=
    continuousOn_psiMap.comp
      ((QuantumZipper.FwdHolo.differentiableOn_fwdMap hW hs).continuousOn.mono hSD)
      (fun z hz he => not_mem_H_ofReal a (he ▸ hgH z hz))
  have hκpre := hSc.image _ hκc
  have hκΓ : (fun z => psiMap a (fwdMap W s z)) '' S ⊆ Γᶜ := by
    rintro _ ⟨z, hz, rfl⟩ hζΓ
    have hζH := (psiMap_mem_H_iff
      (fun he => not_mem_H_ofReal a (he ▸ hgH z hz))).2 (hgH z hz)
    have hzf := hbd _ hζΓ hζH
    rw [psiMapInv_psiMap, trMap_zero_fwdMap hW hW0 hs (hSD hz)] at hzf
    exact (hS hz).1 (frontier_subset_closure hzf)
  have hκO : (fun z => psiMap a (fwdMap W s z)) '' S ⊆ outerSide Γ := by
    have hc := hκpre.subset_connectedComponentIn ⟨p, hpS, rfl⟩ hκΓ
    rw [outerSide, connectedComponentIn_eq hpT.2]
    exact hc
  have hψInv : ContinuousAt (psiMapInv a) y := continuousOn_psiMapInv.continuousAt
    (isOpen_compl_singleton.mem_nhds (WangWu.ne_zero_of_mem_H hyH))
  have hχ : ContinuousAt (fun ζ => trMap W 0 s (psiMapInv a ζ)) y :=
    ((YuanSimpleApprox.trMap_continuousOn hη hW hW0 le_rfl hs).mono
      QuantumZipper.H_subset_Hbar).continuousAt
      (QuantumZipper.isOpen_H.mem_nhds hyInvH) |>.comp hψInv
  have hxI := hχ.continuousWithinAt.mem_closure_image
    (frontier_subset_closure ((jordan_sides hΓ hΓH).2.2.1.symm ▸ hy))
  obtain ⟨q, hqI, hqd⟩ := Metric.mem_closure_iff.1 hxI δ hδ
  have hqS : q ∈ S := hδS ⟨by rwa [mem_ball, dist_comm], hIE hqI⟩
  obtain ⟨ζ, hζ, rfl⟩ := hqI
  have hζO := hκO ⟨trMap W 0 s (psiMapInv a ζ), hqS, rfl⟩
  change psiMap a (fwdMap W s (trMap W 0 s (psiMapInv a ζ))) ∈ outerSide Γ at hζO
  rw [fwdMap_trMap_zero hW hW0 hs (psiMapInv_mem_H (p := a) (innerSide_subset_H hΓ hΓH hζ)),
    psiMap_psiMapInv] at hζO
  exact disjoint_innerSide_outerSide.le_bot ⟨hζ, hζO⟩

end InteractingSLE.Sec7.R7InfinityAccess
