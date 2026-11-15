/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7LocalFaceAccess

/-!
# A locally connected physical exterior determines the chart's inner side

PROVE-R7-GAPEQ. At a surviving boundary point, an exterior access on the outer chart side
prevents the inner chart face from also mapping into the physical exterior. A small connected
relative exterior neighborhood would otherwise join the two Jordan sides off their boundary.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H Hbar fwdHull fwdMap)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Sec7.R7LocalFace

open Sec6

/-- **An exterior access pins the correct inner side.** The physical exterior is locally
connected at the surviving junction, the chart boundary maps to the physical frontier, and
there is no additional physical frontier inside the chart face. These facts force a pocket
witness in the inner chart face. -/
theorem exists_inner_pocket_of_exterior_access {W : ℝ → ℝ} {η : ℝ → ℂ} {r : ℝ}
    {C Γ : Set ℂ} (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hr : 0 ≤ r) (hCo : IsOpen C) (hΓ : LQGMetric.JordanMap.IsJordanCurve Γ)
    (hΓH : Γ ⊆ Hbar) (hbd : ∀ w ∈ Γ, w ∈ H → trMap W 0 r w ∈ frontier C)
    (hfr : ∀ w ∈ innerSide Γ, trMap W 0 r w ∉ frontier C)
    {y : ℂ} (hy : y ∈ Γ) (hyH : y ∈ H)
    (hloc : IsLocConnWithin (closure C)ᶜ (trMap W 0 r y))
    (haccess : trMap W 0 r y ∈ closure
      ((H \ fwdHull W r) ∩ (closure C)ᶜ ∩ (fwdMap W r ⁻¹' outerSide Γ))) :
    ∃ p ∈ innerSide Γ, trMap W 0 r p ∈ C := by
  by_contra hn
  push Not at hn
  have hIE : trMap W 0 r '' innerSide Γ ⊆ (closure C)ᶜ := by
    rintro _ ⟨w, hw, rfl⟩ hcl
    exact hfr w hw ⟨hcl, by rw [hCo.interior_eq]; exact hn w hw⟩
  have hxD := trMap_zero_mem_domain hW hW0 hr hyH
  obtain ⟨ε, hε, hεD⟩ := Metric.isOpen_iff.1
    (QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW hr) _ hxD
  obtain ⟨S, hS, hSc, hSN⟩ := hloc ε hε
  have hSD : S ⊆ H \ fwdHull W r := fun _ hz => hεD (hS hz).2
  obtain ⟨δ, hδ, hδS⟩ := Metric.mem_nhdsWithin_iff.1 hSN
  obtain ⟨p, hpT, hpd⟩ := Metric.mem_closure_iff.1 haccess δ hδ
  have hpS : p ∈ S := hδS ⟨by rwa [mem_ball, dist_comm], hpT.1.2⟩
  have hgSc : IsPreconnected (fwdMap W r '' S) := hSc.image _
    ((QuantumZipper.FwdHolo.differentiableOn_fwdMap hW hr).continuousOn.mono hSD)
  have hgSΓ : fwdMap W r '' S ⊆ Γᶜ := by
    rintro _ ⟨z, hz, rfl⟩ hzΓ
    have hzf := hbd _ hzΓ (QuantumZipper.FwdHolo.mapsTo_fwdMap hW hr (hSD hz))
    rw [trMap_zero_fwdMap hW hW0 hr (hSD hz)] at hzf
    exact (hS hz).1 (frontier_subset_closure hzf)
  have hgSO : fwdMap W r '' S ⊆ outerSide Γ := by
    have hcomp := hgSc.subset_connectedComponentIn ⟨p, hpS, rfl⟩ hgSΓ
    intro w hw
    rw [outerSide, connectedComponentIn_eq hpT.2]
    exact hcomp hw
  have hxI := R7GapEqCorner.target_mem_closure_face_image hη hW hW0 hr hΓ hΓH hy hyH rfl
  obtain ⟨q, hqI, hqd⟩ := Metric.mem_closure_iff.1 hxI δ hδ
  have hqS : q ∈ S := hδS ⟨by rwa [mem_ball, dist_comm], hIE hqI⟩
  obtain ⟨w, hw, rfl⟩ := hqI
  have hwO := hgSO ⟨trMap W 0 r w, hqS, rfl⟩
  rw [fwdMap_trMap_zero hW hW0 hr (innerSide_subset_H hΓ hΓH hw)] at hwO
  exact disjoint_innerSide_outerSide.le_bot ⟨hw, hwO⟩

end InteractingSLE.Sec7.R7LocalFace
