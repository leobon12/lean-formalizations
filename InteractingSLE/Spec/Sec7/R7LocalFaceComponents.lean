/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7LocalFaceWitness

/-!
# A surviving component adhering to the fresh target is unique

PROVE-R7-GAPEQ. Local connectivity of the Jordan pocket at a point in the ambient domain
gives uniqueness of a component adhering there. Thus forbidden-bulge confinement reduces
to a physical target-adherence statement with no quantification over lifted arm choices.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H Hbar fwdHull fwdMap)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Sec7.R7LocalFace

open Sec6 R7GapEqCorner

/-- Two components of `C ∩ D` adhering to a point of the open set `D` coincide when
`C` is locally connected from within at that point. -/
theorem component_eq_of_common_adherent {C D : Set ℂ} {x p q : ℂ}
    (hDo : IsOpen D) (hxD : x ∈ D) (hloc : IsLocConnWithin C x)
    (hxP : x ∈ closure (connectedComponentIn (C ∩ D) p))
    (hxQ : x ∈ closure (connectedComponentIn (C ∩ D) q)) :
    connectedComponentIn (C ∩ D) p = connectedComponentIn (C ∩ D) q := by
  obtain ⟨ε, hε, hεD⟩ := Metric.isOpen_iff.1 hDo x hxD
  obtain ⟨S, hS, hSc, hSN⟩ := hloc ε hε
  obtain ⟨δ, hδ, hδS⟩ := Metric.mem_nhdsWithin_iff.1 hSN
  obtain ⟨p', hp'P, hp'd⟩ := Metric.mem_closure_iff.1 hxP δ hδ
  obtain ⟨q', hq'Q, hq'd⟩ := Metric.mem_closure_iff.1 hxQ δ hδ
  have hp'S : p' ∈ S := hδS ⟨by rwa [mem_ball, dist_comm],
    (connectedComponentIn_subset _ _ hp'P).1⟩
  have hq'S : q' ∈ S := hδS ⟨by rwa [mem_ball, dist_comm],
    (connectedComponentIn_subset _ _ hq'Q).1⟩
  have hSsub : S ⊆ C ∩ D := fun _ hz => ⟨(hS hz).1, hεD (hS hz).2⟩
  have hq'P : q' ∈ connectedComponentIn (C ∩ D) p := by
    rw [connectedComponentIn_eq hp'P]
    exact hSc.subset_connectedComponentIn hp'S hSsub hq'S
  exact (connectedComponentIn_eq hq'P).trans (connectedComponentIn_eq hq'Q).symm

/-- The existing Jordan-domain local-connectivity theorem applies directly to a bounded
open connected pocket with Jordan frontier. -/
theorem isLocConnWithin_pocket {C : Set ℂ} (hCo : IsOpen C) (hCc : IsConnected C)
    (hCb : IsBounded C) (hCJ : LQGMetric.JordanMap.IsJordanCurve (frontier C))
    {x : ℂ} (hx : x ∈ closure C) : IsLocConnWithin C x := by
  obtain ⟨p, hp⟩ := hCc.nonempty
  have hCeq := connectedComponentIn_compl_frontier_eq hCo hCc hp
  have hpfr : p ∈ (frontier C)ᶜ := by
    rw [hCo.frontier_eq]
    exact fun h => h.2 hp
  have hb : IsBounded (connectedComponentIn (frontier C)ᶜ p) := hCeq.symm ▸ hCb
  have hx' : x ∈ closure (connectedComponentIn (frontier C)ᶜ p) := hCeq.symm ▸ hx
  simpa only [hCeq] using isLocConnWithin_of_jordan hCJ hpfr hb hx'

/-- **Bulges from physical target adherence.** If every allowed surviving pocket point
has a component adhering to the fresh target, it belongs to the selected face component.
All other pocket preimages therefore lie in the forbidden set. -/
theorem gate_bulges_of_target_adherence {W : ℝ → ℝ} {η : ℝ → ℂ} {r : ℝ}
    {C B Γ : Set ℂ} (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hr : 0 ≤ r) (hCo : IsOpen C) (hΓ : LQGMetric.JordanMap.IsJordanCurve Γ)
    (hΓH : Γ ⊆ Hbar) (hfr : ∀ w ∈ innerSide Γ, trMap W 0 r w ∉ frontier C)
    (hbd : ∀ w ∈ Γ, w ∈ H → trMap W 0 r w ∉ C)
    {p : ℂ} (hp : p ∈ innerSide Γ) (hpC : trMap W 0 r p ∈ C)
    {y x : ℂ} (hy : y ∈ Γ) (hyH : y ∈ H) (hyx : trMap W 0 r y = x)
    (hloc : IsLocConnWithin C x)
    (haccess : ∀ z ∈ C ∩ (H \ fwdHull W r), z ∉ B →
      x ∈ closure (connectedComponentIn (C ∩ (H \ fwdHull W r)) z)) :
    ∀ w ∈ H, trMap W 0 r w ∈ C → w ∉ innerSide Γ → trMap W 0 r w ∈ B := by
  obtain ⟨-, himage⟩ := image_innerSide_eq_component hη hW hW0 hr hCo hΓ hΓH hfr hbd hp hpC
  have hxP := target_mem_closure_face_image hη hW hW0 hr hΓ hΓH hy hyH hyx
  rw [himage] at hxP
  have hxD : x ∈ H \ fwdHull W r := hyx ▸ trMap_zero_mem_domain hW hW0 hr hyH
  intro w hw hwC hwn
  by_contra hwB
  have hwD := trMap_zero_mem_domain hW hW0 hr hw
  have he := component_eq_of_common_adherent (QuantumZipper.FwdHolo.isOpen_compl_fwdHull hW hr)
    hxD hloc hxP (haccess _ ⟨hwC, hwD⟩ hwB)
  have hwcomp : trMap W 0 r w ∈
      connectedComponentIn (C ∩ (H \ fwdHull W r)) (trMap W 0 r p) := by
    rw [he]
    exact mem_connectedComponentIn ⟨hwC, hwD⟩
  rw [← himage] at hwcomp
  obtain ⟨v, hv, hvw⟩ := hwcomp
  have hev : v = w := by
    have he' := congrArg (fwdMap W r) hvw
    rwa [fwdMap_trMap_zero hW hW0 hr (innerSide_subset_H hΓ hΓH hv),
      fwdMap_trMap_zero hW hW0 hr hw] at he'
  exact hwn (hev ▸ hv)

/-- Conversely, the old bulge condition implies physical target adherence. Thus the new
physical remaining input does not strengthen that condition in a selected Jordan face. -/
theorem target_adherence_of_gate_bulges {W : ℝ → ℝ} {η : ℝ → ℂ} {r : ℝ}
    {C B Γ : Set ℂ} (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hr : 0 ≤ r) (hCo : IsOpen C) (hΓ : LQGMetric.JordanMap.IsJordanCurve Γ)
    (hΓH : Γ ⊆ Hbar) (hfr : ∀ w ∈ innerSide Γ, trMap W 0 r w ∉ frontier C)
    (hbd : ∀ w ∈ Γ, w ∈ H → trMap W 0 r w ∉ C)
    {p : ℂ} (hp : p ∈ innerSide Γ) (hpC : trMap W 0 r p ∈ C)
    {y x : ℂ} (hy : y ∈ Γ) (hyH : y ∈ H) (hyx : trMap W 0 r y = x)
    (hbulges : ∀ w ∈ H, trMap W 0 r w ∈ C → w ∉ innerSide Γ → trMap W 0 r w ∈ B) :
    ∀ z ∈ C ∩ (H \ fwdHull W r), z ∉ B →
      x ∈ closure (connectedComponentIn (C ∩ (H \ fwdHull W r)) z) := by
  obtain ⟨-, himage⟩ := image_innerSide_eq_component hη hW hW0 hr hCo hΓ hΓH hfr hbd hp hpC
  have hxP := target_mem_closure_face_image hη hW hW0 hr hΓ hΓH hy hyH hyx
  rw [himage] at hxP
  intro z hz hzB
  have hgH := QuantumZipper.FwdHolo.mapsTo_fwdMap hW hr hz.2
  have hgI : fwdMap W r z ∈ innerSide Γ := by
    by_contra hn
    have hc : trMap W 0 r (fwdMap W r z) ∈ C :=
      (trMap_zero_fwdMap hW hW0 hr hz.2).symm ▸ hz.1
    have hb := hbulges _ hgH hc hn
    rw [trMap_zero_fwdMap hW hW0 hr hz.2] at hb
    exact hzB hb
  have hzP : z ∈ connectedComponentIn (C ∩ (H \ fwdHull W r)) (trMap W 0 r p) := by
    rw [← himage]
    exact ⟨fwdMap W r z, hgI, trMap_zero_fwdMap hW hW0 hr hz.2⟩
  rwa [connectedComponentIn_eq hzP] at hxP

end InteractingSLE.Sec7.R7LocalFace
