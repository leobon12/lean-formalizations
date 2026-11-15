/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7LocalFaceComponents

/-!
# The mixed-pocket face witness from the actual outer exterior

PROVE-R7-GAPEQ. The outer side adheres to its own untouched exterior at the fresh target.
Its lift lies on the outer chart side. Jordan exterior local connectivity then identifies
the inner face with the pocket side and discharges the former `GateWitnesses` hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H Hbar fwdHull fwdMap)
open InteractingSLE.YuanSimpleApprox (trMap)
open scoped NNReal

namespace InteractingSLE.Sec7.R7LocalFace

open Sec6 PocketJordan R7GapEqCorner R7GateBridge R7FaceSelect

/-- **A mixed face has a physical pocket witness.** The exterior data already used to
exclude surviving outer suffixes also determine which physical side the face occupies. -/
theorem exists_gate_witness_of_exterior
    {W : ℝ → ℝ} {η A₁ A₂ a₁ a₂ : ℝ → ℂ} {C E : Set ℂ} {τ σ r q₁ q₂ : ℝ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hC : IsCfPocket C A₁ A₂) (hτ0 : 0 ≤ τ) (hτr : τ ≤ r) (hrσ : r < σ)
    (hτ : η τ = A₁ 1) (hσ : η σ = A₁ 0) (hxf : A₁ 0 ∉ η '' Ico 0 σ)
    (hrev : R16.IsReverseVisitOrder A₁ fun t => η '' Icc 0 t)
    (ha₁ : IsFirstVisitArm W η A₁ r q₁ a₁) (ha₂ : IsFirstVisitArm W η A₂ r q₂ a₂)
    (hE : IsPreconnected E) (hEH : E ⊆ H) (hEb : ¬ IsBounded E)
    (havoid : Disjoint E (η '' Icc 0 r)) (hEfr : Disjoint E (frontier C))
    (houter : A₂ '' Icc 0 1 ⊆ closure E) :
    ∃ p ∈ innerSide
        (a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ∪ ofReal '' Icc (min q₁ q₂) (max q₁ q₂)),
      trMap W 0 r p ∈ C := by
  have hr := hτ0.trans hτr
  obtain ⟨hu₁, hu₁1, hD₁, -⟩ := firstVisit_prefix_domain hη hW hW0 hC.cont₁ hC.mem_H₁
    hτ0 hτr hrσ hτ hσ hxf
  have hxf₂ : A₂ 0 ∉ η '' Ico 0 σ := hC.junction ▸ hxf
  obtain ⟨-, hu₂1, hD₂, -⟩ := firstVisit_prefix_domain hη hW hW0 hC.cont₂ hC.mem_H₂
    hτ0 hτr hrσ (hτ.trans hC.seed.symm) (hσ.trans hC.junction.symm) hxf₂
  obtain ⟨hΓ, hΓH⟩ := firstVisit_face_jordan hW hr hC hu₁1 hu₂1 hD₁ hD₂ ha₁ ha₂
  have hbd := gate_boundary_mem_frontier hW hW0 hr hC hu₁1 hu₂1 hD₁ hD₂ ha₁ ha₂
  have hfr := gate_face_avoids_frontier_of_exterior hη hW hW0 hC hτ0 hτr hrσ hτ hσ hxf
    hrev ha₁ ha₂ hE hEH hEb havoid hEfr houter
  obtain ⟨hED, hEO⟩ := lift_exterior_subset_outerSide hη hW hW0 hr hΓ hΓH hE hEH hEb havoid
    (fun w hw hwH hzE => Set.disjoint_left.1 hEfr hzE (hbd w hw hwH))
  have hxD := hD₁ 0 ⟨le_rfl, hu₁⟩
  have hyΓ : fwdMap W r (A₁ 0) ∈
      a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ∪ ofReal '' Icc (min q₁ q₂) (max q₁ q₂) :=
    Or.inl (Or.inl ⟨1, ⟨zero_le_one, le_rfl⟩, ha₁.2.2.2.1⟩)
  have hyH := QuantumZipper.FwdHolo.mapsTo_fwdMap hW hr hxD
  have hxfr : A₁ 0 ∈ frontier C := hC.frontier_eq.symm ▸
    Or.inl ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
  have hloc := R7GapEqFin.isLocConnWithin_compl_closure_jordan hC.isOpen hC.isConnected hC.isBounded
    (R7GapEqFin.isJordanCurve_frontier_of_isCfPocket hC) hxfr
  have hxE : A₁ 0 ∈ closure E := hC.junction ▸ houter ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
  have haccess := mem_closure_exterior_access hxE hED
    (exterior_subset_compl_closure hC.isOpen hC.isBounded hE hEb hEfr) hEO
  apply exists_inner_pocket_of_exterior_access hη hW hW0 hr hC.isOpen hΓ hΓH hbd hfr hyΓ hyH
  · rwa [trMap_zero_fwdMap hW hW0 hr hxD]
  · rwa [trMap_zero_fwdMap hW hW0 hr hxD]

/-- **Full mixed face selection from physical target adherence.** Boundary avoidance and
the witness are proved. Only adherence of every allowed surviving component is supplied. -/
theorem gate_face_of_exterior_of_target_adherence
    {W : ℝ → ℝ} {η A₁ A₂ a₁ a₂ : ℝ → ℂ} {C B E : Set ℂ} {τ σ r q₁ q₂ : ℝ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hC : IsCfPocket C A₁ A₂) (hτ0 : 0 ≤ τ) (hτr : τ ≤ r) (hrσ : r < σ)
    (hτ : η τ = A₁ 1) (hσ : η σ = A₁ 0) (hxf : A₁ 0 ∉ η '' Ico 0 σ)
    (hrev : R16.IsReverseVisitOrder A₁ fun t => η '' Icc 0 t)
    (ha₁ : IsFirstVisitArm W η A₁ r q₁ a₁) (ha₂ : IsFirstVisitArm W η A₂ r q₂ a₂)
    (hE : IsPreconnected E) (hEH : E ⊆ H) (hEb : ¬ IsBounded E)
    (havoid : Disjoint E (η '' Icc 0 r)) (hEfr : Disjoint E (frontier C))
    (houter : A₂ '' Icc 0 1 ⊆ closure E)
    (haccess : ∀ z ∈ C ∩ (H \ fwdHull W r), z ∉ B →
      A₁ 0 ∈ closure (connectedComponentIn (C ∩ (H \ fwdHull W r)) z)) :
    HasGateFace W C B
      (a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ∪ ofReal '' Icc (min q₁ q₂) (max q₁ q₂)) r := by
  have hr := hτ0.trans hτr
  obtain ⟨hu₁, hu₁1, hD₁, -⟩ := firstVisit_prefix_domain hη hW hW0 hC.cont₁ hC.mem_H₁
    hτ0 hτr hrσ hτ hσ hxf
  have hxf₂ : A₂ 0 ∉ η '' Ico 0 σ := hC.junction ▸ hxf
  obtain ⟨-, hu₂1, hD₂, -⟩ := firstVisit_prefix_domain hη hW hW0 hC.cont₂ hC.mem_H₂
    hτ0 hτr hrσ (hτ.trans hC.seed.symm) (hσ.trans hC.junction.symm) hxf₂
  obtain ⟨hΓ, hΓH⟩ := firstVisit_face_jordan hW hr hC hu₁1 hu₂1 hD₁ hD₂ ha₁ ha₂
  have hbd := gate_boundary_mem_frontier hW hW0 hr hC hu₁1 hu₂1 hD₁ hD₂ ha₁ ha₂
  have hfr := gate_face_avoids_frontier_of_exterior hη hW hW0 hC hτ0 hτr hrσ hτ hσ hxf
    hrev ha₁ ha₂ hE hEH hEb havoid hEfr houter
  obtain ⟨p, hp, hpC⟩ := exists_gate_witness_of_exterior hη hW hW0 hC hτ0 hτr hrσ hτ hσ hxf
    hrev ha₁ ha₂ hE hEH hEb havoid hEfr houter
  have hbd' : ∀ w ∈
      a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ∪ ofReal '' Icc (min q₁ q₂) (max q₁ q₂),
      w ∈ H → trMap W 0 r w ∉ C := by
    intro w hw hwH hwC
    exact (hC.isOpen.frontier_eq ▸ hbd w hw hwH).2 hwC
  have hxD := hD₁ 0 ⟨le_rfl, hu₁⟩
  have hyΓ : fwdMap W r (A₁ 0) ∈
      a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ∪ ofReal '' Icc (min q₁ q₂) (max q₁ q₂) :=
    Or.inl (Or.inl ⟨1, ⟨zero_le_one, le_rfl⟩, ha₁.2.2.2.1⟩)
  have hxfr : A₁ 0 ∈ frontier C := hC.frontier_eq.symm ▸
    Or.inl ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
  exact ⟨hfr, ⟨p, hp, hpC⟩, gate_bulges_of_target_adherence hη hW hW0 hr hC.isOpen hΓ hΓH
    hfr hbd' hp hpC hyΓ (QuantumZipper.FwdHolo.mapsTo_fwdMap hW hr hxD)
    (trMap_zero_fwdMap hW hW0 hr hxD)
    (isLocConnWithin_pocket hC.isOpen hC.isConnected hC.isBounded
      (R7GapEqFin.isJordanCurve_frontier_of_isCfPocket hC) (frontier_subset_closure hxfr)) haccess⟩

end InteractingSLE.Sec7.R7LocalFace
