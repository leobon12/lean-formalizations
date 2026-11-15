/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7LocalFaceMixed

/-!
# The central gate face of a pocket with two outer arms

Packet PROVE-R7-AUX41OO (Theorem 1.2's R.7, Aux. lemma 41 for pockets with two outer arms).

PROVE-R7-GAPEQ's face lemmas (`R7FaceSelect.gate_face_avoids_frontier_of_exterior`,
`R7LocalFace.exists_gate_witness_of_exterior`, `R7LocalFace.gate_face_of_exterior_of_target_adherence`) need one arm
visited in reverse first-visit order: its visited suffix accounts for the part of the pocket boundary that is not on
the first-visit arm. For a pocket with **two outer arms** (§5.4: "For two outer arms apply this reasoning to both
certified frontiers") neither arm is visited in reverse order, but **each arm adheres to its own exterior**, an
unbounded preconnected set in `ℍ` avoided by the trace and by the pocket frontier. Both exteriors lift to the outer
side of the gate curve (`R7FaceSelect.lift_exterior_subset_outerSide`), and the inner side of the gate curve maps off
both closures (`R7FaceSelect.trMap_inner_not_mem_closure_exterior`). Since the pocket frontier is the union of the two
arms, the inner side avoids the whole frontier. The witness and the forbidden-bulge field then follow as in GAPEQ's
mixed case, from one exterior adherent at the target and from physical target adherence.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H Hbar fwdHull fwdMap)
open InteractingSLE.YuanSimpleApprox (trMap)
open scoped NNReal

namespace InteractingSLE.Sec7.Aux41OO

open Sec6 PocketJordan R7GapEqCorner R7GateBridge R7FaceSelect R7LocalFace

section Faces

variable {W : ℝ → ℝ} {η A₁ A₂ a₁ a₂ : ℝ → ℂ} {C B E₁ E₂ : Set ℂ} {τ σ r q₁ q₂ : ℝ}

/-- **The boundary-avoidance field of a gate face with two outer arms.** Each arm adheres to an unbounded
preconnected exterior in `ℍ` avoided by the trace up to `r` and by the pocket frontier; no reverse visit order is
used. -/
theorem gate_face_avoids_frontier_of_two_exteriors
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hC : IsCfPocket C A₁ A₂) (hτ0 : 0 ≤ τ) (hτr : τ ≤ r) (hrσ : r < σ)
    (hτ : η τ = A₁ 1) (hσ : η σ = A₁ 0) (hxf : A₁ 0 ∉ η '' Ico 0 σ)
    (ha₁ : IsFirstVisitArm W η A₁ r q₁ a₁) (ha₂ : IsFirstVisitArm W η A₂ r q₂ a₂)
    (hE₁ : IsPreconnected E₁) (hE₁H : E₁ ⊆ H) (hE₁b : ¬ IsBounded E₁)
    (havoid₁ : Disjoint E₁ (η '' Icc 0 r)) (hE₁fr : Disjoint E₁ (frontier C))
    (hE₂ : IsPreconnected E₂) (hE₂H : E₂ ⊆ H) (hE₂b : ¬ IsBounded E₂)
    (havoid₂ : Disjoint E₂ (η '' Icc 0 r)) (hE₂fr : Disjoint E₂ (frontier C))
    (houter₁ : A₁ '' Icc 0 1 ⊆ closure E₁) (houter₂ : A₂ '' Icc 0 1 ⊆ closure E₂) :
    ∀ w ∈ innerSide
        (a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ∪ ofReal '' Icc (min q₁ q₂) (max q₁ q₂)),
      trMap W 0 r w ∉ frontier C := by
  have hr := hτ0.trans hτr
  obtain ⟨-, hu₁, hD₁, -⟩ := firstVisit_prefix_domain hη hW hW0 hC.cont₁ hC.mem_H₁
    hτ0 hτr hrσ hτ hσ hxf
  have hxf₂ : A₂ 0 ∉ η '' Ico 0 σ := hC.junction ▸ hxf
  obtain ⟨-, hu₂, hD₂, -⟩ := firstVisit_prefix_domain hη hW hW0 hC.cont₂ hC.mem_H₂
    hτ0 hτr hrσ (hτ.trans hC.seed.symm) (hσ.trans hC.junction.symm) hxf₂
  obtain ⟨hΓ, hΓH⟩ := firstVisit_face_jordan hW hr hC hu₁ hu₂ hD₁ hD₂ ha₁ ha₂
  have hbd := gate_boundary_mem_frontier hW hW0 hr hC hu₁ hu₂ hD₁ hD₂ ha₁ ha₂
  obtain ⟨-, hE₁O⟩ := lift_exterior_subset_outerSide hη hW hW0 hr hΓ hΓH hE₁ hE₁H hE₁b havoid₁
    (fun w hw hwH hzE => Set.disjoint_left.1 hE₁fr hzE (hbd w hw hwH))
  obtain ⟨-, hE₂O⟩ := lift_exterior_subset_outerSide hη hW hW0 hr hΓ hΓH hE₂ hE₂H hE₂b havoid₂
    (fun w hw hwH hzE => Set.disjoint_left.1 hE₂fr hzE (hbd w hw hwH))
  have hcl₁ := trMap_inner_not_mem_closure_exterior hW hW0 hr hΓ hΓH hE₁O
  have hcl₂ := trMap_inner_not_mem_closure_exterior hW hW0 hr hΓ hΓH hE₂O
  intro w hw hfr
  rw [hC.frontier_eq] at hfr
  rcases hfr with hz | hz
  · exact hcl₁ w hw (houter₁ hz)
  · exact hcl₂ w hw (houter₂ hz)

/-- **A gate face with two outer arms has a physical pocket witness** (the first arm's exterior is adherent at the
target `A₁ 0`; the argument is GAPEQ's `exists_gate_witness_of_exterior` with the two-exterior boundary field). -/
theorem exists_gate_witness_of_two_exteriors
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hC : IsCfPocket C A₁ A₂) (hτ0 : 0 ≤ τ) (hτr : τ ≤ r) (hrσ : r < σ)
    (hτ : η τ = A₁ 1) (hσ : η σ = A₁ 0) (hxf : A₁ 0 ∉ η '' Ico 0 σ)
    (ha₁ : IsFirstVisitArm W η A₁ r q₁ a₁) (ha₂ : IsFirstVisitArm W η A₂ r q₂ a₂)
    (hE₁ : IsPreconnected E₁) (hE₁H : E₁ ⊆ H) (hE₁b : ¬ IsBounded E₁)
    (havoid₁ : Disjoint E₁ (η '' Icc 0 r)) (hE₁fr : Disjoint E₁ (frontier C))
    (hE₂ : IsPreconnected E₂) (hE₂H : E₂ ⊆ H) (hE₂b : ¬ IsBounded E₂)
    (havoid₂ : Disjoint E₂ (η '' Icc 0 r)) (hE₂fr : Disjoint E₂ (frontier C))
    (houter₁ : A₁ '' Icc 0 1 ⊆ closure E₁) (houter₂ : A₂ '' Icc 0 1 ⊆ closure E₂) :
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
  have hfr := gate_face_avoids_frontier_of_two_exteriors hη hW hW0 hC hτ0 hτr hrσ hτ hσ hxf
    ha₁ ha₂ hE₁ hE₁H hE₁b havoid₁ hE₁fr hE₂ hE₂H hE₂b havoid₂ hE₂fr houter₁ houter₂
  obtain ⟨hED, hEO⟩ := lift_exterior_subset_outerSide hη hW hW0 hr hΓ hΓH hE₁ hE₁H hE₁b havoid₁
    (fun w hw hwH hzE => Set.disjoint_left.1 hE₁fr hzE (hbd w hw hwH))
  have hxD := hD₁ 0 ⟨le_rfl, hu₁⟩
  have hyΓ : fwdMap W r (A₁ 0) ∈
      a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ∪ ofReal '' Icc (min q₁ q₂) (max q₁ q₂) :=
    Or.inl (Or.inl ⟨1, ⟨zero_le_one, le_rfl⟩, ha₁.2.2.2.1⟩)
  have hyH := QuantumZipper.FwdHolo.mapsTo_fwdMap hW hr hxD
  have hxfr : A₁ 0 ∈ frontier C := hC.frontier_eq.symm ▸
    Or.inl ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
  have hloc := R7GapEqFin.isLocConnWithin_compl_closure_jordan hC.isOpen hC.isConnected hC.isBounded
    (R7GapEqFin.isJordanCurve_frontier_of_isCfPocket hC) hxfr
  have hxE : A₁ 0 ∈ closure E₁ := houter₁ ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
  have haccess := mem_closure_exterior_access hxE hED
    (exterior_subset_compl_closure hC.isOpen hC.isBounded hE₁ hE₁b hE₁fr) hEO
  apply exists_inner_pocket_of_exterior_access hη hW hW0 hr hC.isOpen hΓ hΓH hbd hfr hyΓ hyH
  · rwa [trMap_zero_fwdMap hW hW0 hr hxD]
  · rwa [trMap_zero_fwdMap hW hW0 hr hxD]

/-- **The full central gate face of a pocket with two outer arms**, from the two exteriors and physical adherence of
every allowed surviving component to the target (as `R7LocalFace.gate_face_of_exterior_of_target_adherence`). -/
theorem gate_face_of_two_exteriors_of_target_adherence
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hC : IsCfPocket C A₁ A₂) (hτ0 : 0 ≤ τ) (hτr : τ ≤ r) (hrσ : r < σ)
    (hτ : η τ = A₁ 1) (hσ : η σ = A₁ 0) (hxf : A₁ 0 ∉ η '' Ico 0 σ)
    (ha₁ : IsFirstVisitArm W η A₁ r q₁ a₁) (ha₂ : IsFirstVisitArm W η A₂ r q₂ a₂)
    (hE₁ : IsPreconnected E₁) (hE₁H : E₁ ⊆ H) (hE₁b : ¬ IsBounded E₁)
    (havoid₁ : Disjoint E₁ (η '' Icc 0 r)) (hE₁fr : Disjoint E₁ (frontier C))
    (hE₂ : IsPreconnected E₂) (hE₂H : E₂ ⊆ H) (hE₂b : ¬ IsBounded E₂)
    (havoid₂ : Disjoint E₂ (η '' Icc 0 r)) (hE₂fr : Disjoint E₂ (frontier C))
    (houter₁ : A₁ '' Icc 0 1 ⊆ closure E₁) (houter₂ : A₂ '' Icc 0 1 ⊆ closure E₂)
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
  have hfr := gate_face_avoids_frontier_of_two_exteriors hη hW hW0 hC hτ0 hτr hrσ hτ hσ hxf
    ha₁ ha₂ hE₁ hE₁H hE₁b havoid₁ hE₁fr hE₂ hE₂H hE₂b havoid₂ hE₂fr houter₁ houter₂
  obtain ⟨p, hp, hpC⟩ := exists_gate_witness_of_two_exteriors hη hW hW0 hC hτ0 hτr hrσ hτ hσ hxf
    ha₁ ha₂ hE₁ hE₁H hE₁b havoid₁ hE₁fr hE₂ hE₂H hE₂b havoid₂ hE₂fr houter₁ houter₂
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

end Faces

end InteractingSLE.Sec7.Aux41OO
