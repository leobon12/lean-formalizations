/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7LocalFaceMixed

/-!
# Actual mixed-pocket witnesses and the remaining physical component input

PROVE-R7-GAPEQ. The witnesses are proved for both actual orientations. Full face selection
needs only the named physical assertion that allowed surviving components adhere to the
fresh target. It contains no gate, lift or chosen-arm quantifier.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H fwdHull)
open scoped NNReal

namespace InteractingSLE.Sec7.R7LocalFace

open Sec6 WangWu Lemma71I PocketCoord PocketJordan R7StopIn R7GapEqCorner R7GateBridge R7FaceSelect

/-- **Remaining physical planar input.** Every surviving pocket component with an allowed
point adheres to the fresh target. Other components contained in the forbidden set are
permitted. This statement is not asserted here as a consequence of the source wall data. -/
def AllowedTargetAdherence (W : ℝ → ℝ) (C B : Set ℂ) (x : ℂ) (τ σ : ℝ) : Prop :=
  ∀ s : ℝ, τ ≤ s → s < σ → ∀ z ∈ C ∩ (H \ fwdHull W s), z ∉ B →
    x ∈ closure (connectedComponentIn (C ∩ (H \ fwdHull W s)) z)

/-- **The actual left-outer witnesses are proved**, using the outer wall's own exterior. -/
theorem gate_witnesses_leftOuter {R M L : ℝ≥0 → ℂ} {r : ℝ≥0} {τ σ : ℝ}
    (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r))
    (hO : IsOrderedArcs (realPath R) (realPath M) (realPath L))
    {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hτ0 : 0 ≤ τ) (hτ : η τ = cfArcR R L r 1) (hσ : η σ = cfArcR R L r 0)
    (hxf : cfArcR R L r 0 ∉ η '' Ico 0 σ) (hrev : IsWallReverseVisit R η)
    (havoid : ∀ t, 0 ≤ t → η t ∉ negInv '' leftSideOf (range M)) :
    GateWitnesses W η (cfArcR R L r) (cfArcL R L r) (cfPocket R L r) τ σ := by
  intro s hτs hsσ q₁ q₂ a₁ a₂ ha₁ ha₂
  obtain ⟨hE, hEH, hEb⟩ := left_exterior_props h.left
  apply exists_gate_witness_of_exterior hη hW hW0 (h.isCfPocket h0) hτ0 hτs hsσ hτ hσ hxf
    (cfArcR_rev h h0 hη.1 hrev) ha₁ ha₂ hE hEH hEb ?_
    (left_exterior_disjoint_frontier h h0 hO) (cfArcL_subset_closure_exterior h h0)
  refine Set.disjoint_left.2 ?_
  rintro _ hzE ⟨t, ht, rfl⟩
  exact havoid t ht.1 (left_exterior_subset hO hzE)

/-- **The actual right-outer witnesses are proved**, with the contained left arm first. -/
theorem gate_witnesses_rightOuter {R M L : ℝ≥0 → ℂ} {r : ℝ≥0} {τ σ : ℝ}
    (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r))
    (hO : IsOrderedArcs (realPath R) (realPath M) (realPath L))
    {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hτ0 : 0 ≤ τ) (hτ : η τ = cfArcR R L r 1) (hσ : η σ = cfArcR R L r 0)
    (hxf : cfArcR R L r 0 ∉ η '' Ico 0 σ) (hrev : IsWallReverseVisit L η)
    (havoid : ∀ t, 0 ≤ t → η t ∉ negInv '' rightSideOf (range M)) :
    GateWitnesses W η (cfArcL R L r) (cfArcR R L r) (cfPocket R L r) τ σ := by
  intro s hτs hsσ q₁ q₂ a₁ a₂ ha₁ ha₂
  have hC := h.isCfPocket h0
  have hxf₂ : cfArcL R L r 0 ∉ η '' Ico 0 σ := hC.junction ▸ hxf
  obtain ⟨hE, hEH, hEb⟩ := right_exterior_props h.right
  apply exists_gate_witness_of_exterior hη hW hW0 (cfPocket_swap hC) hτ0 hτs hsσ
    (hτ.trans hC.seed.symm) (hσ.trans hC.junction.symm) hxf₂
    (cfArcL_rev h h0 hη.1 hrev) ha₁ ha₂ hE hEH hEb ?_
    (right_exterior_disjoint_frontier h h0 hO) (cfArcR_subset_closure_exterior h h0)
  refine Set.disjoint_left.2 ?_
  rintro _ hzE ⟨t, ht, rfl⟩
  exact havoid t ht.1 (right_exterior_subset hO hzE)

/-- Full left-outer faces from the remaining physical component-adherence input. -/
theorem gate_faces_leftOuter_of_target_adherence {R M L : ℝ≥0 → ℂ} {r : ℝ≥0} {τ σ : ℝ}
    (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r))
    (hO : IsOrderedArcs (realPath R) (realPath M) (realPath L))
    {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hτ0 : 0 ≤ τ) (hτ : η τ = cfArcR R L r 1) (hσ : η σ = cfArcR R L r 0)
    (hxf : cfArcR R L r 0 ∉ η '' Ico 0 σ) (hrev : IsWallReverseVisit R η)
    (havoid : ∀ t, 0 ≤ t → η t ∉ negInv '' leftSideOf (range M))
    (haccess : AllowedTargetAdherence W (cfPocket R L r) (negInv '' leftSideOf (range M))
      (cfArcR R L r 0) τ σ) :
    ∀ s : ℝ, τ ≤ s → s < σ → ∀ (q₁ q₂ : ℝ) (a₁ a₂ : ℝ → ℂ),
      IsFirstVisitArm W η (cfArcR R L r) s q₁ a₁ → IsFirstVisitArm W η (cfArcL R L r) s q₂ a₂ →
      HasGateFace W (cfPocket R L r) (negInv '' leftSideOf (range M))
        (a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ∪ ofReal '' Icc (min q₁ q₂) (max q₁ q₂)) s := by
  intro s hτs hsσ q₁ q₂ a₁ a₂ ha₁ ha₂
  obtain ⟨hE, hEH, hEb⟩ := left_exterior_props h.left
  apply gate_face_of_exterior_of_target_adherence hη hW hW0 (h.isCfPocket h0) hτ0 hτs hsσ hτ hσ hxf
    (cfArcR_rev h h0 hη.1 hrev) ha₁ ha₂ hE hEH hEb ?_
    (left_exterior_disjoint_frontier h h0 hO) (cfArcL_subset_closure_exterior h h0) (haccess s hτs hsσ)
  refine Set.disjoint_left.2 ?_
  rintro _ hzE ⟨t, ht, rfl⟩
  exact havoid t ht.1 (left_exterior_subset hO hzE)

/-- Full right-outer faces from physical component adherence, retaining right-labeled times. -/
theorem gate_faces_rightOuter_of_target_adherence {R M L : ℝ≥0 → ℂ} {r : ℝ≥0} {τ σ : ℝ}
    (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r))
    (hO : IsOrderedArcs (realPath R) (realPath M) (realPath L))
    {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hτ0 : 0 ≤ τ) (hτ : η τ = cfArcR R L r 1) (hσ : η σ = cfArcR R L r 0)
    (hxf : cfArcR R L r 0 ∉ η '' Ico 0 σ) (hrev : IsWallReverseVisit L η)
    (havoid : ∀ t, 0 ≤ t → η t ∉ negInv '' rightSideOf (range M))
    (haccess : AllowedTargetAdherence W (cfPocket R L r) (negInv '' rightSideOf (range M))
      (cfArcR R L r 0) τ σ) :
    ∀ s : ℝ, τ ≤ s → s < σ → ∀ (q₁ q₂ : ℝ) (a₁ a₂ : ℝ → ℂ),
      IsFirstVisitArm W η (cfArcL R L r) s q₁ a₁ → IsFirstVisitArm W η (cfArcR R L r) s q₂ a₂ →
      HasGateFace W (cfPocket R L r) (negInv '' rightSideOf (range M))
        (a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ∪ ofReal '' Icc (min q₁ q₂) (max q₁ q₂)) s := by
  intro s hτs hsσ q₁ q₂ a₁ a₂ ha₁ ha₂
  have hC := h.isCfPocket h0
  have hxf₂ : cfArcL R L r 0 ∉ η '' Ico 0 σ := hC.junction ▸ hxf
  obtain ⟨hE, hEH, hEb⟩ := right_exterior_props h.right
  apply gate_face_of_exterior_of_target_adherence hη hW hW0 (cfPocket_swap hC) hτ0 hτs hsσ
    (hτ.trans hC.seed.symm) (hσ.trans hC.junction.symm) hxf₂
    (cfArcL_rev h h0 hη.1 hrev) ha₁ ha₂ hE hEH hEb ?_
    (right_exterior_disjoint_frontier h h0 hO) (cfArcR_subset_closure_exterior h h0) ?_
  · refine Set.disjoint_left.2 ?_
    rintro _ hzE ⟨t, ht, rfl⟩
    exact havoid t ht.1 (right_exterior_subset hO hzE)
  · rw [hC.junction]
    exact haccess s hτs hsσ

end InteractingSLE.Sec7.R7LocalFace
