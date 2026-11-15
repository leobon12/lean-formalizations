/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7FaceSelectWalls

/-!
# Central-face selection reduced to a witness and forbidden bulges

PROVE-R7-GAPEQ. These two named propositions are the remaining planar inputs. The third
former input, absence of extra pocket boundary inside the face, is proved from the actual
outer exterior. Contained attachment/germ comparisons are not changed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H)
open InteractingSLE.YuanSimpleApprox (trMap)
open scoped NNReal

namespace InteractingSLE.Sec7.R7FaceSelect

open Sec6 WangWu Lemma71I PocketCoord PocketJordan R7StopIn R7GapEqCorner R7GateBridge

/-- **Remaining planar witness input.** Every current incoming-arm face contains a point
of the physical pocket. This is not inferred from the existence of prime-end lifts. -/
def GateWitnesses (W : ℝ → ℝ) (η A₁ A₂ : ℝ → ℂ) (C : Set ℂ) (τ σ : ℝ) : Prop :=
  ∀ s : ℝ, τ ≤ s → s < σ → ∀ (q₁ q₂ : ℝ) (a₁ a₂ : ℝ → ℂ),
    IsFirstVisitArm W η A₁ s q₁ a₁ → IsFirstVisitArm W η A₂ s q₂ a₂ →
    ∃ p ∈ innerSide
      (a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ∪ ofReal '' Icc (min q₁ q₂) (max q₁ q₂)),
      trMap W 0 s p ∈ C

/-- **Remaining planar confinement input.** All surviving pocket preimages outside the
selected face lie in the certified forbidden side. Other surviving pocket components are
allowed, so connectedness of all `C ∩ D_s` is not assumed. -/
def GateBulges (W : ℝ → ℝ) (η A₁ A₂ : ℝ → ℂ) (C B : Set ℂ) (τ σ : ℝ) : Prop :=
  ∀ s : ℝ, τ ≤ s → s < σ → ∀ (q₁ q₂ : ℝ) (a₁ a₂ : ℝ → ℂ),
    IsFirstVisitArm W η A₁ s q₁ a₁ → IsFirstVisitArm W η A₂ s q₂ a₂ →
    ∀ w ∈ H, trMap W 0 s w ∈ C →
      w ∉ innerSide
        (a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ∪ ofReal '' Icc (min q₁ q₂) (max q₁ q₂)) →
      trMap W 0 s w ∈ B

/-- **Left outer face selection.** Global order, reverse visits of the contained right wall
and avoidance of the certified left exterior discharge the boundary-avoidance field. -/
theorem gate_faces_leftOuter {R M L : ℝ≥0 → ℂ} {r : ℝ≥0} {τ σ : ℝ}
    (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r))
    (hO : IsOrderedArcs (realPath R) (realPath M) (realPath L))
    {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hτ0 : 0 ≤ τ) (hτ : η τ = cfArcR R L r 1) (hσ : η σ = cfArcR R L r 0)
    (hxf : cfArcR R L r 0 ∉ η '' Ico 0 σ) (hrev : IsWallReverseVisit R η)
    (havoid : ∀ t, 0 ≤ t → η t ∉ negInv '' leftSideOf (range M))
    (hwitness : GateWitnesses W η (cfArcR R L r) (cfArcL R L r) (cfPocket R L r) τ σ)
    (hbulges : GateBulges W η (cfArcR R L r) (cfArcL R L r)
      (cfPocket R L r) (negInv '' leftSideOf (range M)) τ σ) :
    ∀ s : ℝ, τ ≤ s → s < σ → ∀ (q₁ q₂ : ℝ) (a₁ a₂ : ℝ → ℂ),
      IsFirstVisitArm W η (cfArcR R L r) s q₁ a₁ → IsFirstVisitArm W η (cfArcL R L r) s q₂ a₂ →
      HasGateFace W (cfPocket R L r) (negInv '' leftSideOf (range M))
        (a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ∪ ofReal '' Icc (min q₁ q₂) (max q₁ q₂)) s := by
  intro s hτs hsσ q₁ q₂ a₁ a₂ ha₁ ha₂
  obtain ⟨hE, hEH, hEb⟩ := left_exterior_props h.left
  refine ⟨gate_face_avoids_frontier_of_exterior hη hW hW0 (h.isCfPocket h0)
    hτ0 hτs hsσ hτ hσ hxf (cfArcR_rev h h0 hη.1 hrev) ha₁ ha₂ hE hEH hEb ?_
    (left_exterior_disjoint_frontier h h0 hO) (cfArcL_subset_closure_exterior h h0),
    hwitness s hτs hsσ q₁ q₂ a₁ a₂ ha₁ ha₂, hbulges s hτs hsσ q₁ q₂ a₁ a₂ ha₁ ha₂⟩
  refine Set.disjoint_left.2 ?_
  rintro _ hzE ⟨t, ht, rfl⟩
  exact havoid t ht.1 (left_exterior_subset hO hzE)

/-- **Right outer face selection.** The contained left wall is listed first. The two
remaining named inputs have the same types after swapping the wall labels. -/
theorem gate_faces_rightOuter {R M L : ℝ≥0 → ℂ} {r : ℝ≥0} {τ σ : ℝ}
    (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r))
    (hO : IsOrderedArcs (realPath R) (realPath M) (realPath L))
    {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hτ0 : 0 ≤ τ) (hτ : η τ = cfArcR R L r 1) (hσ : η σ = cfArcR R L r 0)
    (hxf : cfArcR R L r 0 ∉ η '' Ico 0 σ) (hrev : IsWallReverseVisit L η)
    (havoid : ∀ t, 0 ≤ t → η t ∉ negInv '' rightSideOf (range M))
    (hwitness : GateWitnesses W η (cfArcL R L r) (cfArcR R L r) (cfPocket R L r) τ σ)
    (hbulges : GateBulges W η (cfArcL R L r) (cfArcR R L r)
      (cfPocket R L r) (negInv '' rightSideOf (range M)) τ σ) :
    ∀ s : ℝ, τ ≤ s → s < σ → ∀ (q₁ q₂ : ℝ) (a₁ a₂ : ℝ → ℂ),
      IsFirstVisitArm W η (cfArcL R L r) s q₁ a₁ → IsFirstVisitArm W η (cfArcR R L r) s q₂ a₂ →
      HasGateFace W (cfPocket R L r) (negInv '' rightSideOf (range M))
        (a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ∪ ofReal '' Icc (min q₁ q₂) (max q₁ q₂)) s := by
  intro s hτs hsσ q₁ q₂ a₁ a₂ ha₁ ha₂
  have hC := h.isCfPocket h0
  have hxf₂ : cfArcL R L r 0 ∉ η '' Ico 0 σ := hC.junction ▸ hxf
  obtain ⟨hE, hEH, hEb⟩ := right_exterior_props h.right
  refine ⟨gate_face_avoids_frontier_of_exterior hη hW hW0 (cfPocket_swap hC)
    hτ0 hτs hsσ (hτ.trans hC.seed.symm) (hσ.trans hC.junction.symm) hxf₂
    (cfArcL_rev h h0 hη.1 hrev) ha₁ ha₂ hE hEH hEb ?_
    (right_exterior_disjoint_frontier h h0 hO) (cfArcR_subset_closure_exterior h h0),
    hwitness s hτs hsσ q₁ q₂ a₁ a₂ ha₁ ha₂, hbulges s hτs hsσ q₁ q₂ a₁ a₂ ha₁ ha₂⟩
  refine Set.disjoint_left.2 ?_
  rintro _ hzE ⟨t, ht, rfl⟩
  exact havoid t ht.1 (right_exterior_subset hO hzE)

end InteractingSLE.Sec7.R7FaceSelect
