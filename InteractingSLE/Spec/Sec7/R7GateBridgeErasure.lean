/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7GateBridgeChange

/-!
# The finite left-outer relative driver without an assumed physical gap

PROVE-R7-GAPEQ. Compose the new finite physical gap with the landed R.3/R.4 erasure theorem
and the selected-face driver reduction. The geometry is stated on the actual forbidden side
of the certified middle frontier. Contained germ comparisons remain the named input `hAC`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H)
open scoped NNReal

namespace InteractingSLE.Sec7.R7GateBridge

open Sec6 WangWu Lemma71I PocketJordan PocketCoord R7StopIn R7GapEq R7GapEqCorner

/-- **The actual finite left-outer relative driver.** The source R.3 inputs produce erasure
facts after applying the proved physical-gap reduction. Neither `IsErasurePocket`, any gap
equality, a proper-arm witness nor target-face data is assumed. The remaining geometric input
is central-side selection `hfaces`, with the stated global side inclusions. -/
theorem relLoewner_leftOuter_of_faces {R M L : ℝ≥0 → ℂ} {r : ℝ≥0}
    (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r))
    (hM : IsSimpleProper M) (hO : IsOrderedArcs (realPath R) (realPath M) (realPath L))
    (hcR : NoCommonArc M R) (hcL : NoCommonArc M L)
    (houter : range L ⊆ leftSideOf (range M) ∪ range M)
    {W : ℝ → ℝ} {η : ℝ → ℂ} {ψ : ℂ → ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hηH : ∀ t, 0 < t → η t ∈ H)
    (hψ : IsJordanCoord (cfPocket R L r) (cfArcR R L r 0) (cfArcR R L r 1) ψ)
    (havoid : ∀ t, 0 ≤ t → negInv (η t) ∉ leftSideOf (range M))
    (hrevR : IsWallReverseVisit R η) (hvisR : IsWallVisited R η)
    (hrevM : IsWallReverseVisit M η) (hvisM : IsWallVisited M η)
    (h42 : Theorem14.GB10.NoSimpleArcInterval (fun s : ℝ≥0 => η s) ⊤)
    (hAC : BarrierAttachConst η (cfPocket R L r) (cfArcR R L r)
      (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0)))
    (hCr : changePocket R L r ⊆ rightSideOf (range L))
    (hside : negInv '' leftSideOf (range L) ⊆ negInv '' leftSideOf (range M))
    (hfaces : ∀ s : ℝ, firstHit η (cfArcR R L r 1) ≤ s → s < firstHit η (cfArcR R L r 0) →
      ∀ (q₁ q₂ : ℝ) (a₁ a₂ : ℝ → ℂ),
      IsFirstVisitArm W η (cfArcR R L r) s q₁ a₁ → IsFirstVisitArm W η (cfArcL R L r) s q₂ a₂ →
      HasGateFace W (cfPocket R L r) (negInv '' leftSideOf (range M))
        (a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ∪ ofReal '' Icc (min q₁ q₂) (max q₁ q₂)) s) :
    RelLoewner
      (fun v => ψ (erasedPath η (cfPocket R L r)
        (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0)) v))
      (pocketClock η (cfPocket R L r) (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0))
        (firstHit η (cfArcR R L r 0))) := by
  have hC := h.isCfPocket h0
  have havoidB : ∀ t, 0 ≤ t → η t ∉ negInv '' leftSideOf (range M) :=
    fun t ht => notMem_image_negInv (havoid t ht)
  have hgap := pocketGapEq_leftOuter_of_faces h h0 hη hW hW0 hηH hrevR hvisR h42 hAC
    havoidB hCr hside hfaces
  have hP := isErasurePocket_leftOuter h (h.rightLo_pos h0) hM hO hcR hcL houter hη hW hW0
    havoid hrevR hrevM hvisM h42 hAC hgap
  have h42' := no_interval_frontier hC hη.2.1 h42
  have hcollar : ∀ v ∈ Ioo (0 : ℝ) 1,
      HasExteriorCollar (cfPocket R L r) (negInv '' leftSideOf (range M))
        (frontier (cfPocket R L r)) (cfArcL R L r v) :=
    fun _ hv => R7GapEqGeo.hasExteriorCollar_cfArcL h h0 hCr hside Subset.rfl hv
  have hxf₂ : cfArcL R L r 0 ∉ η '' Ico 0 (firstHit η (cfArcR R L r 0)) := by
    rw [hC.junction]; exact hP.fresh_x
  have hAC₂ := barrierAttachConst_of_outerCollars hη.2.1 hC.cont₂ hP.nonneg
    (hP.first_y.trans hC.seed.symm) hxf₂ h42' havoidB hcollar
  exact relLoewner_of_change_gate_faces h h0 hP hη hW hW0 hηH hψ (Or.inl hrevR)
    hAC hAC₂ havoidB hfaces

end InteractingSLE.Sec7.R7GateBridge
