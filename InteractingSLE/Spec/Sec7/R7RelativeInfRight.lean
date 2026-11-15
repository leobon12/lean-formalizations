/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7RelativeInfLoewner
import InteractingSLE.Spec.Sec7.R7RelativeInfChart

/-!
# Aux. 41 for the actual infinite right-outer pocket

PROVE-R7-GAPEQ. All relative-driver geometry is discharged by the actual
component charts and mapped gaps. The contained germ comparison remains explicit.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H Hbar)
open InteractingSLE.YuanSimpleApprox (trMap)
open scoped NNReal

namespace InteractingSLE.Sec7.R7RelativeInf

open Sec6 WangWu Lemma71I PocketCoord PocketJordan R7StopIn

variable {R M L : ℝ≥0 → ℂ} {r : ℝ≥0}
variable (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0)
variable (hM : IsSimpleProper M) (hO : IsOrderedArcs (realPath R) (realPath M) (realPath L))
variable (hcR : NoCommonArc M R) (hcL : NoCommonArc M L)
variable (houter : range R ⊆ rightSideOf (range M) ∪ range M)
variable {W : ℝ → ℝ} {η : ℝ → ℂ} {ψ : ℂ → ℂ}
variable (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
variable (hrevL : IsWallReverseVisit L η) (hrevM : IsWallReverseVisit M η)
variable (havoid : ∀ t, 0 ≤ t → negInv (η t) ∉ rightSideOf (range M))
variable (h42 : Theorem14.GB10.NoSimpleArcInterval (fun s : ℝ≥0 => η s) ⊤)

include h h0 hM hO hcR hcL houter hη hW hW0 hrevL hrevM havoid h42

/-- The actual selected right-outer faces and mapped gaps prove the relative
driver conclusion for any entrance erasure satisfying the contained comparison. -/
theorem relLoewner_rightOuter_of_erasure {τ : ℝ}
    (hAC : BarrierAttachConstInf η (cfPocket R L r) (cfArcLInf R L r) τ)
    (hP : IsErasurePocketInf η (cfPocket R L r) (cfArcRInf R L r 0) τ)
    (hψ : IsJordanCoordInf (cfPocket R L r) (cfArcRInf R L r 0) ψ) :
    RelLoewner (fun v => ψ (erasedPathInf η (cfPocket R L r) τ v))
      (clockEnd η (cfPocket R L r) τ) := by
  have hτ0 := hP.nonneg
  have hτ := hP.first_y
  have hallowed := R7EndFace.allowedUnboundedComponents_rightOuter h h0 hM hO hcR hcL
    houter hη hW hW0 hτ0 hτ hrevL hrevM
  apply relLoewner_of_compact_charts hP hη hW hW0 (h.isCfPocketInf h0).subset_H hψ
  · intro s a b hτs hsa hab hgap ha hb
    exact (R7InfinityGap.gap_eq_rightOuter h h0 hM hO hcR hcL houter hη hW hW0
      hτ0 hτ hrevL hrevM havoid h42 hAC hτs hsa hab hgap ha hb).1
  · intro s hτs B
    obtain ⟨p, hp, Γ, q, hchart⟩ := exists_chart_below_rightOuter h h0 hO hη hW hW0
      hτ0 hτ hrevL havoid s hτs B
    refine ⟨p, hp, Γ, q, hchart, ?_⟩
    exact R7EndFace.ownFuture_mem_infinite_face h h0 hη hW hW0 (hτ0.trans hτs)
      hτs hallowed hchart (fun t ht => notMem_image_negInv (havoid t ((hτ0.trans hτs).trans ht)))

/-- Aux. 41's actual right-outer driver and strict capacity clock, with only the
contained attachment comparison left among the pocket geometry inputs. -/
theorem relLoewner_rightOuter_of_containedAttach (hvisL : IsWallVisited L η)
    (hAC : BarrierAttachConstInf η (cfPocket R L r) (cfArcLInf R L r)
      (firstHit η (cfArcRInf R L r 0)))
    (hψ : IsJordanCoordInf (cfPocket R L r) (cfArcRInf R L r 0) ψ) :
    RelLoewner (fun v => ψ (erasedPathInf η (cfPocket R L r)
      (firstHit η (cfArcRInf R L r 0)) v))
      (clockEnd η (cfPocket R L r) (firstHit η (cfArcRInf R L r 0))) := by
  have hP := R7InfinityGap.isErasurePocketInf_rightOuter_of_containedAttach
    h h0 hM hO hcR hcL houter hη hW hW0 hrevL hvisL hrevM havoid h42 hAC
  exact relLoewner_rightOuter_of_erasure h h0 hM hO hcR hcL houter hη hW hW0
    hrevL hrevM havoid h42 hAC hP hψ

end InteractingSLE.Sec7.R7RelativeInf
