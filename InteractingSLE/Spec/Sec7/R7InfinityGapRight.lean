/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7InfinityGapActual

/-!
# Equal physical and mapped gaps of the actual infinite right-outer pocket

PROVE-R7-GAPEQ. The contained left arm is first in the compact boundary.
The entrance time still refers to the common right-arm seed.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open QuantumZipper (H)
open InteractingSLE.YuanSimpleApprox (trMap)
open scoped NNReal

namespace InteractingSLE.Sec7.R7InfinityGap

open Sec6 WangWu Lemma71I PocketCoord PocketJordan R7StopIn R7InfinityAccess

variable {R M L : ℝ≥0 → ℂ} {r : ℝ≥0} {τ : ℝ}
variable (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0)
variable (hM : IsSimpleProper M) (hO : IsOrderedArcs (realPath R) (realPath M) (realPath L))
variable (hcR : NoCommonArc M R) (hcL : NoCommonArc M L)
variable (houter : range R ⊆ rightSideOf (range M) ∪ range M)
variable {W : ℝ → ℝ} {η : ℝ → ℂ}
variable (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
variable (hτ0 : 0 ≤ τ) (hτ : η τ = cfArcRInf R L r 0)
variable (hrevL : IsWallReverseVisit L η) (hrevM : IsWallReverseVisit M η)
variable (havoid : ∀ t, 0 ≤ t → negInv (η t) ∉ rightSideOf (range M))
variable (h42 : Theorem14.GB10.NoSimpleArcInterval (fun s : ℝ≥0 => η s) ⊤)
variable (hAC : BarrierAttachConstInf η (cfPocket R L r) (cfArcLInf R L r) τ)

include h h0 hM hO hcR hcL houter hη hW hW0 hτ0 hτ hrevL hrevM havoid h42 hAC

/-- Every actual right-outer gap has equal endpoint values in each earlier chart,
including an old shared entrance-corner start. -/
theorem gap_eq_rightOuter {s a b : ℝ} (hτs : τ ≤ s) (hsa : s < a) (hab : a < b)
    (hgap : ∀ t ∈ Icc a b, η t ∉ cfPocket R L r)
    (ha : a ∈ closure {t | τ < t ∧ η t ∈ cfPocket R L r})
    (hb : b ∈ closure {t | a < t ∧ η t ∈ cfPocket R L r}) :
    trMap W s a 0 = trMap W s b 0 ∧ η a = η b := by
  have hC := h.isCfPocketInf h0
  obtain ⟨hrev, hK, hcollars⟩ := gap_data_rightOuter h h0 hO hη hrevL h42
  exact gap_eq_of_selected_faces (cfPocketInf_swap hC) hη hW hW0 hτ0
    (hτ.trans hC.seed.symm) hrev hAC hK
    (fun t ht => notMem_image_negInv (havoid t ht)) hcollars
    (current_faces_rightOuter h h0 hM hO hcR hcL houter hη hW hW0 hτ0 hτ hrevL hrevM havoid)
    hτs hsa hab hgap ha hb

/-- The physical infinite-gap predicate for the actual right-outer pocket, from
the named contained-arm comparison and the source wall/trace hypotheses. -/
theorem pocketGapEqInf_rightOuter (hτf : η τ ∉ η '' Ico 0 τ) :
    PocketGapEqInf η (cfPocket R L r) τ := by
  have hC := h.isCfPocketInf h0
  obtain ⟨hrev, hK, hcollars⟩ := gap_data_rightOuter h h0 hO hη hrevL h42
  exact pocketGapEqInf_of_selected_faces (cfPocketInf_swap hC) hη hW hW0 hτ0
    (hτ.trans hC.seed.symm) hrev hAC hK
    (fun t ht => notMem_image_negInv (havoid t ht)) hcollars
    (current_faces_rightOuter h h0 hM hO hcR hcL houter hη hW hW0 hτ0 hτ hrevL hrevM havoid) hτf

end InteractingSLE.Sec7.R7InfinityGap
