/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7InfinityGapActual

/-!
# Equal physical and mapped gaps of the actual infinite left-outer pocket

PROVE-R7-GAPEQ. The contained attachment comparison is the sole remaining
germ premise; collars and the selected compact faces are proved inputs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology
open QuantumZipper (H)
open InteractingSLE.YuanSimpleApprox (trMap)
open scoped NNReal

namespace InteractingSLE.Sec7.R7InfinityGap

open Sec6 WangWu Lemma71I PocketCoord PocketJordan R7StopIn

variable {R M L : ℝ≥0 → ℂ} {r : ℝ≥0} {τ : ℝ}
variable (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0)
variable (hM : IsSimpleProper M) (hO : IsOrderedArcs (realPath R) (realPath M) (realPath L))
variable (hcR : NoCommonArc M R) (hcL : NoCommonArc M L)
variable (houter : range L ⊆ leftSideOf (range M) ∪ range M)
variable {W : ℝ → ℝ} {η : ℝ → ℂ}
variable (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
variable (hτ0 : 0 ≤ τ) (hτ : η τ = cfArcRInf R L r 0)
variable (hrevR : IsWallReverseVisit R η) (hrevM : IsWallReverseVisit M η)
variable (havoid : ∀ t, 0 ≤ t → negInv (η t) ∉ leftSideOf (range M))
variable (h42 : Theorem14.GB10.NoSimpleArcInterval (fun s : ℝ≥0 => η s) ⊤)
variable (hAC : BarrierAttachConstInf η (cfPocket R L r) (cfArcRInf R L r) τ)

include h h0 hM hO hcR hcL houter hη hW hW0 hτ0 hτ hrevR hrevM havoid h42 hAC

/-- Every actual left-outer gap has equal endpoint values in each earlier chart,
including an old shared entrance-corner start. -/
theorem gap_eq_leftOuter {s a b : ℝ} (hτs : τ ≤ s) (hsa : s < a) (hab : a < b)
    (hgap : ∀ t ∈ Icc a b, η t ∉ cfPocket R L r)
    (ha : a ∈ closure {t | τ < t ∧ η t ∈ cfPocket R L r})
    (hb : b ∈ closure {t | a < t ∧ η t ∈ cfPocket R L r}) :
    trMap W s a 0 = trMap W s b 0 ∧ η a = η b := by
  obtain ⟨hrev, hK, hcollars⟩ := gap_data_leftOuter h h0 hO hη hrevR h42
  exact gap_eq_of_selected_faces (h.isCfPocketInf h0) hη hW hW0 hτ0 hτ hrev hAC hK
    (fun t ht => notMem_image_negInv (havoid t ht)) hcollars
    (current_faces_leftOuter h h0 hM hO hcR hcL houter hη hW hW0 hτ0 hτ hrevR hrevM havoid)
    hτs hsa hab hgap ha hb

/-- The physical infinite-gap predicate for the actual left-outer pocket, from
the named contained-arm comparison and the source wall/trace hypotheses. -/
theorem pocketGapEqInf_leftOuter (hτf : η τ ∉ η '' Ico 0 τ) :
    PocketGapEqInf η (cfPocket R L r) τ := by
  obtain ⟨hrev, hK, hcollars⟩ := gap_data_leftOuter h h0 hO hη hrevR h42
  exact pocketGapEqInf_of_selected_faces (h.isCfPocketInf h0) hη hW hW0 hτ0 hτ hrev hAC hK
    (fun t ht => notMem_image_negInv (havoid t ht)) hcollars
    (current_faces_leftOuter h h0 hM hO hcR hcL houter hη hW hW0 hτ0 hτ hrevR hrevM havoid) hτf

end InteractingSLE.Sec7.R7InfinityGap
