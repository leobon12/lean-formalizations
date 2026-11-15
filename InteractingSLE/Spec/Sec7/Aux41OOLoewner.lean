/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux41OOProper
import InteractingSLE.Spec.Sec7.Aux41OOFaces
import InteractingSLE.Spec.Sec7.Aux41OOAdherence
import InteractingSLE.Spec.Sec7.OuterGeomAttach

/-!
# Aux. lemma 41 for a bounded pocket with two outer arms

Packet PROVE-R7-AUX41OO (Theorem 1.2's R.7). The relative driver of a bounded R.7 pocket whose two arms `α_R`, `α_L`
are both outer (`θ_R < −π/2`, `θ_L > π/2`), with the certified frontiers `M₁ = β_R`, `M₂ = β_L` between them.

PROVE-R7-GAPEQ's driver reduction `R7GateBridge.relLoewner_of_change_gate_faces` uses one reverse-visited wall only to
build the proper earlier arm; its version with the proper arm as an argument is `relLoewner_of_proper_gate_faces`
(same proof). The inputs are then all proved here for two outer arms:

* the erasure (`R7StopIn.isErasurePocket_outerOuter`, with Aux. 37 along the clipped `β_R` from
  `OuterGeom.outerOuterAttach` and §5.4's gap equality from `OuterIn.pocketGapEq_outerOuter`);
* attachment constancy along both outer arms (`R7GapEqCorner.barrierAttachConst_of_outerCollars` with the exterior
  collars `R7GapEqGeo.hasExteriorCollar_cfArc{R,L}`; §5.4: "In particular no new outer attachment can occur on a
  positive no-`C` interval");
* the proper earlier arm through `β_R` (`hasProperEarlierArm_middle`);
* the central gate face (`gate_face_of_two_exteriors_of_target_adherence`, with the walls' own exteriors and physical
  target adherence through both clipped certified frontiers, `allowedTargetAdherence_outerOuter`).

**`relLoewner_outerOuter`** is Aux. 41's conclusion from the pathwise configuration; **`outerRelLoewner_outerOuter`**
is `OuterIn.OuterRelLoewner`, the field `relOuterOuter` of `OuterGeom.OuterGeomRest`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H)
open InteractingSLE.YuanSimpleApprox (trMap)
open scoped NNReal

namespace InteractingSLE.Sec7.Aux41OO

open Sec6 WangWu Lemma71I PocketJordan PocketCoord R7StopIn R7GapEqCorner R7GateBridge R7FaceSelect R7LocalFace

section Reduction

variable {R L : ℝ≥0 → ℂ} {r : ℝ≥0} {W : ℝ → ℝ} {η : ℝ → ℂ} {B : Set ℂ} {τ σ : ℝ}

/-- **Mapped gaps from a proper earlier arm** (`R7GateBridge.mapped_gaps_of_change_faces` with the proper arm as an
argument instead of a reverse-visited wall). -/
theorem mapped_gaps_of_proper_faces
    (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r))
    (hP : IsErasurePocket η (cfPocket R L r) (cfArcR R L r 0) (cfArcR R L r 1) τ σ)
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hηH : ∀ t, 0 < t → η t ∈ H)
    (hproper : HasProperEarlierArm η (cfArcR R L r) (cfArcL R L r) σ)
    (hAC₁ : BarrierAttachConst η (cfPocket R L r) (cfArcR R L r) τ σ)
    (hAC₂ : BarrierAttachConst η (cfPocket R L r) (cfArcL R L r) τ σ)
    (havoid : ∀ t, 0 ≤ t → η t ∉ B)
    (hfaces : ∀ s : ℝ, τ ≤ s → s < σ → ∀ (q₁ q₂ : ℝ) (a₁ a₂ : ℝ → ℂ),
      IsFirstVisitArm W η (cfArcR R L r) s q₁ a₁ → IsFirstVisitArm W η (cfArcL R L r) s q₂ a₂ →
      HasGateFace W (cfPocket R L r) B
        (a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ∪ ofReal '' Icc (min q₁ q₂) (max q₁ q₂)) s) :
    ∀ s ∈ Ico τ σ, ∀ a b : ℝ, s < a → a < b → b < σ →
      (∀ t ∈ Icc a b, η t ∉ cfPocket R L r) →
      a ∈ closure {t | s < t ∧ η t ∈ cfPocket R L r} →
      b ∈ closure {t | a < t ∧ η t ∈ cfPocket R L r} → trMap W s a 0 = trMap W s b 0 := by
  have hC := h.isCfPocket h0
  apply R7GapEqGeo.mapped_gap_eq_of_old_access hP hη hW hW0 hηH
  intro s hs a b hsa hab hbσ hgap ha hb hold
  have hold' : η a ∈ η '' Ico 0 a := image_mono
    (show Icc (0 : ℝ) s ⊆ Ico 0 a from fun _ ht => ⟨ht.1, ht.2.trans_lt hsa⟩) hold
  exact (gap_eq_at_old_start hη hW hW0 hC.isOpen hC.cont₁ hC.cont₂ hC.inj₁ hC.inj₂ hC.mem_H₁ hC.mem_H₂
    hP.nonneg hs.1 hsa hab hbσ hP.first_y (hP.first_y.trans hC.seed.symm)
    hP.first_x (hP.first_x.trans hC.junction.symm) hP.fresh_x
    (fun _ hv _ hw => cfPocket_arms_eq hC hv hw)
    (hC.frontier_eq.symm ▸ subset_union_left) (hC.frontier_eq.symm ▸ subset_union_right)
    hAC₁ hAC₂ havoid hfaces hproper hgap ha hb hold').1

/-- **The relative Loewner evolution from a proper earlier arm and the central-face selection**
(`R7GateBridge.relLoewner_of_change_gate_faces` with the proper arm as an argument). -/
theorem relLoewner_of_proper_gate_faces {ψ : ℂ → ℂ}
    (h : IsChangeConfigInc R L r) (h0 : (0 : ℂ) ∉ closure (changePocket R L r))
    (hP : IsErasurePocket η (cfPocket R L r) (cfArcR R L r 0) (cfArcR R L r 1) τ σ)
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hηH : ∀ t, 0 < t → η t ∈ H)
    (hψ : IsJordanCoord (cfPocket R L r) (cfArcR R L r 0) (cfArcR R L r 1) ψ)
    (hproper : HasProperEarlierArm η (cfArcR R L r) (cfArcL R L r) σ)
    (hAC₁ : BarrierAttachConst η (cfPocket R L r) (cfArcR R L r) τ σ)
    (hAC₂ : BarrierAttachConst η (cfPocket R L r) (cfArcL R L r) τ σ)
    (havoid : ∀ t, 0 ≤ t → η t ∉ B)
    (hfaces : ∀ s : ℝ, τ ≤ s → s < σ → ∀ (q₁ q₂ : ℝ) (a₁ a₂ : ℝ → ℂ),
      IsFirstVisitArm W η (cfArcR R L r) s q₁ a₁ → IsFirstVisitArm W η (cfArcL R L r) s q₂ a₂ →
      HasGateFace W (cfPocket R L r) B
        (a₁ '' Icc 0 1 ∪ a₂ '' Icc 0 1 ∪ ofReal '' Icc (min q₁ q₂) (max q₁ q₂)) s) :
    RelLoewner (fun v => ψ (erasedPath η (cfPocket R L r) τ σ v))
      (pocketClock η (cfPocket R L r) τ σ σ) := by
  apply relLoewner_of_face_boundaries hP hη hW hW0
    (PocketJordan.image_negInv_subset_H h.changePocket_subset_H) hψ havoid
    (mapped_gaps_of_proper_faces h h0 hP hη hW hW0 hηH hproper hAC₁ hAC₂ havoid hfaces)
  intro u hu
  exact hasTargetFace_of_gate_faces (h.isCfPocket h0) hη hW hW0 hP.nonneg
    (hP.fibre_mem u).1 (hP.fibre_lt_σ hu) hP.first_y hP.first_x hP.fresh_x
    (hfaces _ (hP.fibre_mem u).1 (hP.fibre_lt_σ hu))

end Reduction

section OuterOuter

variable {R L M₁ M₂ : ℝ≥0 → ℂ} {r : ℝ≥0} {W : ℝ → ℝ} {η : ℝ → ℂ}

/-- **Aux. lemma 41 for a bounded pocket with two outer arms** (§5.4, "Erasure, relative prime ends, and the relative
driver", with "For two outer arms apply this reasoning to both certified frontiers"). Walls `R`, `L` with
`range R ⊆ E_R ∪ range M₁`, `range L ⊆ E_L ∪ range M₂`, `E_R = rightSideOf (range M₁)`, `E_L = leftSideOf (range M₂)`;
the counterflow `η` a Loewner trace in `ℍ` avoiding `m(E_R ∪ E_L)`, visiting `M₁`, `M₂` in reverse order and every
point of `M₁`, with Aux. 42. Then the erased pocket traversal has a continuous relative Loewner driver in every Jordan
coordinate of the pocket. -/
theorem relLoewner_outerOuter {ψ : ℂ → ℂ}
    (h : IsChangeConfigInc R L r) (hb : 0 < rightLo R L r)
    (hM₁ : IsSimpleProper M₁) (hM₂ : IsSimpleProper M₂)
    (hO₁ : IsOrderedArcs (Lemma71I.realPath R) (Lemma71I.realPath M₁) (Lemma71I.realPath L))
    (hO₂ : IsOrderedArcs (Lemma71I.realPath R) (Lemma71I.realPath M₂) (Lemma71I.realPath L))
    (hc₁R : NoCommonArc M₁ R) (hc₁L : NoCommonArc M₁ L) (hc₂R : NoCommonArc M₂ R)
    (hc₂L : NoCommonArc M₂ L)
    (houterR : range R ⊆ rightSideOf (range M₁) ∪ range M₁)
    (houterL : range L ⊆ leftSideOf (range M₂) ∪ range M₂)
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hηH : ∀ t, 0 < t → η t ∈ H)
    (hψ : IsJordanCoord (cfPocket R L r) (cfArcR R L r 0) (cfArcR R L r 1) ψ)
    (havoid : ∀ t, 0 ≤ t → negInv (η t) ∉ rightSideOf (range M₁) ∪ leftSideOf (range M₂))
    (hrev₁ : IsWallReverseVisit M₁ η) (hrev₂ : IsWallReverseVisit M₂ η) (hvis₁ : IsWallVisited M₁ η)
    (h42 : Theorem14.GB10.NoSimpleArcInterval (fun s : ℝ≥0 => η s) ⊤) :
    RelLoewner
      (fun v => ψ (erasedPath η (cfPocket R L r)
        (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0)) v))
      (pocketClock η (cfPocket R L r)
        (firstHit η (cfArcR R L r 1)) (firstHit η (cfArcR R L r 0))
        (firstHit η (cfArcR R L r 0))) := by
  have h0 := PocketMarks.zero_notMem_closure_of_rightLo_pos h hb
  have hC := h.isCfPocket h0
  have havoidB : ∀ t, 0 ≤ t →
      η t ∉ negInv '' rightSideOf (range M₁) ∪ negInv '' leftSideOf (range M₂) := fun t ht hm => by
    rcases hm with hm | hm
    · exact notMem_image_negInv (fun hz => havoid t ht (Or.inl hz)) hm
    · exact notMem_image_negInv (fun hz => havoid t ht (Or.inr hz)) hm
  have hgap := OuterIn.pocketGapEq_outerOuter h hb hM₁ hO₁ hO₂ hc₁R hc₁L hη havoid hrev₁ hvis₁ h42
  have hAC := OuterGeom.outerOuterAttach h hb hM₁ hO₁ hc₁R hc₁L hη.2.1 hη.1 hrev₁ hvis₁
  have hP := isErasurePocket_outerOuter h hb hM₁ hM₂ hO₁ hO₂ hc₁R hc₁L hc₂R hc₂L houterR houterL
    hη hW hW0 havoid hrev₁ hrev₂ hvis₁ h42 hAC hgap
  have h42' := no_interval_frontier hC hη.2.1 h42
  have hAC₁ := barrierAttachConst_of_outerCollars hη.2.1 hC.cont₁ hP.nonneg hP.first_y hP.fresh_x
    h42' havoidB fun _ hv => R7GapEqGeo.hasExteriorCollar_cfArcR h h0
      (changePocket_subset_left_of_order h hO₁) ((right_exterior_subset hO₁).trans subset_union_left)
      Subset.rfl hv
  have hxf₂ : cfArcL R L r 0 ∉ η '' Ico 0 (firstHit η (cfArcR R L r 0)) := by
    rw [hC.junction]
    exact hP.fresh_x
  have hAC₂ := barrierAttachConst_of_outerCollars hη.2.1 hC.cont₂ hP.nonneg
    (hP.first_y.trans hC.seed.symm) hxf₂ h42' havoidB
    fun _ hv => R7GapEqGeo.hasExteriorCollar_cfArcL h h0
      (changePocket_subset_right_of_order h hO₂) ((left_exterior_subset hO₂).trans subset_union_right)
      Subset.rfl hv
  have hproper := hasProperEarlierArm_middle h h0 hM₁ hO₁ hc₁R hc₁L hη.1 hrev₁ hP.fresh_x
  have haccess := allowedTargetAdherence_outerOuter h h0 hM₁ hM₂ hO₁ hO₂ hc₁R hc₁L hc₂R hc₂L
    houterR houterL hη hW hW0 hP.nonneg hP.first_y hP.first_x hP.fresh_x hrev₁ hrev₂
  obtain ⟨hE₁, hE₁H, hE₁b⟩ := right_exterior_props h.right
  obtain ⟨hE₂, hE₂H, hE₂b⟩ := left_exterior_props h.left
  apply relLoewner_of_proper_gate_faces h h0 hP hη hW hW0 hηH hψ hproper hAC₁ hAC₂ havoidB
  intro s hτs hsσ q₁ q₂ a₁ a₂ ha₁ ha₂
  refine gate_face_of_two_exteriors_of_target_adherence hη hW hW0 hC hP.nonneg hτs hsσ hP.first_y
    hP.first_x hP.fresh_x ha₁ ha₂ hE₁ hE₁H hE₁b ?_ (right_exterior_disjoint_frontier h h0 hO₁)
    hE₂ hE₂H hE₂b ?_ (left_exterior_disjoint_frontier h h0 hO₂)
    (cfArcR_subset_closure_exterior h h0) (cfArcL_subset_closure_exterior h h0) (haccess s hτs hsσ)
  · refine Set.disjoint_left.2 ?_
    rintro _ hzE ⟨t, ht, rfl⟩
    exact havoidB t ht.1 (Or.inl (right_exterior_subset hO₁ hzE))
  · refine Set.disjoint_left.2 ?_
    rintro _ hzE ⟨t, ht, rfl⟩
    exact havoidB t ht.1 (Or.inr (left_exterior_subset hO₂ hzE))

/-- **`OuterIn.OuterRelLoewner` for a bounded pocket with two outer arms** (the field `relOuterOuter` of
`OuterGeom.OuterGeomRest`, pathwise): Aux. lemma 41 in every Jordan coordinate `IsCfJordan` of the pocket. -/
theorem outerRelLoewner_outerOuter
    (h : IsChangeConfigInc R L r) (hb : 0 < rightLo R L r)
    (hM₁ : IsSimpleProper M₁) (hM₂ : IsSimpleProper M₂)
    (hO₁ : IsOrderedArcs (Lemma71I.realPath R) (Lemma71I.realPath M₁) (Lemma71I.realPath L))
    (hO₂ : IsOrderedArcs (Lemma71I.realPath R) (Lemma71I.realPath M₂) (Lemma71I.realPath L))
    (hc₁R : NoCommonArc M₁ R) (hc₁L : NoCommonArc M₁ L) (hc₂R : NoCommonArc M₂ R)
    (hc₂L : NoCommonArc M₂ L)
    (houterR : range R ⊆ rightSideOf (range M₁) ∪ range M₁)
    (houterL : range L ⊆ leftSideOf (range M₂) ∪ range M₂)
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hηH : ∀ t, 0 < t → η t ∈ H)
    (havoid : ∀ t, 0 ≤ t → negInv (η t) ∉ rightSideOf (range M₁) ∪ leftSideOf (range M₂))
    (hrev₁ : IsWallReverseVisit M₁ η) (hrev₂ : IsWallReverseVisit M₂ η) (hvis₁ : IsWallVisited M₁ η)
    (h42 : Theorem14.GB10.NoSimpleArcInterval (fun s : ℝ≥0 => η s) ⊤) :
    OuterIn.OuterRelLoewner R L r η := fun _ hψ =>
  relLoewner_outerOuter h hb hM₁ hM₂ hO₁ hO₂ hc₁R hc₁L hc₂R hc₂L houterR houterL hη hW hW0 hηH
    (PocketStopMarked.isJordanCoord_of_cf hψ) havoid hrev₁ hrev₂ hvis₁ h42

end OuterOuter

end InteractingSLE.Sec7.Aux41OO
