/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.Aux41OOInfGap
import InteractingSLE.Spec.Sec7.R7RelativeInfLoewner
import InteractingSLE.Spec.Sec7.OuterGeomAttach

/-!
# Aux. lemma 41 for a pocket with two outer arms opening at the flow seed

Packet PROVE-R7-AUX41OO (Theorem 1.2's R.7). The relative driver of an R.7 pocket opening at the flow seed
(`rightLo = 0`) whose two arms are both outer, with the certified frontiers `M₁ = β_R`, `M₂ = β_L` between them.

PROVE-R7-GAPEQ's infinite-end criterion `R7RelativeInf.relLoewner_of_compact_charts` (generic in the pocket) needs the
erasure at infinity, mapped gaps in every chart after the entrance, and compact component charts with arbitrarily
negative poles confining the active future. For two outer arms:

* the erasure is `R7StopIn.isErasurePocketInf_outerOuter` with Aux. 37 along the clipped `β_R`
  (`OuterGeom.outerOuterAttachInf`) and §5.4's gap equality at infinity (`OuterIn.pocketGapEqInf_outerOuter`);
* the mapped gaps are `gap_eq_outerOuterInf` (`Aux41OOInfGap`);
* the charts below any pole are `exists_chart_below_outerOuter` (`infiniteFaceSides_outerOuter`, the two-barrier
  `allowedUnboundedComponents_outerOuter` and GAPEQ's `R7EndFace.ownFuture_mem_infinite_face`).

**`relLoewnerInf_outerOuter`** is Aux. 41's conclusion; **`outerRelLoewnerInf_outerOuter`** is
`OuterIn.OuterRelLoewnerInf`, the field `relInfOuterOuter` of `OuterGeom.OuterGeomRest`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H Hbar fwdHull fwdMap)
open InteractingSLE.YuanSimpleApprox (trMap)
open scoped NNReal

namespace InteractingSLE.Sec7.Aux41OO

open Sec6 WangWu Lemma71I PocketCoord PocketJordan R7StopIn R7InfinityChart R7InfinityAccess

variable {R L M₁ M₂ : ℝ≥0 → ℂ} {r : ℝ≥0} {τ : ℝ} {W : ℝ → ℝ} {η : ℝ → ℂ}

/-- **Component charts with arbitrarily negative poles for a two-outer infinite pocket**, confining every active future
visit (the input `hcharts` of `R7RelativeInf.relLoewner_of_compact_charts`). -/
theorem exists_chart_below_outerOuter
    (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0)
    (hM₁ : IsSimpleProper M₁) (hM₂ : IsSimpleProper M₂)
    (hO₁ : IsOrderedArcs (Lemma71I.realPath R) (Lemma71I.realPath M₁) (Lemma71I.realPath L))
    (hO₂ : IsOrderedArcs (Lemma71I.realPath R) (Lemma71I.realPath M₂) (Lemma71I.realPath L))
    (hc₁R : NoCommonArc M₁ R) (hc₁L : NoCommonArc M₁ L) (hc₂R : NoCommonArc M₂ R)
    (hc₂L : NoCommonArc M₂ L)
    (houterR : range R ⊆ rightSideOf (range M₁) ∪ range M₁)
    (houterL : range L ⊆ leftSideOf (range M₂) ∪ range M₂)
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hτ0 : 0 ≤ τ) (hτ : η τ = cfArcRInf R L r 0)
    (hrev₁ : IsWallReverseVisit M₁ η) (hrev₂ : IsWallReverseVisit M₂ η)
    (havoid : ∀ t, 0 ≤ t → negInv (η t) ∉ rightSideOf (range M₁) ∪ leftSideOf (range M₂)) :
    ∀ s, τ ≤ s → ∀ B : ℝ, ∃ p < B, ∃ (Γ : Set ℂ) (q : ℂ),
      R7EndFace.InfiniteFaceChart W (cfPocket R L r) s p Γ q ∧
      ∀ t, s ≤ t → η t ∈ cfPocket R L r → trMap W s t 0 ∈ H →
        psiMap p (trMap W s t 0) ∈ innerSide Γ := by
  intro s hτs B
  have hC := h.isCfPocketInf h0
  have hs := hτ0.trans hτs
  have havoidB : ∀ t, 0 ≤ t →
      η t ∉ negInv '' rightSideOf (range M₁) ∪ negInv '' leftSideOf (range M₂) := fun t ht hm => by
    rcases hm with hm | hm
    · exact notMem_image_negInv (fun hz => havoid t ht (Or.inl hz)) hm
    · exact notMem_image_negInv (fun hz => havoid t ht (Or.inr hz)) hm
  obtain ⟨q₁, q₂, hq⟩ := exists_pocket_chart_reduction hC hη hW hW0 hτ0 hτs hτ
  let p := min (min q₁ q₂) B - 1
  have hp : p < min q₁ q₂ := (sub_one_lt _).trans_le (min_le_left _ _)
  obtain ⟨b₁, b₂, hb₁, hb₂, hΓ, hΓH, -, -, hchart⟩ := hq _ hp
  obtain ⟨q, hq'⟩ := hchart
    (infiniteFaceSides_outerOuter h h0 hO₁ hO₂ hη hW hW0 hτ0 hτ havoid hτs hb₁ hb₂ hp hΓ hΓH)
  have hallowed := allowedUnboundedComponents_outerOuter h h0 hM₁ hM₂ hO₁ hO₂ hc₁R hc₁L hc₂R hc₂L
    houterR houterL hη hW hW0 hτ0 hτ hrev₁ hrev₂
  exact ⟨p, (sub_one_lt _).trans_le (min_le_right _ _), _, q, hq',
    R7EndFace.ownFuture_mem_infinite_face h h0 hη hW hW0 hs hτs hallowed hq'
      (fun t ht => havoidB t (hs.trans ht))⟩

/-- **Aux. lemma 41 for a pocket with two outer arms opening at the flow seed** (§5.4 with "For two outer arms apply
this reasoning to both certified frontiers", at the infinite end). Walls `R`, `L` with `range R ⊆ E_R ∪ range M₁`,
`range L ⊆ E_L ∪ range M₂`; the counterflow `η` a Loewner trace avoiding `m(E_R ∪ E_L)`, visiting `M₁`, `M₂` in
reverse order and every point of `M₁`, with Aux. 42. Then the erased pocket traversal has a continuous relative Loewner
driver in every Jordan coordinate of the pocket with the entrance at `0`. -/
theorem relLoewnerInf_outerOuter {ψ : ℂ → ℂ}
    (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0)
    (hM₁ : IsSimpleProper M₁) (hM₂ : IsSimpleProper M₂)
    (hO₁ : IsOrderedArcs (Lemma71I.realPath R) (Lemma71I.realPath M₁) (Lemma71I.realPath L))
    (hO₂ : IsOrderedArcs (Lemma71I.realPath R) (Lemma71I.realPath M₂) (Lemma71I.realPath L))
    (hc₁R : NoCommonArc M₁ R) (hc₁L : NoCommonArc M₁ L) (hc₂R : NoCommonArc M₂ R)
    (hc₂L : NoCommonArc M₂ L)
    (houterR : range R ⊆ rightSideOf (range M₁) ∪ range M₁)
    (houterL : range L ⊆ leftSideOf (range M₂) ∪ range M₂)
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hψ : IsJordanCoordInf (cfPocket R L r) (cfArcRInf R L r 0) ψ)
    (havoid : ∀ t, 0 ≤ t → negInv (η t) ∉ rightSideOf (range M₁) ∪ leftSideOf (range M₂))
    (hrev₁ : IsWallReverseVisit M₁ η) (hrev₂ : IsWallReverseVisit M₂ η) (hvis₁ : IsWallVisited M₁ η)
    (h42 : Theorem14.GB10.NoSimpleArcInterval (fun s : ℝ≥0 => η s) ⊤) :
    RelLoewner (fun v => ψ (erasedPathInf η (cfPocket R L r) (firstHit η (cfArcRInf R L r 0)) v))
      (clockEnd η (cfPocket R L r) (firstHit η (cfArcRInf R L r 0))) := by
  have hP := isErasurePocketInf_outerOuter h h0 hM₁ hM₂ hO₁ hO₂ hc₁R hc₁L hc₂R hc₂L houterR houterL
    hη havoid hrev₁ hrev₂ hvis₁ (OuterGeom.outerOuterAttachInf h h0 hM₁ hO₁ hc₁R hc₁L hη.2.1 hη.1 hrev₁ hvis₁)
    (OuterIn.pocketGapEqInf_outerOuter h h0 hM₁ hO₁ hO₂ hc₁R hc₁L hη havoid hrev₁ hvis₁ h42)
  apply R7RelativeInf.relLoewner_of_compact_charts hP hη hW hW0 (h.isCfPocketInf h0).subset_H hψ
  · intro s a b hτs hsa hab hgap ha hb
    exact (gap_eq_outerOuterInf h h0 hM₁ hM₂ hO₁ hO₂ hc₁R hc₁L hc₂R hc₂L houterR houterL hη hW hW0
      hP.nonneg hP.first_y hrev₁ hrev₂ havoid h42 hτs hsa hab hgap ha hb).1
  · exact exists_chart_below_outerOuter h h0 hM₁ hM₂ hO₁ hO₂ hc₁R hc₁L hc₂R hc₂L houterR houterL
      hη hW hW0 hP.nonneg hP.first_y hrev₁ hrev₂ havoid

/-- **`OuterIn.OuterRelLoewnerInf` for a pocket with two outer arms opening at the flow seed** (the field
`relInfOuterOuter` of `OuterGeom.OuterGeomRest`, pathwise): Aux. lemma 41 in every Jordan coordinate `IsCfJordanInf`
of the pocket. -/
theorem outerRelLoewnerInf_outerOuter
    (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0)
    (hM₁ : IsSimpleProper M₁) (hM₂ : IsSimpleProper M₂)
    (hO₁ : IsOrderedArcs (Lemma71I.realPath R) (Lemma71I.realPath M₁) (Lemma71I.realPath L))
    (hO₂ : IsOrderedArcs (Lemma71I.realPath R) (Lemma71I.realPath M₂) (Lemma71I.realPath L))
    (hc₁R : NoCommonArc M₁ R) (hc₁L : NoCommonArc M₁ L) (hc₂R : NoCommonArc M₂ R)
    (hc₂L : NoCommonArc M₂ L)
    (houterR : range R ⊆ rightSideOf (range M₁) ∪ range M₁)
    (houterL : range L ⊆ leftSideOf (range M₂) ∪ range M₂)
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (havoid : ∀ t, 0 ≤ t → negInv (η t) ∉ rightSideOf (range M₁) ∪ leftSideOf (range M₂))
    (hrev₁ : IsWallReverseVisit M₁ η) (hrev₂ : IsWallReverseVisit M₂ η) (hvis₁ : IsWallVisited M₁ η)
    (h42 : Theorem14.GB10.NoSimpleArcInterval (fun s : ℝ≥0 => η s) ⊤) :
    OuterIn.OuterRelLoewnerInf R L r η := by
  intro ψ hψ
  have hψ' : IsJordanCoordInf (cfPocket R L r) (cfArcRInf R L r 0) ψ := by
    rw [IsChangeConfigInc.cfArcRInf_zero]
    exact hψ
  exact relLoewnerInf_outerOuter h h0 hM₁ hM₂ hO₁ hO₂ hc₁R hc₁L hc₂R hc₂L houterR houterL hη hW hW0 hψ'
    havoid hrev₁ hrev₂ hvis₁ h42

end InteractingSLE.Sec7.Aux41OO
