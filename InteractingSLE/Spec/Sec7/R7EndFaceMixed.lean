/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7EndFaceFuture

/-!
# Actual infinite-end mixed-pocket confinement

PROVE-R7-GAPEQ. Component existence, selection and confinement follow from source wall
data. The result includes own-mapped limits of visits, without a chart hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H fwdHull fwdMap)
open InteractingSLE.YuanSimpleApprox (trMap)
open scoped NNReal

namespace InteractingSLE.Sec7.R7EndFace

open Sec6 WangWu Lemma71I PocketCoord PocketJordan R7StopIn

/-- Left-outer infinite-end confinement: all allowed surviving points and all future
active pocket visits use the unique unbounded component; visit limits lie in its lifted
closure. No component or chart assertion is a premise. -/
theorem exists_selected_component_leftOuter {R M L : ℝ≥0 → ℂ} {r : ℝ≥0} {τ : ℝ}
    (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0)
    (hM : IsSimpleProper M) (hO : IsOrderedArcs (realPath R) (realPath M) (realPath L))
    (hcR : NoCommonArc M R) (hcL : NoCommonArc M L)
    (houter : range L ⊆ leftSideOf (range M) ∪ range M)
    {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hτ0 : 0 ≤ τ) (hτ : η τ = cfArcRInf R L r 0)
    (hrevR : IsWallReverseVisit R η) (hrevM : IsWallReverseVisit M η)
    (havoid : ∀ t, 0 ≤ t → negInv (η t) ∉ leftSideOf (range M)) :
    ∀ s, τ ≤ s → ∃ p ∈ cfPocket R L r ∩ (H \ fwdHull W s),
      ¬ IsBounded (connectedComponentIn (cfPocket R L r ∩ (H \ fwdHull W s)) p) ∧
      (∀ z ∈ cfPocket R L r ∩ (H \ fwdHull W s), z ∉ negInv '' leftSideOf (range M) →
        z ∈ connectedComponentIn (cfPocket R L r ∩ (H \ fwdHull W s)) p) ∧
      (∀ t, s ≤ t → η t ∈ cfPocket R L r → trMap W s t 0 ∈ H →
        trMap W s t 0 ∈ fwdMap W s ''
          connectedComponentIn (cfPocket R L r ∩ (H \ fwdHull W s)) p) ∧
      ∀ a ∈ closure {t | s < t ∧ η t ∈ cfPocket R L r},
        trMap W s a 0 ∈ closure (fwdMap W s ''
          connectedComponentIn (cfPocket R L r ∩ (H \ fwdHull W s)) p) := by
  have hallowed := allowedUnboundedComponents_leftOuter h h0 hM hO hcR hcL houter
    hη hW hW0 hτ0 hτ hrevR hrevM
  intro s hτs
  obtain ⟨p, hp, hpb, hsel⟩ := exists_allowed_component h h0 hW hallowed hτs
  have hs0 := hτ0.trans hτs
  have hav : ∀ t, s ≤ t → η t ∉ negInv '' leftSideOf (range M) :=
    fun t hst => notMem_image_negInv (havoid t (hs0.trans hst))
  exact ⟨p, hp, hpb, hsel,
    ownFuture_mem_unbounded_component h h0 hη hW hW0 hs0 hτs hallowed hpb hav,
    fun a ha => ownFuture_mem_closure_unbounded_component h h0 hη hW hW0 hs0 hτs
      hallowed hpb hav ha⟩

/-- Right-outer infinite-end confinement, with the contained left wall and the same
right-labeled entrance point. -/
theorem exists_selected_component_rightOuter {R M L : ℝ≥0 → ℂ} {r : ℝ≥0} {τ : ℝ}
    (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0)
    (hM : IsSimpleProper M) (hO : IsOrderedArcs (realPath R) (realPath M) (realPath L))
    (hcR : NoCommonArc M R) (hcL : NoCommonArc M L)
    (houter : range R ⊆ rightSideOf (range M) ∪ range M)
    {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hτ0 : 0 ≤ τ) (hτ : η τ = cfArcRInf R L r 0)
    (hrevL : IsWallReverseVisit L η) (hrevM : IsWallReverseVisit M η)
    (havoid : ∀ t, 0 ≤ t → negInv (η t) ∉ rightSideOf (range M)) :
    ∀ s, τ ≤ s → ∃ p ∈ cfPocket R L r ∩ (H \ fwdHull W s),
      ¬ IsBounded (connectedComponentIn (cfPocket R L r ∩ (H \ fwdHull W s)) p) ∧
      (∀ z ∈ cfPocket R L r ∩ (H \ fwdHull W s), z ∉ negInv '' rightSideOf (range M) →
        z ∈ connectedComponentIn (cfPocket R L r ∩ (H \ fwdHull W s)) p) ∧
      (∀ t, s ≤ t → η t ∈ cfPocket R L r → trMap W s t 0 ∈ H →
        trMap W s t 0 ∈ fwdMap W s ''
          connectedComponentIn (cfPocket R L r ∩ (H \ fwdHull W s)) p) ∧
      ∀ a ∈ closure {t | s < t ∧ η t ∈ cfPocket R L r},
        trMap W s a 0 ∈ closure (fwdMap W s ''
          connectedComponentIn (cfPocket R L r ∩ (H \ fwdHull W s)) p) := by
  have hallowed := allowedUnboundedComponents_rightOuter h h0 hM hO hcR hcL houter
    hη hW hW0 hτ0 hτ hrevL hrevM
  intro s hτs
  obtain ⟨p, hp, hpb, hsel⟩ := exists_allowed_component h h0 hW hallowed hτs
  have hs0 := hτ0.trans hτs
  have hav : ∀ t, s ≤ t → η t ∉ negInv '' rightSideOf (range M) :=
    fun t hst => notMem_image_negInv (havoid t (hs0.trans hst))
  exact ⟨p, hp, hpb, hsel,
    ownFuture_mem_unbounded_component h h0 hη hW hW0 hs0 hτs hallowed hpb hav,
    fun a ha => ownFuture_mem_closure_unbounded_component h h0 hη hW hW0 hs0 hτs
      hallowed hpb hav ha⟩

end InteractingSLE.Sec7.R7EndFace
