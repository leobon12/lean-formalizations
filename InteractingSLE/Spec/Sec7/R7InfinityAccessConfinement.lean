/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7InfinityAccessActual

/-!
# Actual mixed infinite-end current-face confinement

PROVE-R7-GAPEQ. The former chart and side-selection hypotheses are discharged.
Both actual mixed orientations have the selected lift and active/closed confinement.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H Hbar fwdHull fwdMap)
open InteractingSLE.YuanSimpleApprox (trMap)
open scoped NNReal

namespace InteractingSLE.Sec7.R7InfinityAccess

open Sec6 WangWu Lemma71I PocketCoord PocketJordan R7StopIn

/-- The actual left-outer compact face exists and confines both active pocket
visits and limiting visits. The real pole exclusion remains explicit at limits. -/
theorem exists_confined_infinite_face_leftOuter {R M L : ℝ≥0 → ℂ} {r : ℝ≥0} {τ : ℝ}
    (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0)
    (hM : IsSimpleProper M) (hO : IsOrderedArcs (realPath R) (realPath M) (realPath L))
    (hcR : NoCommonArc M R) (hcL : NoCommonArc M L)
    (houter : range L ⊆ leftSideOf (range M) ∪ range M)
    {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hτ0 : 0 ≤ τ) (hτ : η τ = cfArcRInf R L r 0)
    (hrevR : IsWallReverseVisit R η) (hrevM : IsWallReverseVisit M η)
    (havoid : ∀ t, 0 ≤ t → negInv (η t) ∉ leftSideOf (range M)) :
    ∀ s, τ ≤ s → ∃ (a : ℝ) (Γ : Set ℂ) (q : ℂ),
      R7EndFace.InfiniteFaceChart W (cfPocket R L r) s a Γ q ∧
      fwdMap W s '' connectedComponentIn (cfPocket R L r ∩ (H \ fwdHull W s)) q =
        psiMapInv a '' innerSide Γ ∧
      (∀ t, s ≤ t → η t ∈ cfPocket R L r → trMap W s t 0 ∈ H →
        psiMap a (trMap W s t 0) ∈ innerSide Γ) ∧
      ∀ b ∈ closure {t | s < t ∧ η t ∈ cfPocket R L r}, trMap W s b 0 ≠ a →
        psiMap a (trMap W s b 0) ∈ closure (innerSide Γ) := by
  intro s hτs
  have hs := hτ0.trans hτs
  obtain ⟨a, Γ, q, hq⟩ := exists_infiniteFaceChart_leftOuter h h0 hO hη hW hW0
    hτ0 hτ hrevR havoid s hτs
  have hallowed := R7EndFace.allowedUnboundedComponents_leftOuter h h0 hM hO hcR hcL
    houter hη hW hW0 hτ0 hτ hrevR hrevM
  have hav := fun t ht => notMem_image_negInv (havoid t (hs.trans ht))
  exact ⟨a, Γ, q, hq, R7EndFace.lift_eq_infinite_face hW hW0 hs hq,
    R7EndFace.ownFuture_mem_infinite_face h h0 hη hW hW0 hs hτs hallowed hq hav,
    fun b hb hpole => R7EndFace.ownFuture_mem_closure_infinite_face h h0 hη hW hW0
      hs hτs hallowed hq hav hb hpole⟩

/-- The reflected right-outer compact face, with contained left and middle wall
reverse visits, has the same proved lift and confinement conclusions. -/
theorem exists_confined_infinite_face_rightOuter {R M L : ℝ≥0 → ℂ} {r : ℝ≥0} {τ : ℝ}
    (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0)
    (hM : IsSimpleProper M) (hO : IsOrderedArcs (realPath R) (realPath M) (realPath L))
    (hcR : NoCommonArc M R) (hcL : NoCommonArc M L)
    (houter : range R ⊆ rightSideOf (range M) ∪ range M)
    {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hτ0 : 0 ≤ τ) (hτ : η τ = cfArcRInf R L r 0)
    (hrevL : IsWallReverseVisit L η) (hrevM : IsWallReverseVisit M η)
    (havoid : ∀ t, 0 ≤ t → negInv (η t) ∉ rightSideOf (range M)) :
    ∀ s, τ ≤ s → ∃ (a : ℝ) (Γ : Set ℂ) (q : ℂ),
      R7EndFace.InfiniteFaceChart W (cfPocket R L r) s a Γ q ∧
      fwdMap W s '' connectedComponentIn (cfPocket R L r ∩ (H \ fwdHull W s)) q =
        psiMapInv a '' innerSide Γ ∧
      (∀ t, s ≤ t → η t ∈ cfPocket R L r → trMap W s t 0 ∈ H →
        psiMap a (trMap W s t 0) ∈ innerSide Γ) ∧
      ∀ b ∈ closure {t | s < t ∧ η t ∈ cfPocket R L r}, trMap W s b 0 ≠ a →
        psiMap a (trMap W s b 0) ∈ closure (innerSide Γ) := by
  intro s hτs
  have hs := hτ0.trans hτs
  obtain ⟨a, Γ, q, hq⟩ := exists_infiniteFaceChart_rightOuter h h0 hO hη hW hW0
    hτ0 hτ hrevL havoid s hτs
  have hallowed := R7EndFace.allowedUnboundedComponents_rightOuter h h0 hM hO hcR hcL
    houter hη hW hW0 hτ0 hτ hrevL hrevM
  have hav := fun t ht => notMem_image_negInv (havoid t (hs.trans ht))
  exact ⟨a, Γ, q, hq, R7EndFace.lift_eq_infinite_face hW hW0 hs hq,
    R7EndFace.ownFuture_mem_infinite_face h h0 hη hW hW0 hs hτs hallowed hq hav,
    fun b hb hpole => R7EndFace.ownFuture_mem_closure_infinite_face h h0 hη hW hW0
      hs hτs hallowed hq hav hb hpole⟩

end InteractingSLE.Sec7.R7InfinityAccess
