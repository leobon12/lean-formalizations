/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7InfinityChartConfinement

/-!
# Actual mixed compactified faces with explicit interior side inputs

PROVE-R7-GAPEQ. The face boundary, physical landing, unboundedness, component image
and confinement reductions are assembled. Interior side selection remains named.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H Hbar)
open InteractingSLE.YuanSimpleApprox (trMap)
open scoped NNReal

namespace InteractingSLE.Sec7.R7InfinityChart

open Sec6 WangWu Lemma71I PocketCoord PocketJordan R7StopIn

/-- The left-outer compactified boundary is constructed from source wall data.
Only interior frontier avoidance and a pocket witness remain conditional. -/
theorem exists_confined_compact_face_leftOuter {R M L : ℝ≥0 → ℂ} {r : ℝ≥0} {τ : ℝ}
    (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0)
    (hM : IsSimpleProper M) (hO : IsOrderedArcs (realPath R) (realPath M) (realPath L))
    (hcR : NoCommonArc M R) (hcL : NoCommonArc M L)
    (houter : range L ⊆ leftSideOf (range M) ∪ range M)
    {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hτ0 : 0 ≤ τ) (hτ : η τ = cfArcRInf R L r 0)
    (hrevR : IsWallReverseVisit R η) (hrevM : IsWallReverseVisit M η)
    (havoid : ∀ t, 0 ≤ t → negInv (η t) ∉ leftSideOf (range M)) :
    ∀ s, τ ≤ s → ∃ (a : ℝ) (Γ : Set ℂ),
      LQGMetric.JordanMap.IsJordanCurve Γ ∧ Γ ⊆ Hbar ∧ (0 : ℂ) ∈ Γ ∧
      (∀ ζ ∈ Γ, ζ ∈ H → trMap W 0 s (psiMapInv a ζ) ∈ frontier (cfPocket R L r)) ∧
      (InfiniteFaceSides W (cfPocket R L r) s a Γ →
        (∃ q : ℂ, R7EndFace.InfiniteFaceChart W (cfPocket R L r) s a Γ q) ∧
        (∀ t, s ≤ t → η t ∈ cfPocket R L r → trMap W s t 0 ∈ H →
          psiMap a (trMap W s t 0) ∈ innerSide Γ) ∧
        ∀ b ∈ closure {t | s < t ∧ η t ∈ cfPocket R L r}, trMap W s b 0 ≠ a →
          psiMap a (trMap W s b 0) ∈ closure (innerSide Γ)) := by
  exact exists_confined_compact_face h h0 hη hW hW0 hτ0 hτ
    (R7EndFace.allowedUnboundedComponents_leftOuter h h0 hM hO hcR hcL houter
      hη hW hW0 hτ0 hτ hrevR hrevM)
    (fun t ht => notMem_image_negInv (havoid t ht))

/-- The reflected right-outer compactified boundary, preserving the right-labeled
entrance and the contained left wall's reverse visit type. -/
theorem exists_confined_compact_face_rightOuter {R M L : ℝ≥0 → ℂ} {r : ℝ≥0} {τ : ℝ}
    (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0)
    (hM : IsSimpleProper M) (hO : IsOrderedArcs (realPath R) (realPath M) (realPath L))
    (hcR : NoCommonArc M R) (hcL : NoCommonArc M L)
    (houter : range R ⊆ rightSideOf (range M) ∪ range M)
    {W : ℝ → ℝ} {η : ℝ → ℂ}
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hτ0 : 0 ≤ τ) (hτ : η τ = cfArcRInf R L r 0)
    (hrevL : IsWallReverseVisit L η) (hrevM : IsWallReverseVisit M η)
    (havoid : ∀ t, 0 ≤ t → negInv (η t) ∉ rightSideOf (range M)) :
    ∀ s, τ ≤ s → ∃ (a : ℝ) (Γ : Set ℂ),
      LQGMetric.JordanMap.IsJordanCurve Γ ∧ Γ ⊆ Hbar ∧ (0 : ℂ) ∈ Γ ∧
      (∀ ζ ∈ Γ, ζ ∈ H → trMap W 0 s (psiMapInv a ζ) ∈ frontier (cfPocket R L r)) ∧
      (InfiniteFaceSides W (cfPocket R L r) s a Γ →
        (∃ q : ℂ, R7EndFace.InfiniteFaceChart W (cfPocket R L r) s a Γ q) ∧
        (∀ t, s ≤ t → η t ∈ cfPocket R L r → trMap W s t 0 ∈ H →
          psiMap a (trMap W s t 0) ∈ innerSide Γ) ∧
        ∀ b ∈ closure {t | s < t ∧ η t ∈ cfPocket R L r}, trMap W s b 0 ≠ a →
          psiMap a (trMap W s b 0) ∈ closure (innerSide Γ)) := by
  exact exists_confined_compact_face h h0 hη hW hW0 hτ0 hτ
    (R7EndFace.allowedUnboundedComponents_rightOuter h h0 hM hO hcR hcL houter
      hη hW hW0 hτ0 hτ hrevL hrevM)
    (fun t ht => notMem_image_negInv (havoid t ht))

end InteractingSLE.Sec7.R7InfinityChart
