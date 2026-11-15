/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7InfinityChartGeometry

/-!
# Compactified future confinement with only interior side selection left

PROVE-R7-GAPEQ. The compact Jordan boundary is constructed. Its unbounded physical
component and active/closed confinement follow from the two explicit side inputs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H Hbar)
open InteractingSLE.YuanSimpleApprox (trMap)
open scoped NNReal

namespace InteractingSLE.Sec7.R7InfinityChart

open Sec6 WangWu Lemma71I PocketCoord PocketJordan

/-- The Jordan boundary and its physical landing are proved. Supplying only
`InfiniteFaceSides` identifies its component and confines active and limiting visits. -/
theorem exists_confined_compact_face {R L : ℝ≥0 → ℂ} {r : ℝ≥0}
    {W : ℝ → ℝ} {η : ℝ → ℂ} {F : Set ℂ} {τ : ℝ}
    (h : IsChangeConfigInc R L r) (h0 : rightLo R L r = 0)
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hτ0 : 0 ≤ τ) (hτ : η τ = cfArcRInf R L r 0)
    (hallowed : R7EndFace.AllowedUnboundedComponents W (cfPocket R L r) F τ)
    (havoid : ∀ t, 0 ≤ t → η t ∉ F) :
    ∀ s, τ ≤ s → ∃ (a : ℝ) (Γ : Set ℂ),
      LQGMetric.JordanMap.IsJordanCurve Γ ∧ Γ ⊆ Hbar ∧ (0 : ℂ) ∈ Γ ∧
      (∀ ζ ∈ Γ, ζ ∈ H → trMap W 0 s (psiMapInv a ζ) ∈ frontier (cfPocket R L r)) ∧
      (InfiniteFaceSides W (cfPocket R L r) s a Γ →
        (∃ q : ℂ, R7EndFace.InfiniteFaceChart W (cfPocket R L r) s a Γ q) ∧
        (∀ t, s ≤ t → η t ∈ cfPocket R L r → trMap W s t 0 ∈ H →
          psiMap a (trMap W s t 0) ∈ innerSide Γ) ∧
        ∀ b ∈ closure {t | s < t ∧ η t ∈ cfPocket R L r}, trMap W s b 0 ≠ a →
          psiMap a (trMap W s b 0) ∈ closure (innerSide Γ)) := by
  intro s hτs
  obtain ⟨a, Γ, hJ, hH, hzero, hbd, hchart⟩ := exists_pocket_compact_face
    (h.isCfPocketInf h0) hη hW hW0 hτ0 hτs hτ
  refine ⟨a, Γ, hJ, hH, hzero, hbd, fun hsides => ?_⟩
  obtain ⟨q, hq⟩ := hchart hsides
  have hs0 := hτ0.trans hτs
  have hav := fun t ht => havoid t (hs0.trans ht)
  exact ⟨⟨q, hq⟩,
    R7EndFace.ownFuture_mem_infinite_face h h0 hη hW hW0 hs0 hτs hallowed hq hav,
    fun b hb hpole => R7EndFace.ownFuture_mem_closure_infinite_face h h0 hη hW hW0
      hs0 hτs hallowed hq hav hb hpole⟩

end InteractingSLE.Sec7.R7InfinityChart
