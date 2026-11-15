/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7InfinityChartBoundary
import InteractingSLE.Spec.Sec7.R7InfinityChartComponent

/-!
# The actual compactified boundary and its remaining side selection

PROVE-R7-GAPEQ. Both incoming arms, the Jordan boundary and its physical boundary
landing are proved. Whole-component chart identification needs only `InfiniteFaceSides`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H Hbar fwdHull fwdMap)
open InteractingSLE.YuanSimpleApprox (trMap)

namespace InteractingSLE.Sec7.R7InfinityChart

open Sec6 PocketJordan

/-- The compact boundary's half-plane points land on the original pocket frontier.
The real gate interval contributes no half-plane points. -/
theorem compactBoundary_mem_frontier {W : ℝ → ℝ} {η A₁ A₂ : ℝ → ℂ}
    {C : Set ℂ} {τ s a q₁ q₂ : ℝ} {b₁ b₂ : ℝ → ℂ}
    (hC : IsCfPocketInf C A₁ A₂)
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hτ0 : 0 ≤ τ) (hτs : τ ≤ s) (hτ : η τ = A₁ 0)
    (hb₁ : IsLastVisitArm W η A₁ s a q₁ b₁) (hb₂ : IsLastVisitArm W η A₂ s a q₂ b₂) :
    ∀ ζ ∈ compactBoundary b₁ b₂ (-(q₁ - a)⁻¹) (-(q₂ - a)⁻¹), ζ ∈ H →
      trMap W 0 s (psiMapInv a ζ) ∈ frontier C := by
  have hs := hτ0.trans hτs
  have hy₁ : A₁ 0 ∈ η '' Icc 0 s := ⟨τ, ⟨hτ0, hτs⟩, hτ⟩
  have hy₂ : A₂ 0 ∈ η '' Icc 0 s := hC.seed ▸ hy₁
  obtain ⟨hu₁, -, hD₁⟩ := lastVisit_tail_domain hη hs hC.cont₁ hC.tendsto₁ hC.mem_H₁ hy₁
  obtain ⟨hu₂, -, hD₂⟩ := lastVisit_tail_domain hη hs hC.cont₂ hC.tendsto₂ hC.mem_H₂ hy₂
  intro ζ hζ hζH
  rcases mem_open_arms_of_mem_compactBoundary hb₁.2.2.1 hb₂.2.2.1
    hb₁.2.2.2.1 hb₂.2.2.2.1 hζ hζH with hζ | hζ
  · rw [hb₁.2.2.2.2.2.1] at hζ
    obtain ⟨_, ⟨_, ⟨v, hv, rfl⟩, rfl⟩, rfl⟩ := hζ
    rw [psiMapInv_psiMap, trMap_zero_fwdMap hW hW0 hs (hD₁ v hv), hC.frontier_eq]
    exact Or.inl ⟨v, hu₁.trans hv.le, rfl⟩
  · rw [hb₂.2.2.2.2.2.1] at hζ
    obtain ⟨_, ⟨_, ⟨v, hv, rfl⟩, rfl⟩, rfl⟩ := hζ
    rw [psiMapInv_psiMap, trMap_zero_fwdMap hW hW0 hs (hD₂ v hv), hC.frontier_eq]
    exact Or.inr ⟨v, hu₂.trans hv.le, rfl⟩

/-- All compactified boundary data exist with no reverse visit requirement on
either original side. The remaining local side input then gives the previous chart. -/
theorem exists_pocket_chart_reduction {W : ℝ → ℝ} {η A₁ A₂ : ℝ → ℂ}
    {C : Set ℂ} {τ s : ℝ}
    (hC : IsCfPocketInf C A₁ A₂)
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hτ0 : 0 ≤ τ) (hτs : τ ≤ s) (hτ : η τ = A₁ 0) :
    ∃ q₁ q₂ : ℝ, ∀ a < min q₁ q₂, ∃ b₁ b₂ : ℝ → ℂ,
      IsLastVisitArm W η A₁ s a q₁ b₁ ∧ IsLastVisitArm W η A₂ s a q₂ b₂ ∧
      let Γ := compactBoundary b₁ b₂ (-(q₁ - a)⁻¹) (-(q₂ - a)⁻¹);
      LQGMetric.JordanMap.IsJordanCurve Γ ∧ Γ ⊆ Hbar ∧ (0 : ℂ) ∈ Γ ∧
        (∀ ζ ∈ Γ, ζ ∈ H → trMap W 0 s (psiMapInv a ζ) ∈ frontier C) ∧
        (InfiniteFaceSides W C s a Γ → ∃ q : ℂ, R7EndFace.InfiniteFaceChart W C s a Γ q) := by
  obtain ⟨q₁, q₂, harcs⟩ := exists_pocket_compact_arms hC hη hW hW0 hτ0 hτs hτ
  refine ⟨q₁, q₂, fun a ha => ?_⟩
  obtain ⟨b₁, b₂, hb₁, hb₂, hdisj⟩ := harcs a ha
  have hqa₁ : a < q₁ := ha.trans_le (min_le_left _ _)
  have hqa₂ : a < q₂ := ha.trans_le (min_le_right _ _)
  obtain ⟨hJ, hH⟩ := compactBoundary_jordan
    (neg_neg_of_pos (inv_pos.2 (sub_pos.2 hqa₁)))
    (neg_neg_of_pos (inv_pos.2 (sub_pos.2 hqa₂)))
    hb₁.1 hb₂.1 hb₁.2.1 hb₂.2.1 hb₁.2.2.1 hb₂.2.2.1
    hb₁.2.2.2.1 hb₂.2.2.2.1 hb₁.2.2.2.2.1 hb₂.2.2.2.2.1 hdisj
  have hzero := zero_mem_compactBoundary (b₂ := b₂)
    (x₁ := -(q₁ - a)⁻¹) (x₂ := -(q₂ - a)⁻¹) hb₁.2.2.2.1
  have hbd := compactBoundary_mem_frontier hC hη hW hW0 hτ0 hτs hτ hb₁ hb₂
  refine ⟨b₁, b₂, hb₁, hb₂, hJ, hH, hzero, hbd, ?_⟩
  intro hsides
  exact infiniteFaceChart_of_sides hη hW hW0 (hτ0.trans hτs) hC.isOpen hJ hH hzero
    (fun ζ hζ hζH hζC => (hC.isOpen.frontier_eq ▸ hbd ζ hζ hζH).2 hζC) hsides

/-- A compactified Jordan face boundary exists at every chart time after the
entrance. Only the explicitly named interior side selection remains. -/
theorem exists_pocket_compact_face {W : ℝ → ℝ} {η A₁ A₂ : ℝ → ℂ}
    {C : Set ℂ} {τ s : ℝ}
    (hC : IsCfPocketInf C A₁ A₂)
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hτ0 : 0 ≤ τ) (hτs : τ ≤ s) (hτ : η τ = A₁ 0) :
    ∃ (a : ℝ) (Γ : Set ℂ), LQGMetric.JordanMap.IsJordanCurve Γ ∧ Γ ⊆ Hbar ∧
      (0 : ℂ) ∈ Γ ∧
      (∀ ζ ∈ Γ, ζ ∈ H → trMap W 0 s (psiMapInv a ζ) ∈ frontier C) ∧
      (InfiniteFaceSides W C s a Γ → ∃ q : ℂ, R7EndFace.InfiniteFaceChart W C s a Γ q) := by
  obtain ⟨q₁, q₂, hq⟩ := exists_pocket_chart_reduction hC hη hW hW0 hτ0 hτs hτ
  obtain ⟨b₁, b₂, -, -, hJ, hH, hzero, hbd, hchart⟩ := hq (min q₁ q₂ - 1) (by linarith)
  exact ⟨_, _, hJ, hH, hzero, hbd, hchart⟩

end InteractingSLE.Sec7.R7InfinityChart
