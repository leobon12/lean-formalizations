/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R7InfinityChartTail

/-!
# The two compactified incoming arms of an infinite-end pocket

PROVE-R7-GAPEQ. Both arms and their disjoint open parts are constructed from the
original pocket topology, including an outer side with no reverse visit assumption.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Complex Set Metric Filter Topology Bornology
open QuantumZipper (H fwdHull fwdMap)

namespace InteractingSLE.Sec7.R7InfinityChart

open Sec6 PocketJordan

/-- The common real pole can be chosen anywhere left of the two gates. The open
compactified arms are disjoint because their physical tails are disjoint. -/
theorem exists_pocket_compact_arms {W : ℝ → ℝ} {η A₁ A₂ : ℝ → ℂ}
    {C : Set ℂ} {τ s : ℝ}
    (hC : IsCfPocketInf C A₁ A₂)
    (hη : IsLoewnerTrace W η) (hW : Continuous W) (hW0 : W 0 = 0)
    (hτ0 : 0 ≤ τ) (hτs : τ ≤ s) (hτ : η τ = A₁ 0) :
    ∃ q₁ q₂ : ℝ, ∀ a < min q₁ q₂, ∃ b₁ b₂ : ℝ → ℂ,
      IsLastVisitArm W η A₁ s a q₁ b₁ ∧ IsLastVisitArm W η A₂ s a q₂ b₂ ∧
      ∀ w ∈ b₁ '' Ioo 0 1, w ∉ b₂ '' Ioo 0 1 := by
  have hs := hτ0.trans hτs
  have hy₁ : A₁ 0 ∈ η '' Icc 0 s := ⟨τ, ⟨hτ0, hτs⟩, hτ⟩
  have hy₂ : A₂ 0 ∈ η '' Icc 0 s := hC.seed ▸ hy₁
  obtain ⟨q₁, hq₁⟩ := exists_lastVisit_arm hη hW hW0 hs hC.cont₁ hC.inj₁ hC.tendsto₁ hC.mem_H₁ hy₁
  obtain ⟨q₂, hq₂⟩ := exists_lastVisit_arm hη hW hW0 hs hC.cont₂ hC.inj₂ hC.tendsto₂ hC.mem_H₂ hy₂
  obtain ⟨hu₁, -, hD₁⟩ := lastVisit_tail_domain hη hs hC.cont₁ hC.tendsto₁ hC.mem_H₁ hy₁
  obtain ⟨hu₂, -, hD₂⟩ := lastVisit_tail_domain hη hs hC.cont₂ hC.tendsto₂ hC.mem_H₂ hy₂
  refine ⟨q₁, q₂, fun a ha => ?_⟩
  obtain ⟨b₁, hb₁⟩ := hq₁ a (ha.trans_le (min_le_left _ _))
  obtain ⟨b₂, hb₂⟩ := hq₂ a (ha.trans_le (min_le_right _ _))
  refine ⟨b₁, b₂, hb₁, hb₂, ?_⟩
  intro w hw₁ hw₂
  rw [hb₁.2.2.2.2.2.1] at hw₁
  rw [hb₂.2.2.2.2.2.1] at hw₂
  obtain ⟨_, ⟨_, ⟨v, hv, rfl⟩, rfl⟩, rfl⟩ := hw₁
  obtain ⟨_, ⟨_, ⟨v', hv', rfl⟩, rfl⟩, he⟩ := hw₂
  have hphysical := QuantumZipper.FwdHolo.injOn_fwdMap hW hs (hD₂ v' hv') (hD₁ v hv)
    (psiMap_injective he)
  exact hC.sides v (hu₁.trans_lt hv) v' (hu₂.trans_lt hv') hphysical.symm

end InteractingSLE.Sec7.R7InfinityChart
