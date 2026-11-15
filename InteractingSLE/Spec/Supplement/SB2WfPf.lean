/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2WfJt
import InteractingSLE.Spec.Supplement.G12Statement

/-!
# The forbidden set of a piece

Packet PROVE-T14-SB2WORD (round 3, the junction fact of E7). For a word `β` and the walk angle `θ`, `forb κ θ β` is the
set of real points a launched piece does not visit before its stop (almost surely): right of `0` the points of right
weight `≤ −2` (bad points, `Vr.trace_ne_of_bad`); left of `0` the jumps (G12, or bad) and the points of left weight
`≥ κ/2 − 2` (GB7a). Avoiding it gives the touch hypotheses `hRT`, `hLT` of `jw_walk_step` (`hRT_of_avoid`,
`hLT_of_avoid`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (H Hbar chiC)

namespace InteractingSLE.Theorem14.SB.Wf

open Exist Exist.StagedLaw Exist.Staged Restart GW1W
open PiecewiseConstantBoundaryData (rightLim leftLim)

/-- **The forbidden set of a piece with word `β`** (walk angle `θ`). -/
def forb (κ θ : ℝ) (β : BoundaryWord) : Set ℂ :=
  {z | z.im = 0 ∧ ((0 < z.re ∧ Sec4.cumWeightRight κ (rightLim β.fn z.re + θ * chiC κ) ≤ -2) ∨
    (z.re < 0 ∧ (z.re ∈ β.jumps ∨ κ / 2 - 2 ≤ Sec4.cumWeightLeft κ (β.fn z.re + θ * chiC κ))))}

variable {κ θ : ℝ} {β : BoundaryWord} {γ : ℝ → ℂ} {τ : ℝ}

theorem hRT_of_avoid (havoid : ∀ t₀ : ℝ, 0 ≤ t₀ → t₀ < τ → γ t₀ ∉ forb κ θ β) :
    ∀ t₀ : ℝ, 0 ≤ t₀ → t₀ < τ → (γ t₀).im = 0 → 0 < (γ t₀).re →
      -2 < Sec4.cumWeightRight κ (rightLim β.fn (γ t₀).re + θ * chiC κ) := by
  intro t₀ ht₀ ht₀τ him hpos
  by_contra hle
  push Not at hle
  exact havoid t₀ ht₀ ht₀τ ⟨him, Or.inl ⟨hpos, hle⟩⟩

theorem hLT_of_avoid (havoid : ∀ t₀ : ℝ, 0 ≤ t₀ → t₀ < τ → γ t₀ ∉ forb κ θ β) :
    ∀ t₀ : ℝ, 0 ≤ t₀ → t₀ < τ → (γ t₀).im = 0 → (γ t₀).re < 0 →
      ∃ a a' v : ℝ, a < (γ t₀).re ∧ (γ t₀).re < a' ∧ (∀ y ∈ Ioo a a', y ∉ β.jumps → β.fn y = v) ∧
        Sec4.cumWeightLeft κ (v + θ * chiC κ) < κ / 2 - 2 := by
  intro t₀ ht₀ ht₀τ him hneg
  set z := (γ t₀).re with hz
  have hzJ : z ∉ β.jumps := fun h => havoid t₀ ht₀ ht₀τ ⟨him, Or.inr ⟨hneg, Or.inl h⟩⟩
  have hlow : Sec4.cumWeightLeft κ (β.fn z + θ * chiC κ) < κ / 2 - 2 := by
    by_contra hle
    push Not at hle
    exact havoid t₀ ht₀ ht₀τ ⟨him, Or.inr ⟨hneg, Or.inr hle⟩⟩
  obtain ⟨δ, hδ, hδJ⟩ := Supp7.exists_pos_forall_notMem β.jumps z
  have hJ : ∀ w ∈ β.jumps, w ∉ Ioo (z - δ) (z + δ) := by
    intro w hw hwI
    rcases lt_trichotomy w z with hlt | heq | hgt
    · exact (hδJ w hw).2 ⟨hwI.1, hlt⟩
    · exact hzJ (heq ▸ hw)
    · exact (hδJ w hw).1 ⟨hgt, by linarith [hwI.2]⟩
  refine ⟨z - δ, z + δ, β.fn z, by linarith, by linarith, fun y hy _ => ?_, hlow⟩
  exact Sec4.eq_of_mem_Ioo_of_isPiecewiseConstant β.isPiecewiseConstantBoundaryData hJ
    ⟨by linarith, by linarith⟩ hy

end InteractingSLE.Theorem14.SB.Wf
