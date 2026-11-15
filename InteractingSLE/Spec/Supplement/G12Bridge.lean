/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.G12Core
import InteractingSLE.Spec.Supplement.G12Statement

/-!
# Lemma G12: the proved cases and the exact remainder

Packet PROVE-G12. `Supp7.G12EvolStatement` (PROVE-W5-REST2) is Lemma G12 for every ordered force word and every real
point `y ≠ 0`. `G12Core.lean` proves it when `y` is a mark beyond another mark on its side, the cumulative weight
strictly before `y` exceeds `−2`, and the weights beyond `y` on its side are `≥ 0`. This file isolates the cases that
are **not** proved as one named proposition, `G12RemainderStatement` (a conditional input, not a source theorem), and
derives the source form from it:

* `G12RemainderStatement`: the non-visit of `y` in the remaining cases (`y` not a mark, or no mark strictly before it
  on its side, or the weight strictly before `y` is `≤ −2`, or a negative weight beyond `y`);
* `g12EvolStatement_of_remainder : G12RemainderStatement → G12EvolStatement`.

The mathematical status of the remainder is recorded in `planning/handoffs/PROVE-G12.md` ("What remains").
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Supp7

namespace G12

/-- The right-side cases proved in `G12Core.lean`. -/
def RightCovered {nR : ℕ} (xR ρR : Fin nR → ℝ) (y : ℝ) : Prop :=
  ∃ i₀ j₀ : Fin nR, xR j₀ = y ∧ (∀ k, i₀ ≤ k) ∧ xR i₀ < y ∧
    -2 < ∑ k ∈ univ.filter (fun k => xR k < y), ρR k ∧ ∀ k, y < xR k → 0 ≤ ρR k

/-- The left-side cases proved in `G12Core.lean`. -/
def LeftCovered {nL : ℕ} (xL ρL : Fin nL → ℝ) (y : ℝ) : Prop :=
  ∃ i₀ j₀ : Fin nL, xL j₀ = y ∧ (∀ k, i₀ ≤ k) ∧ y < xL i₀ ∧
    -2 < ∑ k ∈ univ.filter (fun k => y < xL k), ρL k ∧ ∀ k, xL k < y → 0 ≤ ρL k

/-- **The remainder of Lemma G12** (not proved): `Supp7.G12EvolStatement` restricted to the points that are not covered
by `ae_trace_ne_right` / `ae_trace_ne_left`. -/
def G12RemainderStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ), IsOrderedForceWord xL xR →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
      (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ →
    ∀ η : Ω → ℝ≥0 → ℂ, (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (η ω)) →
    ∀ y : ℝ,
      (0 < y → κ / 2 - 4 < ∑ i ∈ univ.filter (fun i => xR i ≤ y), ρR i → ¬ RightCovered xR ρR y →
        ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → η ω t ≠ y) ∧
      (y < 0 → κ / 2 - 4 < ∑ i ∈ univ.filter (fun i => y ≤ xL i), ρL i → ¬ LeftCovered xL ρL y →
        ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → η ω t ≠ y)

/-- **Lemma G12 in the source's form from its remainder.** -/
theorem g12EvolStatement_of_remainder (h : G12RemainderStatement.{u}) : G12EvolStatement.{u} := by
  intro κ hκ hκ4 nL nR xL xR ρL ρR hord Ω mΩ P _ 𝓕 W VL VR B ζ hE η hη y
  refine ⟨fun hy hS => ?_, fun hy hS => ?_⟩
  · by_cases hc : RightCovered xR ρR y
    · obtain ⟨i₀, j₀, hj, hi₀, hx, hS', hfar⟩ := hc
      subst hj
      exact ae_trace_ne_right hκ hord hE hη hi₀ hx hS' hS hfar
    · exact (h κ hκ hκ4 xL xR ρL ρR hord P 𝓕 W VL VR B ζ hE η hη y).1 hy hS hc
  · by_cases hc : LeftCovered xL ρL y
    · obtain ⟨i₀, j₀, hj, hi₀, hx, hS', hfar⟩ := hc
      subst hj
      exact ae_trace_ne_left hκ hord hE hη hi₀ hx hS' hS hfar
    · exact (h κ hκ hκ4 xL xR ρL ρR hord P 𝓕 W VL VR B ζ hE η hη y).2 hy hS hc

end G12

end Supp7

end InteractingSLE
