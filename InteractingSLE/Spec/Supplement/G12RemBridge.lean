/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.G12RemPassiveWord
import InteractingSLE.Spec.Supplement.G12Bridge

/-!
# Lemma G12: the proved cases (PROVE-G12B) and the smaller remainder

Packet PROVE-G12B. `Supp7.G12EvolStatement` (Lemma G12, supplement §7.9, p. 504, for every real point `y ≠ 0`) is
now proved whenever, on the side of `y`, some mark lies strictly between the seed and `y` and the cumulative weight
strictly before `y` exceeds `−2`:

* `y` a mark, any weights beyond it: `ae_trace_ne_right_of_near` / `ae_trace_ne_left_of_near` (`G12RemFar.lean`);
* `y` not a mark (a passive point, as W0a uses): `ae_trace_ne_right_of_passive` / `ae_trace_ne_left_of_passive`
  (`G12RemPassiveWord.lean`).

The cases that are **not** proved are isolated as one named proposition, `G12Remainder2Statement` (a conditional
input, not a source theorem; strictly smaller than PROVE-G12's `G12RemainderStatement`):

* `RightCovered2`, `LeftCovered2`: the proved cases;
* `G12Remainder2Statement`: the non-visit of `y` when the cumulative weight strictly before `y` is `≤ −2` (the
  contact-free approach of Lemma G4 / Aux. lemma 132) or no mark lies strictly between the seed and `y`;
* `g12EvolStatement_of_remainder2 : G12Remainder2Statement → G12EvolStatement`, and
  `g12RemainderStatement_of_remainder2` (the older named input follows).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Finset
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Supp7

namespace G12

/-- The right-side cases proved here: a right mark strictly below `y`, and `Σ_{x_k < y} ρ_k > −2`. -/
def RightCovered2 {nR : ℕ} (xR ρR : Fin nR → ℝ) (y : ℝ) : Prop :=
  (∃ i, xR i < y) ∧ -2 < ∑ k ∈ univ.filter (fun k => xR k < y), ρR k

/-- The left-side cases proved here: a left mark strictly above `y`, and `Σ_{y < x_k} ρ_k > −2`. -/
def LeftCovered2 {nL : ℕ} (xL ρL : Fin nL → ℝ) (y : ℝ) : Prop :=
  (∃ i, y < xL i) ∧ -2 < ∑ k ∈ univ.filter (fun k => y < xL k), ρL k

/-- **The remainder of Lemma G12 after PROVE-G12B** (not proved): `Supp7.G12EvolStatement` restricted to the points
not covered by `RightCovered2` / `LeftCovered2`. -/
def G12Remainder2Statement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ)
    (ρR : Fin nR → ℝ), IsOrderedForceWord xL xR →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ)
      (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ →
    ∀ η : Ω → ℝ≥0 → ℂ, (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (η ω)) →
    ∀ y : ℝ,
      (0 < y → κ / 2 - 4 < ∑ i ∈ univ.filter (fun i => xR i ≤ y), ρR i → ¬ RightCovered2 xR ρR y →
        ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → η ω t ≠ y) ∧
      (y < 0 → κ / 2 - 4 < ∑ i ∈ univ.filter (fun i => y ≤ xL i), ρL i → ¬ LeftCovered2 xL ρL y →
        ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → η ω t ≠ y)

section Covered

variable {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ} {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ}
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ}
  {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞}

/-- **Lemma G12 in the right covered cases.** -/
theorem ae_trace_ne_of_rightCovered2 [IsProbabilityMeasure P] (hκ : 0 < κ) (hord : IsOrderedForceWord xL xR)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) {η : Ω → ℝ≥0 → ℂ}
    (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (η ω)) {y : ℝ} (hy : 0 < y)
    (hS : κ / 2 - 4 < ∑ i ∈ univ.filter (fun i => xR i ≤ y), ρR i) (hc : RightCovered2 xR ρR y) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → η ω t ≠ y := by
  obtain ⟨⟨i₁, hi₁⟩, hS'⟩ := hc
  by_cases hmark : ∃ j, xR j = y
  · obtain ⟨j₀, rfl⟩ := hmark
    have hn : 0 < nR := Fin.pos i₁
    set i₀ : Fin nR := ⟨0, hn⟩ with hi₀def
    have hi₀ : ∀ k, i₀ ≤ k := fun k => Fin.mk_le_of_le_val (Nat.zero_le _)
    exact ae_trace_ne_right_of_near (i₀ := i₀) hκ hord hE hη hi₀
      (lt_of_le_of_lt (hord.2.2.1 (hi₀ i₁)) hi₁) hS' hS
  · push Not at hmark
    have h2 : ∑ j ∈ univ.filter (fun j => xR j ≤ y), ρR j = ∑ j ∈ univ.filter (fun j => xR j < y), ρR j :=
      Finset.sum_congr (Finset.filter_congr fun j _ => ⟨fun h => lt_of_le_of_ne h (hmark j), le_of_lt⟩)
        fun _ _ => rfl
    exact ae_trace_ne_right_of_passive hκ hord hE hη hy hmark ⟨i₁, hi₁⟩ hS' (h2 ▸ hS)

/-- **Lemma G12 in the left covered cases.** -/
theorem ae_trace_ne_of_leftCovered2 [IsProbabilityMeasure P] (hκ : 0 < κ) (hord : IsOrderedForceWord xL xR)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) {η : Ω → ℝ≥0 → ℂ}
    (hη : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (η ω)) {y : ℝ} (hy : y < 0)
    (hS : κ / 2 - 4 < ∑ i ∈ univ.filter (fun i => y ≤ xL i), ρL i) (hc : LeftCovered2 xL ρL y) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω → η ω t ≠ y := by
  obtain ⟨⟨i₁, hi₁⟩, hS'⟩ := hc
  by_cases hmark : ∃ j, xL j = y
  · obtain ⟨j₀, rfl⟩ := hmark
    have hn : 0 < nL := Fin.pos i₁
    set i₀ : Fin nL := ⟨0, hn⟩ with hi₀def
    have hi₀ : ∀ k, i₀ ≤ k := fun k => Fin.mk_le_of_le_val (Nat.zero_le _)
    exact ae_trace_ne_left_of_near (i₀ := i₀) hκ hord hE hη hi₀
      (lt_of_lt_of_le hi₁ (hord.1 (hi₀ i₁))) hS' hS
  · push Not at hmark
    have h2 : ∑ j ∈ univ.filter (fun j => y ≤ xL j), ρL j = ∑ j ∈ univ.filter (fun j => y < xL j), ρL j :=
      Finset.sum_congr (Finset.filter_congr fun j _ =>
        ⟨fun h => lt_of_le_of_ne h (fun he => hmark j he.symm), le_of_lt⟩) fun _ _ => rfl
    exact ae_trace_ne_left_of_passive hκ hord hE hη hy hmark ⟨i₁, hi₁⟩ hS' (h2 ▸ hS)

end Covered

/-- **Lemma G12 in the source's form from the smaller remainder.** -/
theorem g12EvolStatement_of_remainder2 (h : G12Remainder2Statement.{u}) : G12EvolStatement.{u} := by
  intro κ hκ hκ4 nL nR xL xR ρL ρR hord Ω mΩ P _ 𝓕 W VL VR B ζ hE η hη y
  refine ⟨fun hy hS => ?_, fun hy hS => ?_⟩
  · by_cases hc : RightCovered2 xR ρR y
    · exact ae_trace_ne_of_rightCovered2 hκ hord hE hη hy hS hc
    · exact (h κ hκ hκ4 xL xR ρL ρR hord P 𝓕 W VL VR B ζ hE η hη y).1 hy hS hc
  · by_cases hc : LeftCovered2 xL ρL y
    · exact ae_trace_ne_of_leftCovered2 hκ hord hE hη hy hS hc
    · exact (h κ hκ hκ4 xL xR ρL ρR hord P 𝓕 W VL VR B ζ hE η hη y).2 hy hS hc

/-- PROVE-G12's named remainder follows from the smaller one. -/
theorem g12RemainderStatement_of_remainder2 (h : G12Remainder2Statement.{u}) : G12RemainderStatement.{u} := by
  intro κ hκ hκ4 nL nR xL xR ρL ρR hord Ω mΩ P _ 𝓕 W VL VR B ζ hE η hη y
  have h' := g12EvolStatement_of_remainder2 h κ hκ hκ4 xL xR ρL ρR hord P 𝓕 W VL VR B ζ hE η hη y
  exact ⟨fun hy hS _ => h'.1 hy hS, fun hy hS _ => h'.2 hy hS⟩

end G12

end Supp7

end InteractingSLE
