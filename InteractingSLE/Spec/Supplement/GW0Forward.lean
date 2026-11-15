/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW0

/-!
# Lemma GW0, forward implication: the seed case, and the reduction to a first bad separated group

Packet PROVE-T14-GW2, item (3). Lemma GW0 (supplement p. 617, `source/spec/p577-624.md` L922–L928):

> "For a finite-force word with its indicated integrated continuation rule, the continuation threshold is almost
> surely not hit if and only if every side cumulative group is greater than `−2`. An inadmissible seed gives zero
> available lifetime. If both initial seed groups are admissible, any first inadmissible separated group is reached at
> a finite continuation threshold with positive probability."

The forward implication (`GW0.GW0ForwardStatement`, PROVE-T14-GW) splits along the second and third sentences:

* **an inadmissible seed** (the threshold condition at the initial state) gives zero lifetime on every path
  (`GW0.lifetime_eq_zero_iff`), so the lifetime is not almost surely infinite — proved here
  (`not_ae_lifetime_eq_top_of_threshold`);
* **admissible seeds and an inadmissible later group**: the third sentence, whose proof is the bounded-reference part
  of BR3 (target change at the first bad mark, LP11 and GB5 for the transformed word, a bounded crosscut buffer, and
  Aux. 108's finite-energy cutoff transfer to the original word). It is the named input
  `GW0SeparatedBadGroupStatement` (in the weaker form "the lifetime is finite with positive probability", which is all
  the forward implication uses). It is **not proved here**: see `planning/handoffs/PROVE-T14-GW2.md` for the exact
  missing Lean pieces.

## Main results

* `GW0SeparatedBadGroupStatement` (named input, the third sentence of Lemma GW0);
* `not_ae_lifetime_eq_top_of_threshold` (the second sentence, in the form used);
* **`gw0ForwardStatement_of_separated`**: `GW0SeparatedBadGroupStatement → GW0.GW0ForwardStatement`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Theorem14

namespace GW0

/-- **Named input: Lemma GW0, third sentence** (p. 617: "If both initial seed groups are admissible, any first
inadmissible separated group is reached at a finite continuation threshold with positive probability"), in the weaker
form used by the forward implication: for `k > 4` and an ordered finite force word whose seed groups are admissible
(no threshold at the initial state) but which has an inadmissible side group end, the lifetime of an integrated
`SLE_k(ρ)` evolution is not almost surely infinite. -/
def GW0SeparatedBadGroupStatement : Prop :=
  ∀ (k : ℝ), 4 < k → ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ),
    IsOrderedForceWord xL xR → ¬ ForceWord.ThresholdCondition ρL ρR 0 xL xR →
    ¬ (LeftGroupEndsAdmissible xL ρL ∧ RightGroupEndsAdmissible xR ρR) →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ)
      (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
      (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution k xL xR ρL ρR P 𝓕 W VL VR B ζ → ¬ (∀ᵐ ω ∂P, ζ ω = ⊤)

/-- **Lemma GW0, second sentence** ("An inadmissible seed gives zero available lifetime"), in the form used by the
forward implication: if the initial state satisfies the threshold condition, every path has zero lifetime, so the
lifetime is not almost surely infinite. -/
theorem not_ae_lifetime_eq_top_of_threshold {a : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞}
    (h : IsIntegratedSLEEvolution a xL xR ρL ρR P 𝓕 W VL VR B ζ)
    (hthr : ForceWord.ThresholdCondition ρL ρR 0 xL xR) : ¬ (∀ᵐ ω ∂P, ζ ω = ⊤) := by
  intro htop
  have h0 : ∀ᵐ ω ∂P, ζ ω = 0 := by
    filter_upwards [h.2.2.2.2] with ω hω
    exact (lifetime_eq_zero_iff hω).2 hthr
  obtain ⟨ω, hω0, hωt⟩ := (h0.and htop).exists
  rw [hω0] at hωt
  exact ENNReal.zero_ne_top hωt

/-- **Lemma GW0, forward implication, from its third sentence** (conditional helper with a distinct name): the seed
case is `not_ae_lifetime_eq_top_of_threshold`, the separated case is `GW0SeparatedBadGroupStatement`. -/
theorem gw0ForwardStatement_of_separated (hsep : GW0SeparatedBadGroupStatement.{u}) :
    GW0ForwardStatement.{u} := by
  intro k hk nL nR xL xR ρL ρR hword Ω mΩ P _ 𝓕 W VL VR B ζ h htop
  by_contra hbad
  by_cases hthr : ForceWord.ThresholdCondition ρL ρR 0 xL xR
  · exact not_ae_lifetime_eq_top_of_threshold h hthr htop
  · exact hsep k hk xL xR ρL ρR hword hthr hbad P 𝓕 W VL VR B ζ h htop

end GW0

end Theorem14

end InteractingSLE
