/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW0

/-!
# Theorem BR6: the exact boundary-hitting characterization (statement)

Packet PROVE-T14-GW3. Supplement §24, **Theorem BR6** (`source/spec/p577-624.md` L806–L813, p. 610):

> For the canonical finite-force law with `k > 4` and `z > 0`, the first visit to `z` is almost surely finite,
> including a possible finite terminal value, if and only if all three conditions hold:
> 1. Every original left cumulative sum, including the seed group, is greater than `−2`.
> 2. Every original right cumulative sum at a mark strictly before `z`, including the seed group, is greater than `−2`.
> 3. Every original right interval meeting `(z, ∞)` has cumulative sum at most `d = k/2 − 4`.
>
> A group exactly at `z` may be inadmissible. It then gives the original terminal hit. The reflected statement holds
> for `z < 0`.

BR6 is used by BW2 (the forced low boundary arc, "Reflected BR6 therefore forces a finite visit to `w`") and by GW2a's
connectors ("BR6 forces the entire connector"). Its proof (L815–L820) is BR3 and BR5 (necessity) and the retargeted
word of BR2 with reflected GB5 and inverse Aux. 10 (sufficiency); none of it is formalized here. This file fixes the
exact statement (`BR6Statement`) so that consumers can be stated against it.

**Reading of the statement.**
* "the canonical finite-force law": an integrated `SLE_k(ρ)` evolution of an ordered finite force word (frozen
  `IsIntegratedSLEEvolution`), with a generating trace `η` (Theorem 1.3; a process `η` that generates the driver up
  to and including a finite lifetime almost surely is quantified universally, generating traces being unique);
* "the first visit to `z` is finite, including a possible finite terminal value": some finite time `t ≤ ζ` has
  `η(t) = z` (a generating trace is continuous on `[0, ζ]`, so at a finite lifetime its value there is the terminal
  value);
* "cumulative sum" of a side at a group: the partial sum of the weights up to that group's end (Lean labels with
  coincident positions form one group; `GW0.LeftGroupEndsAdmissible` for condition 1);
* condition 3: the right intervals are `(p, p⁺)` for `p = 0` and every right position `p`, `p⁺` the next larger right
  position (`∞` if none); such an interval meets `(z, ∞)` iff every right position is `≤ p` or `> z`; its cumulative
  sum is the weight of the right marks at positions `≤ p`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Finset
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Theorem14

namespace BR6

/-- Condition 2 of BR6: every right group end strictly before `z` has partial sum `> −2`. -/
def RightAdmissibleBefore {nR : ℕ} (xR ρR : Fin nR → ℝ) (z : ℝ) : Prop :=
  ∀ m : Fin nR, (∀ i, m < i → xR m < xR i) → xR m < z → -2 < ∑ i ∈ univ.filter (· ≤ m), ρR i

/-- Condition 3 of BR6: every right interval `(p, p⁺)` meeting `(z, ∞)` (with `p = 0` or a right position) has
cumulative weight at most `d = k/2 − 4`. -/
def RightLowBeyond (k : ℝ) {nR : ℕ} (xR ρR : Fin nR → ℝ) (z : ℝ) : Prop :=
  ∀ p : ℝ, (p = 0 ∨ ∃ i, xR i = p) → (∀ i, xR i ≤ p ∨ z < xR i) →
    ∑ i ∈ univ.filter (fun i => xR i ≤ p), ρR i ≤ k / 2 - 4

/-- **Named statement: Theorem BR6** (supplement p. 610). For `k > 4`, `z > 0` and an ordered finite force word,
an integrated `SLE_k(ρ)` evolution with a generating trace `η` (up to and including a finite lifetime) visits `z` at a
finite time almost surely iff the left group ends are admissible (condition 1), the right group ends strictly before
`z` are admissible (condition 2), and the right intervals meeting `(z, ∞)` have cumulative weight `≤ k/2 − 4`
(condition 3). -/
def BR6Statement : Prop :=
  ∀ (k : ℝ), 4 < k → ∀ {nL nR : ℕ} (xL : Fin nL → ℝ) (xR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (z : ℝ), 0 < z → IsOrderedForceWord xL xR →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ)
      (W : ℝ≥0 → Ω → ℝ) (VL : Fin nL → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ)
      (ζ : Ω → ℝ≥0∞) (η : Ω → ℝ≥0 → ℂ),
      IsIntegratedSLEEvolution k xL xR ρL ρR P 𝓕 W VL VR B ζ →
      (∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) (ζ ω) (η ω)) →
      ((∀ᵐ ω ∂P, ∃ t : ℝ≥0, (t : ℝ≥0∞) ≤ ζ ω ∧ η ω t = z) ↔
        GW0.LeftGroupEndsAdmissible xL ρL ∧ RightAdmissibleBefore xR ρR z ∧ RightLowBeyond k xR ρR z)

end BR6

end Theorem14

end InteractingSLE
