/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.Collar

/-!
# Zhan's A.2: the exact Lean form of the crosscut assertion for the (G3) configuration

Packet PROVE-ZHAN-GT4-A14. Source: Astra, *Follow-up proofs*, §A.2 (`ig1_followup_proofs.txt` L511–L637) and its use
in §A.3.2 (L694–L705, R38): "For (G3) apply §A.2 with `x₁ = y, x₂ = 0, p₁ = y⁻, p₂ = ∞, p₃ = y⁺, p₄ = x`,
`C₁ = (κ − 6)/(κ − 4), C₂ = 2/(κ − 4), C₃ = −1/2, C₄ = 1`. … Each mixture component therefore has a crosscut outer
boundary from `y < x` to a positive point."

A.2 (L519–L521): "Let `S` be the closure of the union of [the large curve's] hulls before its first force collision. Its
outer boundary in `ℍ` is a simple crosscut from `x₁` to a point in `(x₂, p₂)`." In the (G3) configuration the large
curve is the integrated `SLE_κ(κ − 4, −4)` evolution from `(0; x, y)`, `y < x < 0` (its charges at `y⁻, y, y⁺`
amalgamate to `−4`, `OuterBoundary.firstSwallow_mid_amalgamate`; the mark at infinity has no drift), its lifetime is
the first force collision, `x₁ = y`, `x₂ = 0`, `p₂ = ∞`.

This file fixes the Lean form consumed by PROVE-ZHAN-A33 (`FirstSwallowCrosscutStatement` from the mixture (G3)):

* `unbddPart S`: the part of `ℍ \ S` reachable from infinity (the union of its unbounded preconnected subsets);
* `outerBoundary S = frontier (unbddPart S) ∩ ℍ`;
* **`FourForceCrosscutG3Statement κ`**: for `4 < κ < 8`, `y < x < 0` and every integrated
  `SLE_κ(κ − 4, −4)` evolution from `(0; x, y)` (left marks nearest first), almost surely the outer boundary of the
  closure of its terminal hull is `γ((0, 1))` for a simple real crosscut `γ` from `y` to a positive point.

Only the crosscut assertion of A.2 is stated (the law of the crosscut, "it has the law of the small-parameter curve",
is not used by A.3 and is not part of this statement). The proof of A.2 needs the dual coupling of A.1
(PROVE-ZHAN-GT4-A8…A14, in progress).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.ZhanGT4

open QuantumZipper (H)

/-- **The part of `ℍ \ S` reachable from infinity**: the union of the unbounded preconnected subsets of `ℍ \ S`
(for a bounded `S`, the unbounded component of `ℍ \ S`). -/
def unbddPart (S : Set ℂ) : Set ℂ :=
  ⋃₀ {U : Set ℂ | IsPreconnected U ∧ U ⊆ H \ S ∧ ¬ Bornology.IsBounded U}

/-- **The outer boundary of `S` in `ℍ`**: the frontier of the part of `ℍ \ S` reachable from infinity, inside `ℍ`. -/
def outerBoundary (S : Set ℂ) : Set ℂ := frontier (unbddPart S) ∩ H

theorem unbddPart_subset (S : Set ℂ) : unbddPart S ⊆ H \ S :=
  Set.sUnion_subset fun _ hU => hU.2.1

theorem outerBoundary_subset_H (S : Set ℂ) : outerBoundary S ⊆ H := Set.inter_subset_right

/-- **A.2's crosscut assertion in the (G3) configuration** (§A.2 L519–L521, applied in §A.3.2 L694–L705). For
`4 < κ < 8`, marks `y < x < 0` and every integrated `SLE_κ(κ − 4, −4)` evolution from `(0; x, y)` (left marks nearest
first, weights `κ − 4` at `x` and `−4` at `y`), almost surely the outer boundary in `ℍ` of the closure `S` of the union of
its hulls before its lifetime (the first force collision) is `γ((0, 1))` for a simple crosscut `γ` with real endpoints
`γ(0) = y` and `γ(1) > 0`. -/
def FourForceCrosscutG3Statement (κ : ℝ) : Prop :=
  4 < κ → κ < 8 → ∀ (y x : ℝ), y < x → x < 0 →
    ∀ {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
      (𝓕 : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ) (VL : Fin 2 → ℝ≥0 → Ω → ℝ)
      (VR : Fin 0 → ℝ≥0 → Ω → ℝ) (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
      IsIntegratedSLEEvolution κ ![x, y] ![] ![κ - 4, -4] ![] P 𝓕 W VL VR B ζ →
        ∀ᵐ ω ∂P, ∃ γ : ℝ → ℂ, IsRealCrosscut γ ∧ (γ 0).re = y ∧ 0 < (γ 1).re ∧
          outerBoundary (closure (terminalHull (fun t => W t ω) (ζ ω))) = γ '' Ioo 0 1

end InteractingSLE.ZhanGT4
