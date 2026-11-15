/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Foundations.Strip.SLE

/-!
# Zhan's strip endpoint theorem: the exact statement

Packet PROVE-ZHAN-A. Astra, *Formalization proofs and dependency audit* §3 (ii)
(`source/external/AstraIG1/ig1_formalization_proofs.txt` L928–L946; [Zha10, Theorems 4.1 and 7.6]):

> Use `S_π = {0 < Im z < π}` and normalization `∂_t ψ_t(z) = coth((ψ_t(z) − ξ_t)/2)`. Take finitely many separated
> lower force marks on each side, weights `ρ±j`, and endpoint weights `τ±` at `±∞`. There are no finite upper marks
> in this interface. Put `s± = Σ_j ρ±j`, `q± = s± + τ±`. Assume
> `q₊ + q₋ = κ − 6`, `Σ_{i ≤ j} ρ±i ≥ κ/2 − 2`, `|q₊ − q₋| < 2`.                                        (3.3)
> Then the strip evolution is defined at every finite strip time and its trace has an actual limit at one finite
> point of `ℝ + iπ`.

In the R36 form (`Foundations/Strip/SLE.lean`) the strip evolution is the chordal evolution of the exponential image
`z ↦ e^z − 1`, with `τ₊` the target charge (so `q₊ + q₋ = κ − 6` holds by construction, `chargePlus_add_chargeMinus`).
Then:

* "defined at every finite strip time": the strip clock `t(s) = ∫₀ˢ (W − v)⁻²` is unbounded on the strip life
  (`IsStripLife`: chordal times before `ζ` with the end mark `v` still strictly left of the driver);
* "its trace": a continuous generating chordal trace on the strip life exists;
* "an actual limit at one finite point of `ℝ + iπ`": every such trace converges, along the strip life, to a point
  `x < −1` of the chordal image `(−∞, −1)` of the upper line (strip point `log(1 + x) = log(−1 − x) + iπ`).

`StripEndpointStatement κ` is this statement (the theorem to be proved; consumers that need it before it is proved
take it as a named hypothesis).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Strip

variable {nL nR : ℕ}

/-- The lower-prefix condition of (3.3): every nonempty prefix of the lower weights on each side (counted from the
source outwards) sums to at least `κ/2 − 2`. -/
def HasStripPrefixSums (κ : ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) : Prop :=
  (∀ j : Fin nL, κ / 2 - 2 ≤ ∑ i ∈ Finset.Iic j, ρL i) ∧ ∀ j : Fin nR, κ / 2 - 2 ≤ ∑ i ∈ Finset.Iic j, ρR i

/-- The conclusion of the strip endpoint theorem for one path: the strip clock is unbounded on the strip life, a
continuous generating chordal trace on the strip life exists, and every such trace converges along the strip life
to a point `x < −1` (the chordal image of a finite point of `ℝ + iπ`). -/
def HasStripEndpoint (w v : ℝ≥0 → ℝ) (ζ : ℝ≥0∞) : Prop :=
  (∀ T : ℝ, ∃ s : ℝ≥0, IsStripLife w v ζ s ∧ T ≤ stripClock (extPath w) (extPath v) s) ∧
  (∃ η : ℝ≥0 → ℂ, ∀ s : ℝ≥0, IsStripLife w v ζ s → IsGeneratingTrace w s η) ∧
  ∀ η : ℝ≥0 → ℂ, (∀ s : ℝ≥0, IsStripLife w v ζ s → IsGeneratingTrace w s η) →
    ∃ x : ℝ, x < -1 ∧ ∀ ε > 0, ∃ s₀ : ℝ≥0, IsStripLife w v ζ s₀ ∧
      ∀ s : ℝ≥0, s₀ ≤ s → IsStripLife w v ζ s → ‖η s - x‖ < ε

/-- **Zhan's strip endpoint theorem** (Astra §3 (ii), (3.3); [Zha10, Theorems 4.1, 7.6]) for the parameter `κ`, in
the R36 form. -/
def StripEndpointStatement (κ : ℝ) : Prop :=
  ∀ {nL nR : ℕ} (pL : Fin nL → ℝ) (pR : Fin nR → ℝ) (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ) (τm : ℝ)
    {Ω : Type u} {mΩ : MeasurableSpace Ω} (P : Measure Ω) (𝓕 : MeasureTheory.Filtration ℝ≥0 mΩ)
    (W : ℝ≥0 → Ω → ℝ) (VL : Fin (nL + 1) → ℝ≥0 → Ω → ℝ) (VR : Fin nR → ℝ≥0 → Ω → ℝ)
    (B : ℝ≥0 → Ω → ℝ) (ζ : Ω → ℝ≥0∞),
    IsSeparatedStripWord pL pR → HasStripPrefixSums κ ρL ρR →
      |chargePlus κ ρL ρR τm - chargeMinus ρL τm| < 2 →
      IsStripSLEEvolution κ pL pR ρL ρR τm P 𝓕 W VL VR B ζ →
        ∀ᵐ ω ∂P, HasStripEndpoint (W · ω) (VL (Fin.last nL) · ω) (ζ ω)

end Strip

end InteractingSLE
