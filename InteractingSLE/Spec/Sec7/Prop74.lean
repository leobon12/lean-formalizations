/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Frozen.Spec.IsFlowLine
import InteractingSLE.Frozen.Spec.IsGFFWithBoundaryData
import InteractingSLE.Frozen.Spec.HasOrderedProperCompletions
import InteractingSLE.Frozen.Spec.sleLambda
import InteractingSLE.Frozen.Spec.IsPiecewiseConstantBoundaryData

/-!
# Proposition 7.4: monotonicity of two flow lines from a common seed (the ordering clause)

Packet PROVE-AUX97. Source: Proposition 7.4 (`source/spec/p241-288.md` L56–L64, p. 244).

**Proposition 7.4.** "Suppose that `h` is a GFF on `ℍ` with boundary data as in the left side of Figure 7.1 (though
we do not restrict the values of `a` and `b`). Assume `θ₁ < θ₂` satisfy `θ₁ > −(λ + b)/χ` and `θ₂ < (a + λ)/χ`. With
`η_{θᵢ}` the flow line of `h` with angle `θᵢ` for `i = 1, 2`, we have that `η_{θ₂}` almost surely lies to the left of
`η_{θ₁}`. The conditional law of `η_{θ₁}` given `η_{θ₂}` is that of an `SLE_κ((θ₂ − θ₁)χ/λ − 2; (b + θ₁χ)/λ − 1)`
independently in each of the connected components of `ℍ ∖ η_{θ₂}` which lie to the right of `η_{θ₂}`. Similarly, …"

The boundary data of Figure 7.1 (left) is `−a` on `(−∞, 0)` and `b` on `(0, ∞)` (the seed weights of the angle-`θ` flow
line are then `ρ^L = (a − θχ)/λ − 1` and `ρ^R = (b + θχ)/λ − 1`, matching the two conditional laws above). The two
hypotheses on the angles say exactly that the right seed weight of `η_{θ₁}` and the left seed weight of `η_{θ₂}` exceed
`−2` ("The hypothesis on `θ₁, θ₂` is to ensure that the values of the weights … exceed `−2`"; the weight remark is
`Sec7.prop74_weights_iff`).

* `prop74Data a b`: the boundary data `−a` on `(−∞, 0)`, `b` on `[0, ∞)` (the value at the jump `0` is never read);
* **`Prop74OrderStatement`** (named input): the first assertion of Proposition 7.4 — the ordering — in the W0
  convention of the frozen Theorem 1.5 (`IsFlowLine.stays_right_of_lt`): almost surely every pair of finite prefixes
  strictly before the lifetimes has ordered proper completions, `η_{θ₂}` on the closed left side. The source's
  whole-curve assertion implies it (the two flow lines are complete continuous simple proper curves, Proposition 7.3,
  and each complete curve is its own proper completion of each of its prefixes). The two conditional-law assertions of
  Proposition 7.4 are not part of this statement (W5 and Aux. lemma 97 use only the ordering).

**Not proved here.** Its proof ("applying the same component-pair construction simultaneously to finitely many middle
flow lines", p. 243) needs Lemma 7.1's embedded three-curve coupling (Proposition 5.5, Remark 6.14, Remark 6.7,
Proposition 6.5, Aux. lemmas 33 and 93) and the two-seed field determination (Proposition 7.3, Lemma 7.2), none of which
is in Lean (`planning/handoffs/PROVE-SEC7-A3.md`, `PROVE-SEC7-A4.md`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Sec7

/-- The boundary data of Figure 7.1 (left): `−a` on `(−∞, 0)` and `b` on `[0, ∞)`, with jump candidate `0`. -/
def prop74Data (a b : ℝ) : ℝ → ℝ := fun y => if y < 0 then -a else b

/-- The data of Figure 7.1 is finite piecewise-constant data with the single jump candidate `0`. -/
theorem isPiecewiseConstant_prop74Data (a b : ℝ) : IsPiecewiseConstantBoundaryData (prop74Data a b) {0} := by
  intro y hy
  rw [Finset.mem_singleton] at hy
  rcases lt_or_gt_of_ne hy with hy | hy
  · filter_upwards [Iio_mem_nhds hy] with z hz
    simp only [prop74Data, show z < 0 from hz, hy, ↓reduceIte]
  · filter_upwards [Ioi_mem_nhds hy] with z hz
    simp only [prop74Data, not_lt.2 (le_of_lt (show 0 < z from hz)), not_lt.2 hy.le, ↓reduceIte]

/-- **Named input: Proposition 7.4, the ordering clause** (p. 244): for `0 < κ < 4`, the GFF `h` on `ℍ` with boundary
data `−a` on `ℝ₋`, `b` on `ℝ₊`, and angles `θ₁ < θ₂` with `−(λ + b)/χ < θ₁` and `θ₂ < (a + λ)/χ`, the flow line
`η_{θ₂}` almost surely lies to the left of `η_{θ₁}`, in the W0 sense of the frozen Theorem 1.5: every pair of finite
prefixes strictly before the lifetimes has ordered proper completions. Implied by the source's whole-curve statement
(see the module docstring). -/
def Prop74OrderStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ a b θ₁ θ₂ : ℝ, θ₁ < θ₂ →
    -(sleLambda κ + b) / QuantumZipper.chiC κ < θ₁ → θ₂ < (a + sleLambda κ) / QuantumZipper.chiC κ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → LQGMetric.DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h (prop74Data a b) {0} →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ (prop74Data a b) {0} 0 θ₁ P h η₁ ζ₁ → IsFlowLine κ (prop74Data a b) {0} 0 θ₂ P h η₂ ζ₂ →
      ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, (s : ℝ≥0∞) < ζ₁ ω → (t : ℝ≥0∞) < ζ₂ ω →
        HasOrderedProperCompletions (η₁ ω) s (η₂ ω) t

end Sec7

end InteractingSLE
