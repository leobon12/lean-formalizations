import QuantumZipper.LQG.Wedge

/-!
# Proposition 1.7 (quantum-length stationarity of the γ-wedge)

Sheffield, *Conformal weldings of random surfaces*, Proposition 1.7. Specification only.

Fix `L > 0` and let `(ℍ, h)` be a `γ`-quantum wedge (canonical description). Choose `y > 0`
with `ν_h[0,y] = L` and let `h* = h(· + y)`. Then `(ℍ, h*)` is a `γ`-quantum wedge.

Modelling (STATEMENT_SPEC B5): the paper presupposes that such `y` exists and is unique. We
define `y := inf {y > 0 : ν_h[0,y] ≥ L}` (`wedgeLengthPoint`) and the conclusion also asserts,
almost surely, `ν_h[0,y] = L` and uniqueness among `y' > 0`. `h(· + y)` is `translate h y`
(pairing with `μ` is pairing of `h` with `μ.map (· + y)`). The wedge `(ℍ, h*)` is a doubly
marked quantum surface (marked at `0`, `∞`), so its law is compared through its canonical
description `canonical γ h*`. `γ ∈ (0,2)` as in the paper's conventions.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace QuantumZipper

/-- The point `y > 0` at which the quantum boundary length `ν_x[0,y]` first reaches `L`:
`inf {y > 0 : ν_x[0,y] ≥ L}` (STATEMENT_SPEC B5). -/
noncomputable def wedgeLengthPoint (γ L : ℝ) (x : FieldSample) : ℝ :=
  sInf {y : ℝ | 0 < y ∧ ENNReal.ofReal L ≤ qBoundaryMeasure γ x (Set.Icc 0 y)}

/-- **Proposition 1.7.** Let `Y` be a `γ`-quantum wedge and `L > 0`. Almost surely the point
`y = wedgeLengthPoint γ L Y` satisfies `ν_Y[0,y] = L` and is the unique `y' > 0` with this
property (B5), and the shifted field `Y(· + y)`, in canonical description, is again a
`γ`-quantum wedge. -/
def theorem1_7 : Prop :=
  ∀ (γ L : ℝ), 0 < γ → γ < 2 → 0 < L →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → FieldSample), IsQuantumWedge γ γ Y P →
    (∀ᵐ ω ∂P,
        qBoundaryMeasure γ (Y ω) (Set.Icc 0 (wedgeLengthPoint γ L (Y ω))) = ENNReal.ofReal L ∧
        ∀ y' : ℝ, 0 < y' → qBoundaryMeasure γ (Y ω) (Set.Icc 0 y') = ENNReal.ofReal L →
          y' = wedgeLengthPoint γ L (Y ω)) ∧
    IsQuantumWedge γ γ
      (fun ω => canonical γ (translate (Y ω) (wedgeLengthPoint γ L (Y ω) : ℂ))) P

end QuantumZipper
