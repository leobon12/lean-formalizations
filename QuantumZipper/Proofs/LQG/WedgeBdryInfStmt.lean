import QuantumZipper.LQG.Measures
import QuantumZipper.GFF.Defs

/-!
# WEDGE-BDRY item 4 (a): statement

`WedgeBdryFreeInfStmt`: for the free boundary GFF modulo constants `X` on `ℍ`, `γ ∈ (0,2)` and
`α'' < Q = Qc γ`, almost surely
`∫_{[1,∞)} t^{−α''γ/2} dν_X(t) = ∞`,
where `ν_X = qBoundaryMeasure γ X`. For `α'' ≤ 0` this is the half-line statement
`ν_X[1,∞) = ∞` (`InfMass.ae_qBoundaryMeasure_Ici_eq_top`); for `α'' ∈ (0,Q)` it is the
weighted form used to show that a quantum wedge has infinite boundary length
(Sheffield, arXiv:1012.4797, §1.6, p. 21; boundary measure as in Duplantier–Sheffield 2011).
The proof is in `WedgeBdryInfA*.lean` (handoff/WEDGE-BDRY.md item 4 (a)).
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace QuantumZipper

namespace WedgeBdry

/-- **WEDGE-BDRY 4 (a).** Weighted infinite boundary mass of the free field on `[1,∞)`. -/
def WedgeBdryFreeInfStmt : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → FieldSample), IsFreeGFFModConstH X P →
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α'' : ℝ, α'' < Qc γ →
    ∀ᵐ ω ∂P, ∫⁻ t in Ici (1 : ℝ), ENNReal.ofReal (t ^ (-(α'' * γ / 2)))
      ∂qBoundaryMeasure γ (X ω) = ⊤

end WedgeBdry

end QuantumZipper
