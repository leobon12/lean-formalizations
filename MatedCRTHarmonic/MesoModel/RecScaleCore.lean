import MatedCRTHarmonic.GMS3.Theorem14
import MatedCRTHarmonic.CellFamily.Interfaces
import MatedCRTHarmonic.CellFamily.ProducersCellCoupling

/-!
# G4-free source-scale data for mated-CRT recurrence

This core package records the coupled family, its Brownian path and multigraph identification,
and the outer-measure estimate for failure of G3's four Theorem 1.4 inputs. It is intentionally
independent of the in-progress GMS4 modules so the family-to-path bridge can be checked separately.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.MesoModel

open MatedCRTHarmonic

/-- A standard-Borel coupled cell family with polynomial outer-measure failure bounds for all
four inputs of G3's Theorem 1.4 at each dyadic mesh. The standard-Borel witness is needed for
quantitative transfer of arbitrary path-event outer measures through the coupling. -/
def MatedCRTRecurrenceScaleInput (γ : ℝ) : Prop :=
  ∃ (C : CellFamily.MultigraphCoupledRandomFamily γ)
    (_ : StandardBorelSpace C.family.Ω)
    (ρ ρ₁ q β β' α A C27 Cfail : ℝ),
      0 < ρ ∧ ρ < ρ₁ ∧ 0 < β ∧ 3 * β < q ∧ 2 * β < β' ∧ β' ≤ q ∧
      2 * β < α ∧ 0 ≤ A ∧ 0 ≤ C27 ∧ 0 ≤ Cfail ∧
      ∀ k : ℕ,
        C.family.P {ω | ¬ GMS3.Theorem14Inputs (C.family.H k ω)
          (CellFamily.mesh k) ρ ρ₁ q β β' α A} ≤
          ENNReal.ofReal (C27 * CellFamily.mesh k ^ α) +
            ENNReal.ofReal (Cfail * CellFamily.mesh k ^ α) +
            ENNReal.ofReal (Cfail * CellFamily.mesh k ^ α) +
            ENNReal.ofReal (Cfail * CellFamily.mesh k ^ α)

end MatedCRTHarmonic.MesoModel
