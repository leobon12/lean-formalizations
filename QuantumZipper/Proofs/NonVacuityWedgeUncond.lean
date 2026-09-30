import QuantumZipper.Proofs.NonVacuityWedge
import QuantumZipper.Proofs.LQG.LogSingGood

/-!
# Non-vacuity of `IsQuantumWedge` with a probability reference law, unconditionally

`NonVacuityWedge.lean` proves that the reference law of a quantum wedge is a probability measure
(`WedgeMeas.isProbabilityMeasure_fieldLawFull_wedgeRef`) **conditionally on**
`NonVacuity.WedgeRefGoodAS γ α`, the statement that the reference wedge field is a.s.
`IsLQGGood`. That hypothesis is now a theorem: `LogSingGood.wedgeRefGoodAS_holds` proves it for
`0 < γ < 2` and `α < Qc γ` (route: the free field plus the boundary log singularity
`α(−log‖·‖)` is a.s. good, `LogSingGood.logSingGoodAS_holds`, which is M4-P4 of the blueprint
with the offsets of `IsLQGGood`; then a coupling with the radial process, `WedgeGood.lean`).

This file removes the hypothesis: every result of `NonVacuityWedge.lean` is restated with
`(hG : WedgeRefGoodAS γ α)` replaced by the parameter conditions `0 < γ`, `γ < 2`, `α < Qc γ`,
and proved by applying the conditional statement to `wedgeRefGoodAS_holds`.

There is nothing to prove beyond that substitution: each `_uncond` theorem is the corresponding
conditional theorem applied to `LogSingGood.wedgeRefGoodAS_holds hγ hγ2 hα`. No statement from
`NonVacuityWedge.lean` is changed, and no new hypothesis is introduced
(`0 < γ`, `γ < 2`, `α < Qc γ` are exactly the hypotheses of `wedgeRefGoodAS_holds`; the
parameter ranges are those of blueprint M4-P4, `0 < γ < 2` and `α < Q`).

`Proofs/LQG/WedgeGood.lean` has no result taking `WedgeRefGoodAS` as a hypothesis — its only
`WedgeRefGoodAS` consumer-facing theorem is `wedgeRefGoodAS_of_logSing`, which *produces* it from
`LogSingGoodAS` — so there is nothing to de-condition there.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace QuantumZipper

namespace NonVacuity

/-- **`isProbabilityMeasure_fieldLawFull_of_isQuantumWedge`, unconditional.** For `0 < γ < 2`
and `α < Qc γ`, every quantum wedge has a probability law through its full coordinates. -/
theorem isProbabilityMeasure_fieldLawFull_of_isQuantumWedge_uncond {γ α : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < Qc γ) {Ω : Type*} [MeasurableSpace Ω]
    {Y : Ω → FieldSample} {P : Measure Ω} (h : IsQuantumWedge γ α Y P) :
    IsProbabilityMeasure (fieldLawFull H Y P) :=
  isProbabilityMeasure_fieldLawFull_of_isQuantumWedge
    (QuantumZipper.LogSingGood.wedgeRefGoodAS_holds hγ hγ2 hα) h

/-- **`exists_wedge_indep_BM_uncond_prob`, unconditional.** For `0 < γ < 2` and `α < Qc γ`
there is a quantum wedge, independent of a Brownian motion, whose full-coordinate law is a
probability measure. -/
theorem exists_wedge_indep_BM_uncond_prob_uncond {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α < Qc γ) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (Y : Ω → FieldSample)
      (B : ℝ≥0 → Ω → ℝ), IsProbabilityMeasure P ∧ IsQuantumWedge γ α Y P ∧
        IsProbabilityMeasure (fieldLawFull H Y P) ∧ IsBrownianReal B P ∧
        IndepFun (pathOf B) Y P :=
  exists_wedge_indep_BM_uncond_prob hα
    (QuantumZipper.LogSingGood.wedgeRefGoodAS_holds hγ hγ2 hα)

end NonVacuity

end QuantumZipper
