import QuantumZipper.Proofs.NonVacuity
import QuantumZipper.Proofs.Probability.BMExistence

/-!
# Unconditional non-vacuity of the main hypotheses

The hypotheses of Theorems 1.1–1.5 (a Brownian motion independent of a free or zero-boundary
GFF on `ℍ`) and of Theorem 1.8 (a quantum wedge independent of a Brownian motion) are jointly
satisfiable. This combines `NonVacuity.lean` (which assumed Brownian motion exists) with the
construction of Brownian motion in `Probability/BMExistence.lean`.
-/

namespace QuantumZipper.NonVacuity

open MeasureTheory ProbabilityTheory
open scoped NNReal

/-- A Brownian motion independent of a free-boundary GFF modulo constants exists. -/
theorem exists_BM_indep_freeGFF_uncond :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
      IsProbabilityMeasure P ∧ IsBrownianReal B P ∧ IsFreeGFFModConstH X P ∧
        IndepFun (pathOf B) X P :=
  exists_BM_indep_freeGFF brownianMotionExists

/-- A Brownian motion independent of a zero-boundary GFF exists. -/
theorem exists_BM_indep_zeroGFF_uncond :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
      IsProbabilityMeasure P ∧ IsBrownianReal B P ∧ IsZeroBoundaryGFFH X P ∧
        IndepFun (pathOf B) X P :=
  exists_BM_indep_zeroGFF brownianMotionExists

/-- For `α < Q`, an `α`-quantum wedge independent of a Brownian motion exists. -/
theorem exists_wedge_indep_BM_uncond {γ α : ℝ} (hα : α < Qc γ) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (Y : Ω → FieldSample) (B : ℝ≥0 → Ω → ℝ),
      IsProbabilityMeasure P ∧ IsQuantumWedge γ α Y P ∧ IsBrownianReal B P ∧
        IndepFun (pathOf B) Y P :=
  exists_wedge_indep_BM brownianMotionExists hα

end QuantumZipper.NonVacuity
