import QuantumZipper.Proofs.LQG.WedgeMeasurable
import QuantumZipper.Proofs.NonVacuityFinal

/-!
# Non-vacuity of `IsQuantumWedge` with a probability reference law (AUDIT-2, M1)

`IsQuantumWedge γ α Y P` equates `fieldLawFull H Y P` with the law of the reference field. If the
reference data map were not a.e.-measurable, that law would be `0`. We show that the reference
law is a probability measure (hence so is `fieldLawFull H Y P` for every quantum wedge, and in
particular for the wedge of `exists_wedge_indep_BM_uncond`), **conditionally on**
`WedgeRefGoodAS γ α`: the reference wedge field is a.s. `IsLQGGood`. That statement is not yet
proved in the project (M4-A5 together with boundary/area existence for wedge fields); it is
stated here as an explicit hypothesis, and everything else is proved
(`WedgeMeas.isProbabilityMeasure_fieldLawFull_wedgeRef`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace QuantumZipper

namespace NonVacuity

/-- **Missing input (proposed blueprint item, not proved):** the reference wedge field of
`IsQuantumWedge` is a.s. a good sample. -/
def WedgeRefGoodAS (γ α : ℝ) : Prop :=
  ∀ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (X : Ω' → FieldSample)
    (A : ℝ → Ω' → ℝ), IsProbabilityMeasure P' → IsFreeGFFModConstH X P' →
    IsWedgeProcess α (Qc γ) A P' → IndepFun X (fun ω t => A t ω) P' →
    ∀ᵐ ω ∂P', IsLQGGood γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ))

/-- Every quantum wedge has a probability law through its full coordinates, given
`WedgeRefGoodAS`. -/
theorem isProbabilityMeasure_fieldLawFull_of_isQuantumWedge {γ α : ℝ}
    (hG : WedgeRefGoodAS γ α) {Ω : Type*} [MeasurableSpace Ω] {Y : Ω → FieldSample}
    {P : Measure Ω} (h : IsQuantumWedge γ α Y P) : IsProbabilityMeasure (fieldLawFull H Y P) := by
  obtain ⟨-, Ω', _, P', X, A, hP', hX, hA, hI, hlaw⟩ := h
  rw [hlaw]
  exact WedgeMeas.isProbabilityMeasure_fieldLawFull_wedgeRef hX hA
    (hG Ω' _ P' X A hP' hX hA hI) H

/-- **Strengthened non-vacuity (conditional on `WedgeRefGoodAS`).** The wedge of
`exists_wedge_indep_BM_uncond` also has `IsProbabilityMeasure (fieldLawFull H Y P)`. -/
theorem exists_wedge_indep_BM_uncond_prob {γ α : ℝ} (hα : α < Qc γ) (hG : WedgeRefGoodAS γ α) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (Y : Ω → FieldSample)
      (B : ℝ≥0 → Ω → ℝ), IsProbabilityMeasure P ∧ IsQuantumWedge γ α Y P ∧
        IsProbabilityMeasure (fieldLawFull H Y P) ∧ IsBrownianReal B P ∧
        IndepFun (pathOf B) Y P := by
  obtain ⟨Ω, _, P, Y, B, hP, hW, hB, hI⟩ := exists_wedge_indep_BM_uncond hα
  exact ⟨Ω, _, P, Y, B, hP, hW, isProbabilityMeasure_fieldLawFull_of_isQuantumWedge hG hW, hB, hI⟩

end NonVacuity

end QuantumZipper
