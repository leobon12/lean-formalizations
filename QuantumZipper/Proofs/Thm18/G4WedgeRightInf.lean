import QuantumZipper.Proofs.Thm18.G4ConcatBdryProof
import QuantumZipper.Proofs.LQG.WedgeBdryInfB3
import QuantumZipper.Proofs.Wire2b
import QuantumZipper.Proofs.Section5.Prop17RawLaw
import QuantumZipper.Proofs.LQG.WedgeBoundaryReg

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G4-WEDGE (2): infinite boundary length of a wedge on `[0, ∞)`

`WedgeRightInfStmt` (Theorem 1.8 node G4, `G4ConcatBdryProof.lean`): for the `(γ − 2/γ)`-wedge
`Y`, a.s. `ν_Y[0,∞) = ∞` (Sheffield, arXiv:1012.4797, §1.6, p. 21: a wedge has "an infinite
amount [of boundary length] in each neighborhood of ∞").

The mirror statement on `(−∞,0]` (`WedgeLeftInfStmt`) needed the reflection `z ↦ −z̄`
(`G4WedgeLeft.lean`), because the boundary length is only known infinite on `[0,∞)`. This side is
therefore *cheaper*: `WedgeBdry.ae_qBoundaryMeasure_Ici_top_wedgeField`
(`LQG/WedgeBdryInfB2.lean`, from the free-field input `WedgeBdry.wedgeBdryFreeInfStmt_holds`,
`LQG/WedgeBdryInfA.lean`, Sheffield §1.6) is already the reference-field statement on `[0,∞)`;
`WedgeBdry.ae_infMassIci_of_isQuantumWedge` (`LQG/WedgeBdryInfB3.lean`) transfers it to the
canonical description and then to every quantum wedge (rescaling by `scaleParam > 0` preserves
`ν[0,∞) = ⊤`). The only work here is to discharge the two handoff conditions of that theorem —
the a.s. positivity of `scaleParam` and the a.e.-measurability of the full-coordinate maps — with
the unconditional wedge results `Wire2.ae_wedge_canonical_spec` and
`Wire2.aemeasurable_dataFull_of_isQuantumWedge` (this is exactly the pattern of
`Thm18Asm.ae_qBoundaryMeasure_Iic_top_of_isQuantumWedge` in `G4WedgeLeft.lean`).

Nothing new is proved: both theorems are one-line combinations of the results above.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace Thm18Asm

/-- **Infinite boundary mass on `[0,∞)` for every quantum wedge** (`α < Q`). Unlike the left-side
statement, no reflection hypothesis is needed: `[0,∞)` is the side on which the reference wedge is
known to have infinite boundary length. -/
theorem ae_qBoundaryMeasure_Ici_top_of_isQuantumWedge {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {Y : Ω → FieldSample}
    (hW : IsQuantumWedge γ α Y P) : ∀ᵐ ω ∂P, qBoundaryMeasure γ (Y ω) (Ici (0 : ℝ)) = ⊤ := by
  have hY := Wire2.aemeasurable_dataFull_of_isQuantumWedge hγ hγ2 hW.1 hW
  obtain ⟨hα, Ω', _, P', X, A, hP', hX, hA, hI, hlaw⟩ := hW
  have hZW : IsQuantumWedge γ α (S5.FieldLaw.Raw.refField γ X A) P' :=
    ⟨hα, Ω', _, P', X, A, hP', hX, hA, hI, rfl⟩
  have hZ := Wire2.aemeasurable_dataFull_of_isQuantumWedge hγ hγ2 hα hZW
  have hsc : ∀ᵐ ω ∂P',
      0 < scaleParam γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ)) :=
    (Wire2.ae_wedge_canonical_spec hγ hγ2 hα hX hA hI).mono fun _ h => h.1
  have href := WedgeBdry.ae_infMassGood_canonical_wedgeField WedgeBdry.wedgeBdryFreeInfStmt_holds
    hγ hγ2 hα hX hA hI hsc
  filter_upwards [WedgeBdry.ae_of_fieldLawFull_eq hlaw hY hZ (WedgeBdry.InfMassGood γ)
    (WedgeBdry.measurableSet_infMassGood γ) (WedgeBdry.infMassGood_reconstruct γ) href] with ω hω
  exact hω.1

/-- **`WedgeRightInfStmt`**: a.s. the Theorem 1.8 wedge field has infinite boundary length on
`[0,∞)`. -/
theorem wedgeRightInfStmt_holds : WedgeRightInfStmt := by
  intro γ Ω _ P _ Y hγ hγ2 hW
  exact ae_qBoundaryMeasure_Ici_top_of_isQuantumWedge hγ hγ2 hW

end Thm18Asm
end QuantumZipper
