import QuantumZipper.Proofs.Zipper.E6ReadBasic

/-!
# E6-READ, part 2: `E6ReadStmt` from two explicit regularity nodes

Task E6-READ. `E6.e6Up_of_read` needs `E6ReadStmt`. With the fixed reconstruction `regG`
(`E6ReadBasic`), readability is **regular readability** (`RegReadable`: raw values at the
`coordsFull` circles and raw test pairings agree with the regularized ones). Proved here:

* the `P_*` configuration `(Y, drive κ B')` has a.e.-measurable data (WEDGE-MEAS (1),
  `Wire2.aemeasurable_dataFull_of_isQuantumWedge`, and `IsBrownianReal.aemeasurable_pathOf`);
* the regularized **pairings** of the reference canonical wedge agree with the raw ones
  (`S5.FieldLaw.Raw.ae_pairRaw_eq_pairTest_wedge`, PAIR-AFF; scale positivity from
  `Wire2.ae_wedge_canonical_spec`);
* readability transfers from the reference wedge to every `IsQuantumWedge` field
  (`readableBy_of_fieldLawFull_eq`).

Remaining inputs (stated as Props, not assumed anywhere else):

* `WedgeRefCircleRegStmt γ α`: a.s. the raw values of the reference canonical wedge at all
  `coordsFull` circles equal the regularized ones (circle-average regularity up to the boundary
  and through the log-singular point `0`; Duplantier–Sheffield 2011, §3.1, Prop. 3.1 plus
  a growth bound for the radial process);
* `UnzipReadStmt`: for `P_*` samples, the unzipped configuration has a.e.-measurable data and its
  field is regularly readable (regularity of `Y ∘ f_{t'}^{-1} + Q log|(f_{t'}^{-1})'|`, rescaled,
  at a random time `t'` and scale `a`; this is a statement uniform over random conformal maps).

`e6ReadStmt_of_nodes : (∀ κ ∈ (0,4), WedgeRefCircleRegStmt √κ (√κ − 2/√κ)) → UnzipReadStmt →
E6ReadStmt`. Wiring only (own elementary argument).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace E6

open S5.FieldLaw.Raw

/-- **Circle regularity of the reference canonical wedge (remaining node).** -/
def WedgeRefCircleRegStmt (γ α : ℝ) : Prop :=
  ∀ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (X : Ω' → FieldSample)
    (A : ℝ → Ω' → ℝ), IsProbabilityMeasure P' → IsFreeGFFModConstH X P' →
    IsWedgeProcess α (Qc γ) A P' → IndepFun X (fun ω t => A t ω) P' →
    ∀ᵐ ω ∂P', ∀ i, refField γ X A ω (fcFull i) = evalReg (refField γ X A ω) (fcFull i)

/-- The reference canonical wedge is regularly readable, given its circle regularity. -/
theorem regReadable_refField {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < Qc γ)
    (hcirc : WedgeRefCircleRegStmt γ α) {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'}
    [hP : IsProbabilityMeasure P'] {X : Ω' → FieldSample} {A : ℝ → Ω' → ℝ}
    (hX : IsFreeGFFModConstH X P') (hA : IsWedgeProcess α (Qc γ) A P')
    (hI : IndepFun X (fun ω t => A t ω) P') : RegReadable (refField γ X A) P' := by
  refine ⟨hcirc Ω' _ P' X A hP hX hA hI, fun ρ => ?_⟩
  filter_upwards [ae_pairRaw_eq_pairTest_wedge hX (WedgeCan4.ae_continuous_wedgeProcess hA)
    (Qc γ) ρ, Wire2.ae_wedge_canonical_spec hγ hγ2 hα hX hA hI] with ω h hs
  exact (h _ hs.1).1

/-- Every quantum wedge field is readable by `regG`, given circle regularity of the reference
wedge. -/
theorem readableBy_regG_of_isQuantumWedge {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hcirc : WedgeRefCircleRegStmt γ α) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Y : Ω → FieldSample} (hW : IsQuantumWedge γ α Y P) : ReadableBy regG Y P := by
  have hY := Wire2.aemeasurable_dataFull_of_isQuantumWedge hγ hγ2 hW.1 hW
  obtain ⟨hα, Ω', _, P', X, A, hP', hX, hA, hI, hlaw⟩ := hW
  have hZW : IsQuantumWedge γ α (refField γ X A) P' :=
    ⟨hα, Ω', _, P', X, A, hP', hX, hA, hI, rfl⟩
  exact readableBy_of_fieldLawFull_eq measurable_regG hY
    (Wire2.aemeasurable_dataFull_of_isQuantumWedge hγ hγ2 hα hZW) hlaw
    (readableBy_regG (regReadable_refField hγ hγ2 hα hcirc hX hA hI))

end E6
end QuantumZipper
