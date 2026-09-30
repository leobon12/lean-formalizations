import QuantumZipper.Proofs.LQG.WedgeMeasND
import QuantumZipper.Proofs.LQG.WedgeInfTotal
import QuantumZipper.Proofs.LQG.WedgeFinZeroCoupling

/-!
# WIRE-2b: discharging the proved wedge inputs

Wiring only (small proofs by application). The two analytic inputs of R23 (TASKS §1.6, Sheffield
arXiv:1012.4797 p. 21) are now proved:

* `WedgeFinZero.wedgeFiniteNearZero_holds` (`Proofs/LQG/WedgeFinZeroCoupling.lean`):
  `WedgeCan4.WedgeFiniteNearZero γ α` for `0 < γ < 2`, `α < Qc γ`;
* `WedgeInf.wedgeInfiniteTotal` (`Proofs/LQG/WedgeInfTotal.lean`):
  `WedgeCan4.WedgeInfiniteTotal γ α`, same range.

This file states `WedgeCan4` / `WedgeMeasND`'s results without those hypotheses (the range
hypotheses `0 < γ`, `γ < 2`, `α < Qc γ` stay, as they are hypotheses of the proved inputs; the
`α < Qc γ` hypothesis of the `WedgeMeasND` statements appears explicitly here because it was
previously read off from `IsQuantumWedge γ α Y P`).

Nothing here is new mathematics.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal

namespace QuantumZipper

namespace Wire2

open WedgeCan4

/-! ## R23 (a): area profile -/

/-- R23 (a): a.s. the wedge field has an area profile. -/
theorem ae_hasAreaProfile_wedgeField {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < Qc γ)
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {X : Ω' → FieldSample} {A : ℝ → Ω' → ℝ} (hX : IsFreeGFFModConstH X P')
    (hA : IsWedgeProcess α (Qc γ) A P') (hI : IndepFun X (fun ω t => A t ω) P') :
    ∀ᵐ ω ∂P', AreaProfile.HasAreaProfile γ
      (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ)) :=
  WedgeCan4.ae_hasAreaProfile_wedgeField_of_inputs
    (hfin := WedgeFinZero.wedgeFiniteNearZero_holds hγ hγ2 hα)
    (hinf := WedgeInf.wedgeInfiniteTotal hγ hγ2 hα) hγ hγ2 hX hA hI

/-! ## R23 (b): canonical specification -/

/-- R23 (b): a.s. the wedge field canonicalizes (positive scale, good, unit area in `B(0,1)`). -/
theorem ae_wedge_canonical_spec {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < Qc γ)
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {X : Ω' → FieldSample} {A : ℝ → Ω' → ℝ} (hX : IsFreeGFFModConstH X P')
    (hA : IsWedgeProcess α (Qc γ) A P') (hI : IndepFun X (fun ω t => A t ω) P') :
    ∀ᵐ ω ∂P', 0 < scaleParam γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ)) ∧
      IsLQGGood γ (canonical γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ))) ∧
      qAreaMeasure γ (canonical γ (wedgeField (lateralPart (X ω)) (fun t => A t ω) (Qc γ)))
        (Metric.ball 0 1 ∩ H) = 1 :=
  WedgeCan4.ae_wedge_canonical_spec_of_inputs
    (hfin := WedgeFinZero.wedgeFiniteNearZero_holds hγ hγ2 hα)
    (hinf := WedgeInf.wedgeInfiniteTotal hγ hγ2 hα) hγ hγ2 hα hX hA hI

/-! ## R23 (c): a.e.-measurability of the data, goodness and unit area -/

open WedgeMeas in
/-- The reference wedge law is not a Dirac mass (the radial averages of the canonical wedge field
separate points). -/
theorem fieldLawFull_wedgeRef_ne_dirac {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < Qc γ)
    {Ω' : Type} [MeasurableSpace Ω'] {P' : Measure Ω'} [IsProbabilityMeasure P']
    {X : Ω' → FieldSample} {A : ℝ → Ω' → ℝ} (hX : IsFreeGFFModConstH X P')
    (hA : IsWedgeProcess α (Qc γ) A P') (hI : IndepFun X (fun ω t => A t ω) P')
    (c : (ℕ → ℝ) × (TestFun H → ℝ)) :
    fieldLawFull H (wedgeRef γ X A) P' ≠ Measure.dirac c :=
  WedgeMeasND.fieldLawFull_wedgeRef_ne_dirac
    (hfin := WedgeFinZero.wedgeFiniteNearZero_holds hγ hγ2 hα)
    (hinf := WedgeInf.wedgeInfiniteTotal hγ hγ2 hα) hγ hγ2 hα hX hA hI c

/-- **WEDGE-MEAS (1).** Every quantum wedge has a.e.-measurable data. -/
theorem aemeasurable_dataFull_of_isQuantumWedge {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α < Qc γ) {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Y : Ω → FieldSample}
    (h : IsQuantumWedge γ α Y P) :
    AEMeasurable (fun ω => WedgeMeas.dataFull H (Y ω)) P :=
  WedgeMeasND.aemeasurable_dataFull_of_isQuantumWedge
    (hfin := WedgeFinZero.wedgeFiniteNearZero_holds hγ hγ2 hα)
    (hinf := WedgeInf.wedgeInfiniteTotal hγ hγ2 hα) hγ hγ2 h

/-- `S5.FieldLaw.WedgeDataAEMeasStmt` (the a.e.-measurability form of WEDGE-MEAS (1)). -/
theorem wedgeDataAEMeasStmt {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < Qc γ) :
    S5.FieldLaw.WedgeDataAEMeasStmt γ α :=
  WedgeMeasND.wedgeDataAEMeasStmt_of_inputs
    (hfin := WedgeFinZero.wedgeFiniteNearZero_holds hγ hγ2 hα)
    (hinf := WedgeInf.wedgeInfiniteTotal hγ hγ2 hα) hγ hγ2

/-- **R23 (c)** (TASKS form, no measurability hypothesis). -/
theorem isQuantumWedge_ae_unitArea {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < Qc γ)
    {Ω : Type*} [MeasurableSpace Ω] {Y : Ω → FieldSample} {P : Measure Ω}
    (h : IsQuantumWedge γ α Y P) :
    ∀ᵐ ω ∂P, IsLQGGood γ (Y ω) ∧ qAreaMeasure γ (Y ω) (Metric.ball 0 1 ∩ H) = 1 :=
  WedgeMeasND.IsQuantumWedge.ae_unitArea
    (hfin := WedgeFinZero.wedgeFiniteNearZero_holds hγ hγ2 hα)
    (hinf := WedgeInf.wedgeInfiniteTotal hγ hγ2 hα) hγ hγ2 h

/-- **WEDGE-MEAS (2).** Every quantum wedge is a.s. good. -/
theorem wedgeGoodStmt {γ α : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < Qc γ) :
    S5.FieldLaw.WedgeGoodStmt γ α :=
  WedgeMeasND.wedgeGoodStmt_of_inputs
    (hfin := WedgeFinZero.wedgeFiniteNearZero_holds hγ hγ2 hα)
    (hinf := WedgeInf.wedgeInfiniteTotal hγ hγ2 hα) hγ hγ2

end Wire2

end QuantumZipper
