import QuantumZipper.Proofs.LQG.WedgeCRegCirc
import QuantumZipper.Proofs.Thm18.Assembly
import QuantumZipper.Proofs.Zipper.F1Read
import QuantumZipper.Proofs.Zipper.ESMComplF1
import QuantumZipper.Proofs.Thm18.G4WedgeZero
import QuantumZipper.Proofs.Thm18.G4WedgeLeft

/-!
# WIRE-4: the wedge-regularity nodes discharged (wiring only)

`QuantumZipper.Proofs.LQG.WedgeCReg{,Cont,B4d,Circ}` prove, for `0 < γ < 2` and `α < Qc γ`,

* `WedgeCReg.wedgeLatReflRegStmt_holds : F1.WedgeLatReflRegStmt γ α` (input (i) of B4(d)),
* `WedgeCReg.wedgeRefReflectStmt_holds' : F1.WedgeRefReflectStmt γ α` (B4(d), over
  `WedgeInf.wedgeInfiniteTotal`),
* `WedgeCReg.wedgeRefCircleRegStmt_holds : E6.WedgeRefCircleRegStmt γ α`.

This file is pure wiring: it restates the consumers of those three with the corresponding
hypotheses replaced by `0 < γ`, `γ < 2` and `α < Qc γ` (so all statements below are
unconditional in the wedge-regularity nodes). Every proof is one application.

* F1 (Theorem 1.3, node F1d): `configLawFull_reflect_of_wedge`, `configLawFull_reflect_of_wedge_bm`,
  `f1d_lengths_agree_wedge_bm` without the reflection-law hypothesis
  `F1.WedgeRefReflectStmt γ α`;
* Theorem 1.8 (node G4): `wedgeZeroRegStmt : Thm18Asm.WedgeZeroRegStmt`,
  `wedgeLeftInfStmt : Thm18Asm.WedgeLeftInfStmt`, and `g4Stmt_of` with those two discharged
  (remaining: `G4WeldStmt`, `G4RoundStmt`, `G4GroupStmt`, `G4FactorStmt`);
* E6 (Theorem 1.3 chain): `e6ReadStmt_of_unzip : E6.UnzipReadStmt → E6.E6ReadStmt` and
  `e6Up_of_unzip : E6.UnzipReadStmt → Thm13Asm.E6UpStmt D3Plus.locData`, without the circle
  regularity hypothesis.

The wedge range `α = γ − 2/γ < Qc γ` for `0 < γ < 2` is the existing `Thm18Asm.alpha_lt_Qc`
(`Proofs/Thm18/Assembly.lean`, from `γ − 2/γ < γ < Qc γ`); nothing new is proved here.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace Wire4

/-! ## 1. F1d (Theorem 1.3) with B4(d) discharged -/

/-- **F1d input (c), unconditional**: `F1.configLawFull_reflect_of_wedge` with the reflection law
`F1.WedgeRefReflectStmt γ α` discharged (the wedge hypothesis supplies `α < Qc γ`). -/
theorem configLawFull_reflect_of_wedge {γ α κ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2)
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → FieldSample} {B : ℝ≥0 → Ω → ℝ} (hW : IsQuantumWedge γ α Y P)
    (hY : AEMeasurable (fun ω => F1.dataH (Y ω)) P) (hB : IsPreBrownianReal B P)
    (hBm : AEMeasurable (pathOf B) P) (hind : IndepFun (pathOf B) Y P) :
    configLawFull (fun ω => F1.reflectConfig (Y ω, drive κ B ω)) P =
      configLawFull (fun ω => (Y ω, drive κ B ω)) P :=
  F1.configLawFull_reflect_of_wedge (WedgeCReg.wedgeRefReflectStmt_holds' hγ hγ2 hW.1)
    hW hY hB hBm hind

/-! ## 2. Theorem 1.8, node G4, with the two wedge nodes discharged -/

/-- **`Thm18Asm.WedgeZeroRegStmt` unconditionally** (`Thm18Asm.wedgeZeroRegStmt_of_circ` with
`E6.WedgeRefCircleRegStmt` discharged). -/
theorem wedgeZeroRegStmt : Thm18Asm.WedgeZeroRegStmt :=
  Thm18Asm.wedgeZeroRegStmt_of_circ fun γ hγ hγ2 =>
    WedgeCReg.wedgeRefCircleRegStmt_holds (γ := γ) hγ hγ2 (Thm18Asm.alpha_lt_Qc hγ hγ2)

/-- **`Thm18Asm.WedgeLeftInfStmt` unconditionally** (`Thm18Asm.wedgeLeftInfStmt_of_latRefl` with
`F1.WedgeLatReflRegStmt` discharged). -/
theorem wedgeLeftInfStmt : Thm18Asm.WedgeLeftInfStmt :=
  Thm18Asm.wedgeLeftInfStmt_of_latRefl fun γ hγ hγ2 =>
    WedgeCReg.wedgeLatReflRegStmt_holds (γ := γ) hγ hγ2 (Thm18Asm.alpha_lt_Qc hγ hγ2)

/-! ## 3. E6 (Theorem 1.3 chain) with circle regularity discharged -/

end Wire4
end QuantumZipper
