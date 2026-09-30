import QuantumZipper.Proofs.Zipper.LocLenDefs
import QuantumZipper.Proofs.Zipper.F1LenReg

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Follow-the-paper campaign (D75): the open-arc read-regularity measurability statement (R2b)

Open-arc copy of `F1.LenReadRegMeasStmt` (F1LenReg.lean:152) by the substitution rule
(`unzipLengths ↦ unzipLengthsArc`). Task R2b proves it (`LocLenR2bReg.lean`); task R6c consumes
it (`lenReadRegArc_of_meas`).
-/

noncomputable section

open MeasureTheory Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace LocLen

/-- Open-arc copy of `F1.LenReadRegMeasStmt`. -/
def LenReadRegMeasArcStmt : Prop :=
  ∀ (κ : ℝ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Y : Ω' → FieldSample) (B' : ℝ≥0 → Ω' → ℝ), Thm13Asm.IsPStarSample κ P' Y B' →
    NullMeasurableSet {d | MonotoneOn
        (fun t => (unzipLengthsArc (Real.sqrt κ) (F1.readCfg d) t).1) (Ici 0) ∧
      ContinuousOn (fun t => (unzipLengthsArc (Real.sqrt κ) (F1.readCfg d) t).2.toReal) (Ici 0)}
      (configLawFull (F1.pcfg κ Y B') P')

end LocLen
end QuantumZipper
