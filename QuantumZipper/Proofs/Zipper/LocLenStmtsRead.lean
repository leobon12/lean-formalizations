import QuantumZipper.Proofs.Zipper.LocLenDefs
import QuantumZipper.Proofs.Zipper.F1Read

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Follow-the-paper campaign (D75): the open-arc reading functional (statements for R2b / R6e)

Open-arc copies of `F1.readLen` and `F1.ReadLenAEMeasStmt` (F1Read.lean:40, :150). Task R2b
proves `ReadLenAEMeasArcStmt`; task R6e consumes it (F1d).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace LocLen

/-- The open-arc lengths at time `1`, recomputed from the `configLawFull` data (copy of
`F1.readLen`). -/
def readLenArc (γ : ℝ) (d : ((ℕ → ℝ) × (TestFun H → ℝ)) × (ℝ≥0 → ℝ)) : ℝ≥0∞ × ℝ≥0∞ :=
  unzipLengthsArc γ (Factorization.reconstruct (WedgeCan4.piC d.1.1), F1.readDrv d.2) 1

/-- Open-arc copy of `F1.ReadLenAEMeasStmt`. -/
def ReadLenAEMeasArcStmt (γ α κ : ℝ) : Prop :=
  0 < κ → κ < 4 → γ = Real.sqrt κ → α < Qc γ →
  ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) (Y : Ω → FieldSample) (B : ℝ≥0 → Ω → ℝ),
    IsProbabilityMeasure P → IsQuantumWedge γ α Y P → IsBrownianReal B P →
    AEMeasurable (fun ω => F1.dataH (Y ω)) P → AEMeasurable (pathOf B) P →
    IndepFun (pathOf B) Y P →
    AEMeasurable (readLenArc γ) (configLawFull (fun ω => (Y ω, drive κ B ω)) P)

end LocLen
end QuantumZipper
