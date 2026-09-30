import QuantumZipper.Proofs.Zipper.F1Read
import QuantumZipper.Proofs.Probability.BrownianPathMeas

/-!
# F1d with the path-measurability hypothesis `hBm` discharged (AUDIT12 F12-1)

The F1d statements of `F1ReflLaw.lean` and `F1Read.lean` take
`hBm : AEMeasurable (pathOf B) P`. For a Brownian motion (`IsBrownianReal`, a.s. continuous
paths) this is `IsBrownianReal.aemeasurable_pathOf` (`Proofs/Probability/BrownianPathMeas.lean`).
This file restates the consumers without `hBm`; the proofs are pure applications (wiring only).
(`hBm` is genuinely needed for a mere `IsPreBrownianReal`, so the originals stay.)
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace QuantumZipper
namespace F1

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Two Brownian motions have the same path law on `ℝ≥0 → ℝ` (product σ-algebra). -/
theorem map_pathOf_eq_of_isBrownianReal {B C : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hC : IsBrownianReal C P) : P.map (pathOf B) = P.map (pathOf C) :=
  map_pathOf_eq_of_isPreBrownianReal hB.toIsPreBrownianReal hC.toIsPreBrownianReal
    (IsBrownianReal.aemeasurable_pathOf hB) (IsBrownianReal.aemeasurable_pathOf hC)

theorem aemeasurable_cfgData_drive_bm (κ : ℝ) {Y : Ω → FieldSample} {B : ℝ≥0 → Ω → ℝ}
    (hY : AEMeasurable (fun ω => dataH (Y ω)) P) (hB : IsBrownianReal B P) :
    AEMeasurable (fun ω => cfgData (Y ω, drive κ B ω)) P :=
  aemeasurable_cfgData_drive κ hY (IsBrownianReal.aemeasurable_pathOf hB)

end F1
end QuantumZipper
