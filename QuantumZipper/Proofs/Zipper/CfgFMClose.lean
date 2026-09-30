import QuantumZipper.Proofs.Zipper.CfgFMMain
import QuantumZipper.Proofs.Zipper.CfgFMVarFinal

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# CFG-FIRSTMODE: `CfgFirstModeStmt` and `CfgDensStmt` hold

`CfgFM.cfgFMVarStmt_holds` (fixed-driver variance node) with the assembly
`CfgFM.cfgFirstMode_of_var` / `CfgFM.cfgDensStmt_of_var`. Bookkeeping only.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace QuantumZipper.E6
namespace CfgFM

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- **`CfgDensStmt` holds.** -/
theorem cfgDensStmt_holds (κ T : ℝ) {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}
    (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) :
    CfgDensStmt κ T P B X :=
  cfgDensStmt_of_var κ T (fun T' hT' => cfgFMVarStmt_holds κ T' hT') hB hX hind

end CfgFM
end QuantumZipper.E6
