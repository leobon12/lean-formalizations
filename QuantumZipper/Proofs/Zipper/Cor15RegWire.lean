import QuantumZipper.Proofs.Zipper.Cor15WRMain
import QuantumZipper.Proofs.Zipper.Cor15RegBasic

/-!
# COR15-HREG: `Cor15WeldReadStmt` without the regularity hypothesis

`cor15WeldRead_of_reg` with its input `hreg` discharged by `ae_reg_zipCapDown`
(`Cor15RegBasic`). Own assembly.
-/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace QuantumZipper
namespace Cor15Group

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : NNReal → Ω → ℝ} {X : Ω → FieldSample}

/-- **`Cor15WeldReadStmt`** (the driver reading of Corollary 1.5 (a), `t > 0`), from Theorem 1.3
and the Rohde–Schramm blueprint item only. -/
theorem cor15WeldRead (h13 : theorem1_3) (hRSS : Blueprint.RohdeSchrammSimple)
    {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (hB : IsBrownianReal B P)
    (hX : IsFreeGFFModConstH X P) (hind : IndepFun (pathOf B) X P) {t : ℝ} (ht : 0 < t) :
    Cor15WeldReadStmt κ t P B X :=
  cor15WeldRead_of_reg h13 hRSS hκ hκ4 hB hX hind ht (ae_reg_zipCapDown hκ hκ4 hB hX hind ht)

end Cor15Group
end QuantumZipper
