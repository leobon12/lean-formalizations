import QuantumZipper.Proofs.Zipper.Cor15FieldGood2Main
import QuantumZipper.Proofs.Zipper.Cor15ZipCoordPushB

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# COR15-FIELDGOOD2 (3): Corollary 1.5 from Theorem 1.3

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Corollary 1.5 (pp. 17–18).
Decisions D42, D47.

* `theorem1_5_of_theorem1_3_of_zipCoordRead`: Theorem 1.3 and the zip reading node
  `Cor15ZipCoordReadStmt` give Corollary 1.5 (the D42/D47 headline
  `theorem1_5_of_theorem1_3_of_zipFixRead''` with the shift good set
  `cor15ShiftGoodStmt_of_theorem1_3` and the round-trip node `cor15UnzipZipFieldGoodStmt'_holds`).
* `theorem1_5_of_theorem1_3'`: Corollary 1.5 from Theorem 1.3 alone (the reading node is
  `cor15ZipCoordRead'`, `Cor15ZipCoordPushB`).

Own assembly.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace QuantumZipper
namespace Cor15Group

/-- **Corollary 1.5 from Theorem 1.3 and the zip reading node.** -/
theorem theorem1_5_of_theorem1_3_of_zipCoordRead (h13 : theorem1_3)
    (hR : ∀ κ : ℝ, 0 < κ → κ < 4 →
      ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample), IsGrpSetup P B X →
      ∀ a : ℝ, 0 < a → Cor15ZipCoordReadStmt κ a P B X) : theorem1_5 :=
  theorem1_5_of_theorem1_3_of_zipFixRead'' h13 (cor15ShiftGoodStmt_of_theorem1_3 h13)
    (fun _ hκ hκ4 _ _ _ _ _ _ hS _ ha => cor15UnzipZipFieldGoodStmt'_holds h13 hκ hκ4 hS ha) hR

/-- **Corollary 1.5 from Theorem 1.3.** -/
theorem theorem1_5_of_theorem1_3' (h13 : theorem1_3) : theorem1_5 :=
  theorem1_5_of_theorem1_3_of_zipCoordRead h13
    fun _ hκ hκ4 _ _ _ _ _ _ hS _ ha => cor15ZipCoordRead' h13 hκ hκ4 hS ha

end Cor15Group
end QuantumZipper
