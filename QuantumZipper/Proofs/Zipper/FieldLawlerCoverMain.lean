import QuantumZipper.Proofs.Zipper.FieldLawlerCover
import QuantumZipper.Proofs.Zipper.FieldLawlerSubExc

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL-THM-COVER: final assembly

`FLCoverStmt` (Field–Lawler, arXiv:1407.3314, proof of Prop. 3.4 with the lower bound of
Prop. 3.1) from the image crosscut sum `FLImageCrosscutSumStmt` alone: the excursion lower bound
`FLExcLowerStmt` is `flExcLower_holds` (FieldLawlerSubExc.lean), and the covering step is
`flCover_of_imageSum_excLower` (FieldLawlerCover.lean).
-/

namespace QuantumZipper
namespace FieldLawler

/-- **FL covering from the image crosscut sum.** -/
theorem flCover_holds_of_imageSum (hS : FLImageCrosscutSumStmt) : FLCoverStmt :=
  flCover_of_imageSum_excLower hS flExcLower_holds

end FieldLawler
end QuantumZipper
