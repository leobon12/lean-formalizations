import QuantumZipper.Proofs.Zipper.FieldLawlerMarkov
import QuantumZipper.Proofs.Zipper.FieldLawlerCoverMain
import QuantumZipper.Proofs.Zipper.FieldLawlerCoverHarm
import QuantumZipper.Proofs.Zipper.FieldLawlerSubSum
import QuantumZipper.Proofs.Zipper.FieldLawlerSubTopMain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# FL-THM: assembly of Field–Lawler Theorem 1.1

L. S. Field, G. F. Lawler, *Escape probability and transience for SLE*, EJP 20 (2015),
Theorem 1.1 (p. 3) = Proposition 3.4 (pp. 8–9). The chain:
* strong Markov + Prop. 3.1 summed over disks: `fieldLawlerReturn_of_cover` (FieldLawlerMarkov);
* covering from the image crosscut sum and the excursion lower bound (Prop. 3.1, p. 7):
  `flCover_holds_of_imageSum` (FieldLawlerCoverMain, with `flExcLower_holds`);
* image crosscut sum from topology + harmonic-measure existence + FL's sum bound:
  `flImageCrosscutSum_of_parts` (FieldLawlerSubSum) with `flHullHarmExists_holds`.
Open inputs: `FLImageTopStmt` (FL p. 9, first display) and `FLImageSumBoundStmt`
(FL p. 9 with Lemma 3.3 and (2.1), (2.4)).
-/

namespace QuantumZipper
namespace FieldLawler

/-- **Field–Lawler Theorem 1.1 (scaled form)** from the two remaining nodes of Prop. 3.4. -/
theorem fieldLawlerReturn_of_parts (hT : FLImageTopStmt) (hB : FLImageSumBoundStmt) :
    BaseFin2.FieldLawlerReturnStmt :=
  fieldLawlerReturn_of_cover
    (flCover_holds_of_imageSum (flImageCrosscutSum_of_parts hT flHullHarmExists_holds hB))

/-- **Field–Lawler Theorem 1.1 (scaled form)** from the crosscut separation fact
(`FLTopSepStmt`, Pommerenke Prop. 2.12) and FL's crosscut sum bound (`FLImageSumBoundStmt`). -/
theorem fieldLawlerReturn_of_sep_sum (hsep : FLTopSepStmt) (hB : FLImageSumBoundStmt) :
    BaseFin2.FieldLawlerReturnStmt :=
  fieldLawlerReturn_of_parts (flImageTop_of_sep hsep) hB

end FieldLawler
end QuantumZipper
