import QuantumZipper.Proofs.Zipper.FieldLawler4Assemble
import QuantumZipper.Proofs.Zipper.FieldLawler4ChainP4
import QuantumZipper.Proofs.Zipper.FieldLawler4ChainN
import QuantumZipper.Proofs.Zipper.FieldLawlerMain
import QuantumZipper.Proofs.Zipper.FLTopSep
import QuantumZipper.Proofs.Zipper.Thm13FromFieldLawler

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Field–Lawler Theorem 1.1 and Theorem 1.3

`flImageSumBound_holds : FLImageSumBoundStmt` (Field–Lawler, EJP 20 (2015), proof of Prop. 3.4,
p. 9: Lemma 3.3 + (2.1) + (2.4) with conformal invariance), from the per-crosscut chains
`fl4_perArc_pos`, `fl4_perArc_neg` and the assembly `fl4_imageSumBound_of`.

`fieldLawlerReturn_holds : BaseFin2.FieldLawlerReturnStmt` (Field–Lawler Theorem 1.1, scaled form),
and `theorem1_3_proved : theorem1_3`.
-/

namespace QuantumZipper
namespace FieldLawler

theorem flImageSumBound_holds : FLImageSumBoundStmt :=
  fl4_imageSumBound_of fl4_perArc_pos fl4_perArc_neg

/-- **Field–Lawler, EJP 20 (2015), Theorem 1.1** (scaled unconditional form). -/
theorem fieldLawlerReturn_holds : BaseFin2.FieldLawlerReturnStmt :=
  fieldLawlerReturn_of_sep_sum flTopSep_holds flImageSumBound_holds

end FieldLawler

/-- **Theorem 1.3.** -/
theorem theorem1_3_proved : theorem1_3 :=
  LocLen.theorem1_3_of_fieldLawler FieldLawler.fieldLawlerReturn_holds

end QuantumZipper
