import QuantumZipper.Proofs.Zipper.LocLenHeadlineFinal
import QuantumZipper.Proofs.Zipper.BaseFin2Main
import QuantumZipper.Proofs.Zipper.BaseFin2SleFL
import QuantumZipper.Proofs.Zipper.SWCoreB8FAll

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.3 from the Field–Lawler escape estimate

Wiring: `LocLen.theorem1_3_of_arcNodes_final` (Theorem 1.3 from X1, the base-finiteness fact the
paper uses without proof) with X1 discharged by `BaseFin2.baseFinite_of_yMerge_tail`
(`YMergeOffTipStmt` proved by `SWCore.yMergeOffTipStmt_holds`) and the SLE base-return tail by
`BaseFin2.sleBaseTail_of_fieldLawler`. The one remaining input is `FieldLawlerReturnStmt`:
L. S. Field, G. F. Lawler, *Escape probability and transience for SLE*, Electron. J. Probab. 20
(2015), no. 10, Theorem 1.1 (in unconditional, Brownian-scaled form for κ < 4), which is being
formalized from its published proof.
-/

namespace QuantumZipper
namespace LocLen

/-- **Theorem 1.3 from the Field–Lawler escape estimate** (its only input). -/
theorem theorem1_3_of_fieldLawler (hFL : BaseFin2.FieldLawlerReturnStmt) : theorem1_3 :=
  theorem1_3_of_arcNodes_final
    (BaseFin2.baseFinite_of_yMerge_tail SWCore.yMergeOffTipStmt_holds
      (BaseFin2.sleBaseTail_of_fieldLawler hFL))

end LocLen
end QuantumZipper
