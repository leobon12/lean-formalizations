import QuantumZipper.Proofs.Thm18.Final18Wire
import QuantumZipper.Proofs.Thm18.Thm18PaperMOBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.8 of Sheffield, arXiv:1012.4797 — proved

`R18.theorem1_8PaperMO_proved` (Thm18/Final18Wire.lean) proves the R18-layer form of Theorem 1.8
(paper form, D87) with no hypotheses; the statement-layer form `Paper18.theorem1_8PaperMO`
follows by the bridge `Paper18.theorem1_8PaperMO_of_R18` (Thm18/Thm18PaperMOBridge.lean).
-/

namespace QuantumZipper

/-- **Theorem 1.8** (Sheffield, arXiv:1012.4797), paper form. -/
theorem theorem1_8_proved : Paper18.theorem1_8PaperMO :=
  Paper18.theorem1_8PaperMO_of_R18 R18.theorem1_8PaperMO_proved

end QuantumZipper
