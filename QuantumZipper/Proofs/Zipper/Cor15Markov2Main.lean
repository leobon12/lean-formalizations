import QuantumZipper.Proofs.Zipper.Cor15Markov2Energy
import QuantumZipper.Proofs.Zipper.Cor15UnzipVerIndep

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# COR15-MARKOV (4): the D35 Markov core `Cor15MarkovStmt` is proved

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.2, §1.4 and
Corollary 1.5 (pp. 17–18); decision D35.

* `freeCircleReconStmt_holds`: the reconstruction input `FreeCircleReconStmt`
  (`Cor15Markov2Recon`, `Cor15Markov2Energy`).
* `cor15UnzipVersionStmt_holds`: the unzip version (with COR15-UNZIPVER's
  `cor15UnzipVersionStmt_of_freeCircleRecon`, which uses the proved B1-FULL law identity and the
  proved Markov input `cor15UnzipCoordIndepStmt_holds`).
* **`cor15MarkovStmt_holds : Cor15MarkovStmt`** (via `cor15MarkovFieldStmt_of_version` and
  `cor15MarkovStmt_of_field`), unconditionally.
* `theorem1_5_of_theorem1_3_of_zipVer`: Corollary 1.5 from Theorem 1.3, the round-trip field
  half and the zip version (the unzip obligations are now discharged).

Bookkeeping only.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace QuantumZipper
namespace Cor15Group

theorem freeCircleReconStmt_holds : FreeCircleReconStmt := freeCircleRecon_holds

theorem cor15UnzipVersionStmt_holds : Cor15UnzipVersionStmt :=
  cor15UnzipVersionStmt_of_freeCircleRecon freeCircleReconStmt_holds

theorem cor15MarkovFieldStmt_holds : Cor15MarkovFieldStmt :=
  cor15MarkovFieldStmt_of_version cor15UnzipVersionStmt_holds

/-- **The D35 Markov core holds.** -/
theorem cor15MarkovStmt_holds : Cor15MarkovStmt :=
  cor15MarkovStmt_of_field cor15MarkovFieldStmt_holds

end Cor15Group
end QuantumZipper
