import QuantumZipper.Proofs.Thm18.RTHmpRed
import QuantumZipper.Proofs.Thm18.RTHmpFree

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# RT-HMP (5): `CircAvgLogGrowthStmt` holds

Hu–Miller–Peres, *Thick points of the Gaussian free field*, Ann. Probab. 38 (2010), Prop. 2.1
and the proof of Lemma 3.1: the free-field circle averages grow logarithmically
(`RTHmp.hmp_free_log_growth`, files `RTHmpBC`, `RTHmpFam`, `RTHmpFree`), and the wedge inherits
this through the realization of the wedge and the wedge decomposition (`RTHmpRed`).
-/

namespace QuantumZipper
namespace R18
namespace RTHmp

/-- **Free-field log growth** (Hu–Miller–Peres, Prop. 2.1 / Lemma 3.1). -/
theorem freeCircLogGrowthStmt_holds : FreeCircLogGrowthStmt := by
  intro Ω _ P _ X hX
  exact hmp_free_log_growth hX

end RTHmp

/-- **`CircAvgLogGrowthStmt` holds**: a.s. the wedge circle averages at radius `2^{-k}` are
`O(k + 1)` on bounded sets. -/
theorem circAvgLogGrowthStmt_holds : CircAvgLogGrowthStmt :=
  RTHmp.circAvgLogGrowth_of_free RTHmp.freeCircLogGrowthStmt_holds

end R18
end QuantumZipper
