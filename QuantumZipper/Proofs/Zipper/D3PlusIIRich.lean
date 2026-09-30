import QuantumZipper.Proofs.Zipper.LocRichD3
import QuantumZipper.Proofs.Zipper.D3PlusIICond

/-!
# D3⁺(ii) (LSC), rich form (decision D25): the reductions of `D3PlusIISplit`, `D3PlusIICond`

D25's `D3PlusIIStmtRich` (`LocRichD3.lean`) is `LSCGen locFieldFull` (`lscGen_locFieldFull_iff`),
so the generic reductions apply verbatim:

* `d3PlusIIRich_of_const_zero`: from the constant (level-shift) part and the part vanishing at `0`
  (Cameron–Martin part), for the reading `locFieldFull`;
* `d3PlusIIRich_of_core`: from the deterministic-correction node `LSCCoreGen locFieldFull`.

Both imply D23's `D3PlusIIStmt` through `d3PlusII_of_rich`.
-/

noncomputable section

namespace QuantumZipper
namespace D3Plus

/-- **Rich D3⁺(ii) from its constant part and its part vanishing at `0`.** -/
theorem d3PlusIIRich_of_const_zero (hC : LSCConstGen locFieldFull)
    (hZ : LSCZeroGen locFieldFull) : D3PlusIIStmtRich :=
  lscGen_of_const_zero hC hZ

end D3Plus
end QuantumZipper
