import QuantumZipper.Proofs.Zipper.D3PlusN2CMInst
import QuantumZipper.Proofs.Zipper.D3PlusN2HarmP1

/-!
# D3⁺(i), node N2: reduction to the TmZero node

With the Cameron–Martin increment input (`cmIncrStmt_holds`) and the harmonic part
(`d3PlusN2HarmPart_holds`) proved, D3⁺(i) in rich form rests on `D3PlusIN2TmZeroStmt` alone.
-/

namespace QuantumZipper
namespace D3Plus

/-- D3⁺(i) (rich form, N2) from the TmZero node alone. -/
theorem d3PlusIN2Rich_of_tmZero (hZ : D3PlusIN2TmZeroStmt) : D3PlusIN2RichStmt :=
  d3PlusIN2Rich_of_two hZ d3PlusN2HarmPart_holds

end D3Plus
end QuantumZipper
