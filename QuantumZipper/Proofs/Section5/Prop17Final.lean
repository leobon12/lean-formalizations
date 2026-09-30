import QuantumZipper.Proofs.Section5.Prop17PalmCFinal
import QuantumZipper.Proofs.Zipper.D3PlusN2Final

/-!
# Proposition 1.7 from the D3⁺(i) node TmZero

Sheffield, arXiv:1012.4797, Proposition 1.7. The Palm zoom is reduced to the fixed-point zoom
(nodes A and B proved, PALM-AB), node C is proved from D3⁺(i) (PALM-C), and D3⁺(i) in its N2
form rests on `D3Plus.D3PlusIN2TmZeroStmt` alone (`D3Plus.d3PlusIN2Rich_of_tmZero`).
-/

namespace QuantumZipper.S5.FieldLaw.Raw

/-- **Proposition 1.7**, conditional only on the D3⁺(i) node `D3PlusIN2TmZeroStmt`. -/
theorem theorem1_7_of_tmZero (hZ : D3Plus.D3PlusIN2TmZeroStmt) : theorem1_7 :=
  theorem1_7_of_D3PlusIN2 (D3Plus.d3PlusIN2Rich_of_tmZero hZ)

end QuantumZipper.S5.FieldLaw.Raw
