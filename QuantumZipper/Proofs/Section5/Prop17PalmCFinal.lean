import QuantumZipper.Proofs.Section5.Prop17PalmCMeas
import QuantumZipper.Proofs.Section5.Prop17PalmABMain

/-!
# Proposition 1.7 from D3⁺(i) (PALM-C)

Nodes A and B of the Palm zoom are proved (`Prop17PalmAB*.lean`, `theorem1_7_of_fixedZoom`), and
node C is proved from D3⁺(i) (`prop17FreeFixedZoom_of_D3PlusIRich`). Hence Proposition 1.7
(`theorem1_7`) follows from the rich form of D3⁺(i), or from its N2 form.
-/

namespace QuantumZipper
namespace S5
namespace FieldLaw
namespace Raw

/-- **Proposition 1.7 from the N2 form of D3⁺(i).** -/
theorem theorem1_7_of_D3PlusIN2 (hN2 : D3Plus.D3PlusIN2RichStmt) : theorem1_7 :=
  theorem1_7_of_fixedZoom (prop17FreeFixedZoom_of_D3PlusIN2 hN2)

end Raw
end FieldLaw
end S5
end QuantumZipper
