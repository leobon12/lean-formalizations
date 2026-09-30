import QuantumZipper.Proofs.Section5.Prop16AN23Lip
import QuantumZipper.Proofs.Section5.Prop16AN4
import QuantumZipper.Proofs.Section5.Prop16LocCoupleAnnMain

/-!
# Proposition 1.6 from the masked Palm nodes B′ and C′ only (D34, nodes AN2–AN4 discharged)

`theorem1_6_of_palmNodes_AN`: `theorem1_6` from `Prop16PalmIdMaskStmt` (B′) and
`Prop16FixedZoomMaskStmt` (C′), through `theorem1_6_of_annNodes` with AN2 `freeAnnRep_holds`,
AN3 `freeAnnLip_holds` (`Prop16AN23*.lean`) and AN4 `prop16UnifLocal_holds` (`Prop16AN4.lean`).
-/

namespace QuantumZipper

namespace Prop16Asm

/-- **Proposition 1.6 from the masked Palm nodes B′ and C′** (AN2–AN4 proved). -/
theorem theorem1_6_of_palmNodes_AN (hId : Prop16PalmIdMaskStmt) (hFix : Prop16FixedZoomMaskStmt) :
    theorem1_6 :=
  theorem1_6_of_annNodes prop16UnifLocal_holds freeAnnRep_holds freeAnnLip_holds hId hFix

end Prop16Asm

end QuantumZipper
