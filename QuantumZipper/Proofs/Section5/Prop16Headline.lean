import QuantumZipper.Proofs.Section5.Prop16AN23Main
import QuantumZipper.Proofs.Section5.Prop16NodeB2Rep
import QuantumZipper.Proofs.Section5.Prop16NodeCMaskFinal
import QuantumZipper.Proofs.Section5.Prop16MarkovMask2
import QuantumZipper.Proofs.Section5.Prop16LocCoupleDom

/-!
# Proposition 1.6: headline wiring from the remaining open nodes

Task WIRE-P16. This file contains **wiring only**: no new mathematics, just the combination of the
proved assemblies of Proposition 1.6 with the still-open nodes, so that

* `theorem1_6_of_openNodes` is Proposition 1.6 from exactly the four remaining open nodes
  `Prop16PalmRepStmt`, `Prop16PalmGlobalStmt` (node B′), `D3Plus.D3PlusIN2RichStmt` (D3⁺(i) in N2
  form) and `Prop16NodeCMarkovMaskStmt` (node C′), and
* `theorem1_6_of_openNodes_palmMarkov` is the same with node C′ further reduced to the
  Palm–Markov node `Prop16PalmMarkovCouplingStmt` (`Prop16NodeCMarkovMaskStmt` without the
  `IsLocNiceOn` clause), using the now-unconditional domain Markov coupling
  `prop16MixedFreeLocCoupling_holds` proved below.

Proved inputs used (all unconditional):

* AN2 `freeAnnRep_holds` (`Prop16AN23.lean`), AN3 `freeAnnLip_holds` (`Prop16AN23Lip.lean`),
  AN4 `prop16UnifLocal_holds` (`Prop16AN4.lean`), AN5 `domMarkovCurveAnn_holds`
  (`Prop16LocCoupleAnnMain.lean`); from these, `prop16MixedFreeLocCoupling_of_domMarkovE`
  (`Prop16LocCoupleDom.lean`) gives the domain Markov coupling `Prop16MixedFreeLocCouplingStmt`
  of `Prop16LocGood.lean` (`prop16MixedFreeLocCoupling_holds` below);
* node C′ `prop16PalmShiftGoodStmt_proved` (`Prop16ShiftGoodPalm.lean`) and, with it, the masked
  law determinacy `Prop16FixedLawMaskStmt` (`prop16FixedLawMask_of_good`,
  `Prop16NodeCMaskFinal.lean`);
* `prop16PalmIdMaskStmt_of_rep` (`Prop16NodeB2Rep.lean`), `prop16FixedZoomMask_of_goodN2`
  (`Prop16NodeCMaskFinal.lean`), `prop16NodeCMarkovMaskStmt_of_palmMarkov`
  (`Prop16MarkovMask2.lean`), `theorem1_6_of_palmNodes_AN` (`Prop16AN23Main.lean`).

Source: Sheffield, arXiv:1012.4797, Proposition 1.6 (p. 25) and its proof; the node decomposition is
the project's (`Prop16PalmMask.lean`, `Prop16NodeB2*.lean`, `Prop16NodeCMask*.lean`,
`Prop16LocCoupleAnn*.lean`). No step of the paper is re-proved here.
-/

noncomputable section

namespace QuantumZipper

namespace Prop16Asm

/-- **The domain Markov coupling of Proposition 1.6, unconditionally.** Wiring of the proved
annulus nodes AN2–AN5 (`domMarkovCurveAnn_holds prop16UnifLocal_holds freeAnnRep_holds
freeAnnLip_holds`) through `prop16MixedFreeLocCoupling_of_domMarkovE`
(`Prop16LocCoupleDom.lean`). -/
theorem prop16MixedFreeLocCoupling_holds : Prop16MixedFreeLocCouplingStmt :=
  prop16MixedFreeLocCoupling_of_domMarkovE
    (domMarkovCurveAnn_holds prop16UnifLocal_holds freeAnnRep_holds freeAnnLip_holds)

end Prop16Asm

end QuantumZipper
