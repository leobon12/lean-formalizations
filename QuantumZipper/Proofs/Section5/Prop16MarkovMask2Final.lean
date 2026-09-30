import QuantumZipper.Proofs.Section5.Prop16MarkovMask2Agree
import QuantumZipper.Proofs.Section5.Prop16AN23Main
import QuantumZipper.Proofs.Section5.Prop16LocCoupleDom
import QuantumZipper.Proofs.Section5.Prop16LocCoupleAnnMain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.6, node C′ (masked): assembly from the harmonic Palm representative

Task P16-MARKOVMASK2.

* `prop16NodeCMarkovMaskStmt_of_harm`: node C′'s Markov input `Prop16NodeCMarkovMaskStmt` from the
  single analytic node `Prop16PalmShiftHarmStmt` (`Prop16MarkovMask2.lean`): the local niceness
  clause by law transfer (`prop16NodeCMarkovMaskStmt_of_palmMarkov`) and the Palm-Markov node by
  `prop16PalmMarkovCoupling_of_harm` (`Prop16MarkovMask2Agree.lean`), both fed with the
  unconditional domain Markov coupling (AN2–AN5 through `prop16MixedFreeLocCoupling_of_domMarkovE`).
* `theorem1_6_of_palmHarm`: **Proposition 1.6** from node B′ (`Prop16PalmIdMaskStmt`), D3⁺(i) in
  N2 form and `Prop16PalmShiftHarmStmt`, via `theorem1_6_of_palmNodes_AN` and
  `prop16FixedZoomMask_of_goodN2` (with the proved `prop16PalmShiftGoodStmt_proved`).

Source: Sheffield, arXiv:1012.4797, Proposition 1.6 (p. 25) and its proof; the node decomposition
is the project's. Own bookkeeping.
-/

noncomputable section

namespace QuantumZipper

namespace Prop16Asm

/-- The domain Markov coupling of Proposition 1.6, unconditionally (proved annulus nodes
AN2–AN5). -/
theorem prop16MixedFreeLocCoupling_mm : Prop16MixedFreeLocCouplingStmt :=
  prop16MixedFreeLocCoupling_of_domMarkovE
    (domMarkovCurveAnn_holds prop16UnifLocal_holds freeAnnRep_holds freeAnnLip_holds)

/-- **Node C′'s Markov input from the harmonic Palm representative.** -/
theorem prop16NodeCMarkovMaskStmt_of_harm (hH : Prop16PalmShiftHarmStmt) :
    Prop16NodeCMarkovMaskStmt :=
  prop16NodeCMarkovMaskStmt_of_palmMarkov prop16MixedFreeLocCoupling_mm
    (prop16PalmMarkovCoupling_of_harm prop16MixedFreeLocCoupling_mm hH)

/-- **Proposition 1.6** from node B′, D3⁺(i) in N2 form and the harmonic Palm representative. -/
theorem theorem1_6_of_palmHarm (hId : Prop16PalmIdMaskStmt) (hN2 : D3Plus.D3PlusIN2RichStmt)
    (hH : Prop16PalmShiftHarmStmt) : theorem1_6 :=
  theorem1_6_of_palmNodes_AN hId
    (prop16FixedZoomMask_of_goodN2 hN2 prop16PalmShiftGoodStmt_proved
      (prop16NodeCMarkovMaskStmt_of_harm hH))

end Prop16Asm

end QuantumZipper
