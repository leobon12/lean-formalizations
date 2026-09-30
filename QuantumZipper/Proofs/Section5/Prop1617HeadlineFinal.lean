import QuantumZipper.Proofs.Section5.Prop1617HeadlineV2
import QuantumZipper.Proofs.Zipper.D3PlusN2H2WinCM
import QuantumZipper.Proofs.Zipper.D3PlusN2OscEquiv
import QuantumZipper.Proofs.Zipper.D3PlusN2FirstModeVar
import QuantumZipper.Proofs.Zipper.D3PlusN2LipMain
import QuantumZipper.Proofs.Zipper.D3PlusN2H2FreeWin
import QuantumZipper.Proofs.Zipper.D3PlusN2H3WinDens
import QuantumZipper.Proofs.Section5.Prop16BdryMomMain
import QuantumZipper.Proofs.Section5.Prop16PalmRep
import QuantumZipper.Proofs.Section5.Prop16ShiftHarm

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Propositions 1.6 and 1.7: final wiring, from the single open node `N2ZFirstModeVarStmt`

Task WIRE-P1617-FINAL. Wiring only, no new mathematics. Sheffield, *Conformal weldings of random
surfaces* (arXiv:1012.4797), Proposition 1.6 (p. 25) and Proposition 1.7 are reduced here to
**one** open statement: the Gaussian variance node

* `D3Plus.N2ZFirstModeVarStmt` (`Proofs/Zipper/D3PlusN2FirstModeVar.lean`): for every free
  GFF-mod-const sample `X` on `(Ω,P)` there is a circle-regularized version `G` of `X` such
  that, for every `m`, some `c ≥ 0` bounds, uniformly in the scale `n ≥ n₀` and the branch
  `k : Fin 2`, the variances of the rescaled first-mode read-offs `V q` (constants) and of their
  differences `V q − V q'` (on the box `R + 1`), each a centred Gaussian; the constants `V q`
  represent the first mode on the corresponding time window (a.e. identity).

Every other node of the two propositions has been proved in the repository and is discharged here:

* `N2ZFirstModeVarStmt → N2ZFirstModeStmt` — `D3Plus.n2ZFirstMode_of_var`
  (`Proofs/Zipper/D3PlusN2FirstModeVar.lean`), via the 16th-moment node
  `D3PlusN2FirstModeBlock.lean`;
* `N2ZFirstModeStmt → N2ZPairOscStmt` — `D3Plus.n2ZPairOsc_of_firstMode`
  (`Proofs/Zipper/D3PlusN2LipMain.lean`), the uniform oscillation bound on the
  circle-regularized test-function pairings;
* `N2H2HarmWinStmt` — `D3Plus.n2H2HarmWinStmt_holds` (`Proofs/Zipper/D3PlusN2H2FreeWin.lean`),
  the model-side Cameron–Martin half of H2;
* `N2H3SplitWinStmt` — `D3Plus.n2H3SplitWinStmt_holds` (`Proofs/Zipper/D3PlusN2H3WinDens.lean`),
  the lateral/radial splitting node;
* `Prop16PalmGlobalStmt` — `Prop16Asm.prop16PalmGlobalStmt_holds_bdryMom`
  (`Proofs/Section5/Prop16BdryMomMain.lean`), node B′ (global): the global window Palm formula,
  from the boundary moment bound `Prop16BdryMomStmt` (and hence UI and boundary `L¹`);
* `Prop16PalmRepStmt` — `Prop16Asm.prop16PalmRepStmt_holds` (`Proofs/Section5/Prop16PalmRep.lean`),
  node B′ items (6), (7): the measurable representation of the masked zoom coordinates by a
  countable admissible family;
* `Prop16PalmShiftHarmStmt` — `Prop16Asm.prop16PalmShiftHarmStmt_holds`
  (`Proofs/Section5/Prop16ShiftHarm.lean`), node C′ in reduced harmonic-Palm form.

The two remaining headline inputs of `Prop1617HeadlineV2.lean`, `N2H2HarmWinStmt` and
`N2ZPairOscStmt`, are supplied from the chain above, so `theorem1_6_of_win` and
`theorem1_7_of_win` become unconditional in everything but `N2ZFirstModeVarStmt`. We use those
two (version 2, stated with `N2H2HarmWinStmt`) rather than the later leaves of
`Prop1617HeadlineV4.lean` (`N2H2WinReprStmt`, `N2ZPairLipStmt`), whose producers
`D3Plus.n2H2HarmWin_of_repr` and `D3Plus.n2ZPairOsc_of_lip` are the same reductions in the other
direction; both routes give the identical headline statements `theorem1_6`, `theorem1_7`.

Source: Sheffield, arXiv:1012.4797, Proposition 1.6 (p. 25) and Proposition 1.7. The node
decomposition is the project's; no step of the paper is re-proved here.
-/

noncomputable section

namespace QuantumZipper

/-- **Proposition 1.7 from the single open node `N2ZFirstModeVarStmt`.** No other hypothesis. -/
theorem theorem1_7_of_firstModeVar (h : D3Plus.N2ZFirstModeVarStmt) : theorem1_7 :=
  theorem1_7_of_win D3Plus.n2H2HarmWinStmt_holds D3Plus.n2H3SplitWinStmt_holds
    (D3Plus.n2ZPairOsc_of_firstMode (D3Plus.n2ZFirstMode_of_var h))

/-- **Proposition 1.6 from the single open node `N2ZFirstModeVarStmt`.** No other hypothesis:
nodes B′ (global and representation) and C′ are discharged by
`prop16PalmGlobalStmt_holds_bdryMom`, `prop16PalmRepStmt_holds` and
`prop16PalmShiftHarmStmt_holds`, the D3⁺(i) node by `d3PlusIN2Rich_of_win`, and the three
window nodes as in `theorem1_7_of_firstModeVar`. -/
theorem theorem1_6_of_firstModeVar (h : D3Plus.N2ZFirstModeVarStmt) : theorem1_6 :=
  theorem1_6_of_win Prop16Asm.prop16PalmRepStmt_holds Prop16Asm.prop16PalmGlobalStmt_holds_bdryMom
    D3Plus.n2H2HarmWinStmt_holds D3Plus.n2H3SplitWinStmt_holds
    (D3Plus.n2ZPairOsc_of_firstMode (D3Plus.n2ZFirstMode_of_var h))
    Prop16Asm.prop16PalmShiftHarmStmt_holds

end QuantumZipper
