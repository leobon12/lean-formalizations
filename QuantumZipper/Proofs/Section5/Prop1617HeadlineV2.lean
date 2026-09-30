import QuantumZipper.Proofs.Section5.Prop16Headline
import QuantumZipper.Proofs.Section5.Prop16MarkovMask2Final
import QuantumZipper.Proofs.Zipper.D3PlusN2RFinal
import QuantumZipper.Proofs.Zipper.D3PlusN2Final

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Propositions 1.6 and 1.7: headline wiring from the remaining open nodes (version 2)

Task WIRE-P16P17-V2. Wiring only, no new mathematics: the two headline propositions of Sheffield,
*Conformal weldings of random surfaces* (arXiv:1012.4797), Prop. 1.6 (p. 25) and Prop. 1.7, are
stated here from the current, smallest set of open nodes.

* `theorem1_7_of_win` is Proposition 1.7 from the three restricted-window N2 nodes, the
  restatement of `D3Plus.theorem1_7_of_winOpen` (`Proofs/Zipper/D3PlusN2RFinal.lean`, Decision D36).
* `d3PlusIN2Rich_of_win` exposes the shared D3⁺(i) node in N2 form from the same three nodes,
  through `D3Plus.d3PlusIN2TmZero_of_winOpen` and `D3Plus.d3PlusIN2Rich_of_tmZero`
  (`Proofs/Zipper/D3PlusN2Final.lean`).
* `theorem1_6_of_idWin` is Proposition 1.6 from node B′ `Prop16PalmIdMaskStmt`, D3⁺(i) in N2 form
  and node C′ in the reduced harmonic-Palm form `Prop16PalmShiftHarmStmt`, via
  `Prop16Asm.theorem1_6_of_palmHarm` (`Prop16MarkovMask2Final.lean`; its node C′ assembly uses the
  unconditional domain Markov coupling `Prop16Asm.prop16MixedFreeLocCoupling_mm`).
* `theorem1_6_of_win` is the same with node B′ further reduced to `Prop16PalmRepStmt` (items (6),
  (7) of the D30 list) plus `Prop16PalmGlobalStmt` (the global window Palm formula) by
  `Prop16Asm.prop16PalmIdMaskStmt_of_rep` (`Prop16NodeB2Rep.lean`).
* `theorem1_6_and_1_7_of_win` is the joint statement `theorem1_6 ∧ theorem1_7` from the union of
  the open nodes.

**No reduction of `Prop16PalmGlobalStmt` exists in the repository** (grepped 2026-09-28: the only
occurrences are its definition, `prop16PalmWinMaskStmt_of_rep`, `prop16PalmIdMaskStmt_of_rep` and
the two headline files; the statement has no producer). The reductions available for the window
Palm formula are `palm_formula_prop16_window_mean` (`Prop16NodeB2Mean.lean`) and
`palm_formula_prop16_window_nodes` (`Prop16NodeB2Reg.lean`), both from `Prop16ActRegStmt` and
`Prop16BdryL1Stmt`; these are the *window/intensity* forms, needed for coordinates carried by the
window set, whereas `Prop16PalmGlobalStmt` is the global form (coordinates carried by a compact
subset of `D ∪ (a,b)`, hence needing the mixed covariance there). So the latter stays a hypothesis
here. For bookkeeping: `Prop16ActRegStmt` is **proved** (`prop16ActReg_holds`,
`Prop16ActReg.lean`) and `Prop16BdryL1Stmt` is reduced to the local statement
`Prop16BdryL1LocStmt` by `prop16BdryL1Stmt_of_loc` (`Prop16ActRegBdryLoc.lean`); neither occurs as
a hypothesis of the headline theorems below.

Source: Sheffield, arXiv:1012.4797, Proposition 1.6 (p. 25) and Proposition 1.7. The node
decomposition is the project's; no step of the paper is re-proved here.
-/

noncomputable section

namespace QuantumZipper

/-- **The shared D3⁺(i) node in N2 form** from the three restricted-window N2 nodes
(`D3Plus.d3PlusIN2TmZero_of_winOpen` followed by `D3Plus.d3PlusIN2Rich_of_tmZero`). -/
theorem d3PlusIN2Rich_of_win (hHarm : D3Plus.N2H2HarmWinStmt) (hSp : D3Plus.N2H3SplitWinStmt)
    (hOsc : D3Plus.N2ZPairOscStmt) : D3Plus.D3PlusIN2RichStmt :=
  D3Plus.d3PlusIN2Rich_of_tmZero (D3Plus.d3PlusIN2TmZero_of_winOpen hHarm hSp hOsc)

/-- **Proposition 1.7** from the three open restricted-window N2 nodes: the model-side
Cameron–Martin half of H2 (`N2H2HarmWinStmt`), the lateral/radial splitting node
(`N2H3SplitWinStmt`) and the uniform oscillation bound on the circle-regularized test-function
pairings (`N2ZPairOscStmt`). Restatement of `D3Plus.theorem1_7_of_winOpen`. -/
theorem theorem1_7_of_win (hHarm : D3Plus.N2H2HarmWinStmt) (hSp : D3Plus.N2H3SplitWinStmt)
    (hOsc : D3Plus.N2ZPairOscStmt) : theorem1_7 :=
  D3Plus.theorem1_7_of_winOpen hHarm hSp hOsc

/-- **Proposition 1.6 from node B′, D3⁺(i) in N2 form and node C′.**

Remaining hypotheses:
* `hId : Prop16PalmIdMaskStmt` — node B′ (`Prop16NodeB2Rep.lean`);
* `hHarm`, `hSp`, `hOsc` — the three open restricted-window N2 nodes, feeding D3⁺(i) in N2 form
  through `d3PlusIN2Rich_of_win`;
* `hH : Prop16PalmShiftHarmStmt` — node C′ in the reduced harmonic-Palm form
  (`Prop16MarkovMask2.lean`). -/
theorem theorem1_6_of_idWin (hId : Prop16Asm.Prop16PalmIdMaskStmt)
    (hHarm : D3Plus.N2H2HarmWinStmt) (hSp : D3Plus.N2H3SplitWinStmt) (hOsc : D3Plus.N2ZPairOscStmt)
    (hH : Prop16Asm.Prop16PalmShiftHarmStmt) : theorem1_6 :=
  Prop16Asm.theorem1_6_of_palmHarm hId (d3PlusIN2Rich_of_win hHarm hSp hOsc) hH

/-- **Proposition 1.6 from the remaining open nodes, node B′ reduced.**

Remaining hypotheses:
* `hRep : Prop16PalmRepStmt` — node B′ (6), (7): the measurable representation of the masked zoom
  coordinates by a countable admissible family (`Prop16NodeB2Rep.lean`);
* `hGl : Prop16PalmGlobalStmt` — node B′ (global): the window Palm formula for coordinates carried
  by a compact subset of `D ∪ (a,b)` (`Prop16NodeB2Rep.lean`);
* `hHarm`, `hSp`, `hOsc` — the three open restricted-window N2 nodes;
* `hH : Prop16PalmShiftHarmStmt` — node C′ in the reduced harmonic-Palm form. -/
theorem theorem1_6_of_win (hRep : Prop16Asm.Prop16PalmRepStmt)
    (hGl : Prop16Asm.Prop16PalmGlobalStmt) (hHarm : D3Plus.N2H2HarmWinStmt)
    (hSp : D3Plus.N2H3SplitWinStmt) (hOsc : D3Plus.N2ZPairOscStmt)
    (hH : Prop16Asm.Prop16PalmShiftHarmStmt) : theorem1_6 :=
  theorem1_6_of_idWin (Prop16Asm.prop16PalmIdMaskStmt_of_rep hRep hGl) hHarm hSp hOsc hH

end QuantumZipper
