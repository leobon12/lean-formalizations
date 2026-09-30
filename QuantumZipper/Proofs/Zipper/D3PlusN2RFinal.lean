import QuantumZipper.Proofs.Zipper.D3PlusN2RMix
import QuantumZipper.Proofs.Zipper.D3PlusN2ContPair

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Proposition 1.7 from the open N2 nodes on the restricted window index (Decision D36)

Task D36-IMPL, step (6). Sheffield, arXiv:1012.4797, Proposition 1.7, through the D3⁺(i) chain
(Duplantier–Miller–Sheffield, arXiv:1409.7055, Prop. 4.7(ii) pp. 77–78 and Prop. 4.8 p. 79), with
the N2 window index restricted to folded circles and bounded compactly supported densities inside
the window (`WinIdx K`, `D3PlusN2RIdx.lean`).

Pure bookkeeping (no new mathematics):
* heart: `n2ZHeartWin_of_nodes` (`D3PlusN2RMix.lean`; H1 proved at folded circles);
* H2': `n2HLatTVWin_of_harm` (`D3PlusN2RWin.lean`; free half `map_latWinFreeW_eq` proved);
* H3': `n2HModelDecompWin_of_split` (`D3PlusN2RHeart.lean`);
* model-side window transfer: `n2ZModelLocWin_of_reg` (`D3PlusN2RRead.lean`) with the same
  a.s.-regularity node as the unrestricted chain, `n2ZModelReg_of_contPair` and
  `n2ZContPair_of_osc` (`D3PlusN2ModelLocPair.lean`, `D3PlusN2ContPair.lean`);
* wedge-side window transfer: `n2ZWedgeLocWin_holds` (`D3PlusN2RZero.lean`, proved);
* assembly: `d3PlusIN2TmZeroWin_of_nodes` (`D3PlusN2RZero.lean`) and
  `S5.FieldLaw.Raw.theorem1_7_of_tmZero`.

**Open inputs** of `theorem1_7_of_winOpen`: `N2H2HarmWinStmt` (model-side Cameron–Martin half of
H2 on the restricted index), `N2H3SplitWinStmt` (lateral/radial splitting on the restricted index)
and `N2ZPairOscStmt` (uniform oscillation bound of the circle-regularized test-function pairings;
it concerns the pairings read by `locFieldFull`, not the window index, and is unchanged by D36).
-/

noncomputable section

namespace QuantumZipper
namespace D3Plus

/-- **D3⁺(i) node TmZero from the open restricted N2 nodes.** -/
theorem d3PlusIN2TmZero_of_winOpen (hHarm : N2H2HarmWinStmt) (hSp : N2H3SplitWinStmt)
    (hOsc : N2ZPairOscStmt) : D3PlusIN2TmZeroStmt :=
  d3PlusIN2TmZeroWin_of_nodes
    (n2ZHeartWin_of_nodes (n2HLatTVWin_of_harm hHarm) (n2HModelDecompWin_of_split hSp))
    (n2ZModelLocWin_of_reg (n2ZModelReg_of_contPair (n2ZContPair_of_osc hOsc)))
    n2ZWedgeLocWin_holds

/-- **Proposition 1.7** (Sheffield, arXiv:1012.4797) from the open N2 nodes on the restricted
window index (Decision D36): the model-side Cameron–Martin half of H2, the H3 splitting node and
the uniform pairing oscillation bound. -/
theorem theorem1_7_of_winOpen (hHarm : N2H2HarmWinStmt) (hSp : N2H3SplitWinStmt)
    (hOsc : N2ZPairOscStmt) : theorem1_7 :=
  S5.FieldLaw.Raw.theorem1_7_of_tmZero (d3PlusIN2TmZero_of_winOpen hHarm hSp hOsc)

end D3Plus
end QuantumZipper
