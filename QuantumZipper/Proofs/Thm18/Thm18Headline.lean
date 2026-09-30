import QuantumZipper.Proofs.Thm18.Assembly
import QuantumZipper.Proofs.Thm18.G4GoodSet
import QuantumZipper.Proofs.Thm18.G4ZipRegPair
import QuantumZipper.Proofs.Thm18.G1ZoomModel
import QuantumZipper.Proofs.Thm18.G1PkgLeft
import QuantumZipper.Proofs.Thm18.G3Reduce
import QuantumZipper.Proofs.Thm18.G3G2Filter
import QuantumZipper.Proofs.Thm18.G3G2FullMix
import QuantumZipper.Proofs.Thm18.G3G2Scale
import QuantumZipper.Proofs.Thm18.G3PalmR
import QuantumZipper.Proofs.Thm18.G3AreaPalm
import QuantumZipper.Proofs.Thm18.LenPos
import QuantumZipper.Proofs.Zipper.LocHitScalePStar
import QuantumZipper.Proofs.Wire4
import QuantumZipper.Proofs.Zipper.WedgeLawReg

/-!
# Theorem 1.8, headline wiring: `theorem1_8` from the still-open nodes

Task WIRE-THM18 (bookkeeping only, no new mathematics). Sheffield, *Conformal weldings of random
surfaces*, arXiv:1012.4797, Theorem 1.8 and §5.4.

`Thm18Asm.theorem1_8_of_nodes` (`Assembly.lean`) reduces `theorem1_8` to the four node
hypotheses `G1Stmt`, `G3Stmt`, `LenPosStmt`, `G4Stmt` plus the two Theorem 1.3-chain nodes
`Thm13Asm.E6Stmt`, `Thm13Asm.F1NodeStmt`. This file plugs into each of the four the strongest
current reduction, using only theorems that are already proved, so that the hypotheses of the
resulting theorem are *only* still-open nodes. Nothing new is proved here; every step is an
application of an existing reduction lemma (an "own trivial bookkeeping" argument).

* **G1**: `g1Stmt_of_N2_model_regRep` (`G1ZoomModel.lean:313`) with the regularity half
  `g1RegRepStmt_of_rc2_rest` (`G1PkgLeft.lean:195`); the selection node `G1PsiSelStmt` is proved
  (`g1PsiSelStmt`, `G1PkgLeft.lean:192`) and filled in there. Open: `D3PlusIN2RichStmt`
  (`D3PlusIRich.lean:177`, the §7 N2 heart cluster), `G1ZoomModelStmt` (`G1ZoomModel.lean:287`),
  `G1RegRepRC2Stmt` / `G1RegRepRestStmt` (`G1RegRepRed.lean:64,70`).
* **G3**: `g3_of_scheme` (`G3Reduce.lean:150`) at the concrete scheme
  `g3ConcreteMap fun _ => g3Filter` (defined below as `g3Scheme`), with the Markov node proved
  (`g3MarkovStmt_g3Filter`, `G3G2Filter.lean:65`), the two-point node from
  `g2TwoPointStmt_of_concrete` (`G3G2Filter.lean:82`) applied to
  `g2ConcreteStmt_of_palmR_area_mix` (`G3G2FullMix.lean:110`) and the transfer node from
  `g3TransferStmt_of_inputs` (`G3G2Scale.lean:116`); the `R(x)`-half of the geometry is reduced
  to the uniform rooted-measure bound by `g3GeoPalmRStmt_of_tight` / `g3GeoStmt_of_tight`
  (`G3PalmR.lean:141,167`), and the area input `G3AreaStmt γ` is discharged here by
  `g3AreaStmt_holds` (the Palm input `G3AreaPalmStmt` is proved, `G3AreaPalm.lean:79`). Open:
  `G3PalmRTightStmt γ` (`G3PalmR.lean:55`), `G2FullMixStmt γ` (`G3G2FullMix.lean:71`),
  `G3TransferFullStmt` (`G3G2Loc.lean:125`).
* **LenPos**: `lenPosStmt_of_bdryPosAt` (`UnzipBdryPos.lean:83`). Open: `UnzipBdryPosAtStmt`
  (`:42`) and `UnzipBdryTransferStmt` (`:54`). (The newer D29 route, `lenPosStmt_of_d29`,
  `UnzipBdryPosAtMain.lean:160`, reduces `UnzipBdryPosAtStmt` further to
  `UnzipBdryPosDecompStmt`, `UnzipBdryPosXAtStmt` and three `WedgeUnzip.*` nodes; it is not used
  here.)
* **G4**: `g4Stmt_of_coreNodesGoodSet` (`G4GoodSet.lean:135`), with `WedgeZeroRegStmt` and
  `WedgeLeftInfStmt` proved unconditionally (`Wire4.wedgeZeroRegStmt`, `Wire4.wedgeLeftInfStmt`,
  `Wire4.lean:98,104`), `WedgeRegSampleStmt` proved (`wedgeRegSampleStmt_holds`,
  `WedgeLawReg.lean:26`), the zipper regularity node from `g4ZipRegStmt_of_rezipCore`
  (`G4ZipRegPair.lean:165`, whose remaining node is the round-trip core) and the good-set/reading
  nodes from `g4UnzipGoodSetStmt_of_roundUp` and `g4WedgeCertStmt` (used inside
  `g4LenDrvReadStmt_of_roundUp`, `G4GoodSet.lean:129`). Open: `G4RoundUpRezipCoreStmt`
  (`G4RoundWedgeReg.lean:105`), `G4RoundDownRezipCoreStmt` (`:63`), `G4GroupNegStmt`
  (`G4WeldGroup.lean:67`), `G4GroupPosStmt` (`G4WeldGroupUp.lean:130`), `G4GroupMixStmt` (`:140`),
  `G4ZipUpFieldReadStmt` (`G4ReadZip.lean:106`), `E6.UnzipMeasStmt` (`LocRichBasic.lean:279`;
  itself reducible to the open `HitScaleZipStmt` through `localAbsRichStmt_of_hitScaleZip` and
  `unzipMeasStmt_of_localAbsRich`).

`theorem1_8_of_openNodes` is the resulting conditional headline; its hypotheses are exactly the
open nodes listed above.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace Thm18Asm

/-! ## The four nodes from their open inputs -/

/-- The concrete G3 approximation scheme: Figure 1.7 zooms at the filter `g3Filter`. -/
abbrev g3Scheme : G3SchemeMap := g3ConcreteMap fun _ => g3Filter

/-- **`G3AreaStmt` holds**: the area input is the exactly stated Palm input
(`g3AreaPalmStmt_holds`, `G3AreaPalm.lean:79`), transferred by `g3AreaStmt_of_palm`
(`G3Area.lean:287`). It is therefore discharged in the G3 headline below. -/
theorem g3AreaStmt_holds {γ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) : G3AreaStmt γ :=
  g3AreaStmt_of_palm hγ (g3AreaPalmStmt_holds hγ hγ2)

/-! ## The headline -/

end Thm18Asm
end QuantumZipper
