import QuantumZipper.Proofs.Thm18.R18Nodes
import QuantumZipper.Proofs.Zipper.LocLenHeadlineFinal

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18: the open-arc E6 and F1 nodes of the paper-form Theorem 1.8, from X1

The Theorem 1.3 open-arc campaign (D75, `handoff/FOLLOW-PAPER-13.md`) proves Theorem 1.3 from the
base-finiteness fact X1 (`LocLen.theorem1_3_of_arcNodes_final`). Its intermediate conclusions
`LocLen.E6StmtArc` (unzipping by quantum length preserves the law, Sheffield p. 26 (3) for `t < 0`)
and `LocLen.F1StmtArc` (the two open-arc lengths along `η` agree, Sheffield p. 26 "their quantum
boundary lengths along `η` agree") are exposed here, and give the nodes `R18.F1ArcStmt` and
`R18.LenPosArcStmt` of the paper-form Theorem 1.8 (wiring only; the chain is copied from
`LocLenHeadline*.lean`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace R18

open Thm18Asm LocLen

/-- **E6 with open arcs from X1** (the chain of `LocLen.theorem1_3_of_arcNodes_final`). -/
theorem e6StmtArc_of_X1 (hX1 : BaseFin.BaseFiniteStmt) : LocLen.E6StmtArc := by
  have hYO := SWCore.yMergeOffTipStmt_holds
  have hC : LenPairCocycleArcStmt := lenPairCocycleArc_of_yMergeOffTip hYO
  have hF : LenFiniteArcStmt :=
    lenFiniteArc_of_baseFinite hX1 (wedgePairCocycleArc_of_yMergeOffTip hYO)
  have hsm : LenStrictMonoArcStmt := lenStrictMonoArc_of_yMergeOffTip hYO hC hF
  have hSZ := R5c.hitScaleZipArcStmt_of_nodes hsm hF (pStarAreaAll_of_yMergeOffTip hYO)
  have h6 := e6NodeStmtRichArc_of_nodes hSZ lenCollidedAllArcStmt_holds
    canonZipRawAllArcStmt_holds e6PalmRegArc_holds
  exact e6UpRichArc_of_meas (R5c.unzipMeasArc_of_hitScaleZip hSZ)
    (h6 (E5.e5Rich_of_repr' (D3Plus.d3PlusIRich_of_N2 D3Plus.d3PlusIN2RichStmt_holds)
      (D3Plus.d3PlusIIRich_of_tWin (D3Plus.lsccTWinInd_of_hitPath D3Plus.hitPathIndStmt_holds)
        D3Plus.hitLevSpreadStmt_holds)
      (E5.e5ReprG'_of_parts3 (E5.e5LvlZoomParts3Stmt_of_partsB E5.e5LvlZoomPartsB_holds)
        E5.zoomModelNonempty_holds) E4Grid.e4_unconditional))

/-- **F1 with open arcs from X1** (the chain of `LocLen.theorem1_3_of_arcNodes_final`). -/
theorem f1StmtArc_of_X1 (hX1 : BaseFin.BaseFiniteStmt) : LocLen.F1StmtArc := by
  have hYO := SWCore.yMergeOffTipStmt_holds
  have hC : LenPairCocycleArcStmt := lenPairCocycleArc_of_yMergeOffTip hYO
  have hF : LenFiniteArcStmt :=
    lenFiniteArc_of_baseFinite hX1 (wedgePairCocycleArc_of_yMergeOffTip hYO)
  have hsm : LenStrictMonoArcStmt := lenStrictMonoArc_of_yMergeOffTip hYO hC hF
  have hI : R5c.PStarLenInfArcStmt :=
    R5c.pStarLenInfArc_of (F1.pStarCanonLawStmt_of F1.wedgeAddConstLawStmt_holds)
      (pStarZipLenInputsLoc_of_yMergeOffTip hYO) R5c.lenReadTimeArc_holds hsm
      (pStarGoodOffAll_of_yMergeOffTip hYO) (unzipBdryPosArc_of_yMergeOffTip hYO) hF
  have hLU : LenLeftUnbddArcStmt := lenLeftUnbddArc_of_pStarLenInf hI
  have hSZ := R5c.hitScaleZipArcStmt_of_nodes hsm hF (pStarAreaAll_of_yMergeOffTip hYO)
  exact f1NodeArc_of_inputs hYO hsm hC (lenLeftRegArc_of_yMergeOffTip hYO hC hF) hLU hF
    (lenRegArc_of_yMergeOffTip hYO hC hF hLU)
    (lenReadRegArc_of_yMergeOffTip hYO hC hF (lenReadRegMeasArc_of_yMergeOffTip hYO))
    (R5c.unzipMeasArc_of_hitScaleZip hSZ) (e6StmtArc_of_X1 hX1)

/-- **The paper-form F1 node from X1**: in the Theorem 1.8 setting the open-arc lengths along `η`
agree a.s. for all `t ≥ 0`. -/
theorem f1ArcStmt_of_X1 (hX1 : BaseFin.BaseFiniteStmt) : F1ArcStmt := by
  intro γ Ω _ P _ B Y hS _
  have h := f1StmtArc_of_X1 hX1 (γ ^ 2) P Y B (isPStarSample_of_setting hS)
  rw [Real.sqrt_sq hS.1.le] at h
  exact h

/-- **The paper-form length non-degeneracy from X1**: a.s., for every `t > 0` the left open-arc
length of `η[0,t]` is positive (strict monotonicity from `0`) and finite. -/
theorem lenPosArcStmt_of_X1 (hX1 : BaseFin.BaseFiniteStmt) : LenPosArcStmt := by
  intro γ Ω _ P _ B Y hS _
  have hYO := SWCore.yMergeOffTipStmt_holds
  have hC : LenPairCocycleArcStmt := lenPairCocycleArc_of_yMergeOffTip hYO
  have hF : LenFiniteArcStmt :=
    lenFiniteArc_of_baseFinite hX1 (wedgePairCocycleArc_of_yMergeOffTip hYO)
  have hsm := lenStrictMonoArc_of_yMergeOffTip hYO hC hF (γ ^ 2) P Y B (isPStarSample_of_setting hS)
  have hfin := ae_unzipLengthsArc_lt_top_all hC hF (γ ^ 2) P Y B (isPStarSample_of_setting hS)
  rw [Real.sqrt_sq hS.1.le] at hsm hfin
  filter_upwards [hsm, hfin] with ω hm hf t ht
  exact ⟨pos_of_gt (hm (le_refl (0 : ℝ)) ht.le ht), (hf t ht.le).1⟩

end R18
end QuantumZipper
