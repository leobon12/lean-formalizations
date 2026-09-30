import QuantumZipper.Proofs.Thm18.A1RFWire
import QuantumZipper.Proofs.Thm18.G3Pl4Node
import QuantumZipper.Proofs.Thm18.ASep2Wedge
import QuantumZipper.Proofs.Thm18.ASepGCSep
import QuantumZipper.Proofs.Thm18.G3ZcFormat
import QuantumZipper.Proofs.Thm18.Thm18PaperMOBridge
import QuantumZipper.Proofs.Thm18.ASep4Main
import QuantumZipper.Proofs.Thm18.G3ZqResc3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3PATH (12): Theorem 1.8 with the curve zoom routed through the fixed-path Palm limit (D92)

`theorem1_8PaperMO_of_leaves5T`: copy of `theorem1_8PaperMO_of_leaves5` (A1RFWire) whose only use
of `G3TCurveStmt` and `G3PlPhiUnscaledStmt` was to produce the step-5T transfer
`G3WedgeFreeTransferStmt`; that node is now taken directly. Headline
`theorem1_8PaperMO_of_open4Z`: `theorem1_8PaperMO` from `A1RFSmearContStmt`,
`G1WedgePalmLimStmt`, and the two G3 zoom leaves `G3ZqResclRegStmt` (a.s. regularity for the
rescaling identity) and `G3ZqPathSmallUStmt` (fixed-path two-point Palm limit of the unscaled
wedge), with A-sep discharged (`ASep.g4SepScale0Stmt_holds`). Wiring only.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18

open Thm18Asm LocLen

/-- **Theorem 1.8 (paper form) from the step-5T transfer node** (copy of
`theorem1_8PaperMO_of_leaves5`). -/
theorem theorem1_8PaperMO_of_leaves5T
    (hFull : A1RFFullYStmt)
    (hWPZ : G1WedgePalmZoomStmt)
    (hT : G3WedgeFreeTransferStmt)
    (hP : ASep.G4SepPath0Stmt) (hGC : ASep.GoodCMeasStmt) :
    theorem1_8PaperMO := by
  have hX1 : BaseFin.BaseFiniteStmt :=
    BaseFin2.baseFinite_of_yMerge_tail SWCore.yMergeOffTipStmt_holds
      (BaseFin2.sleBaseTail_of_fieldLawler FieldLawler.fieldLawlerReturn_holds)
  have hSep0 : ASep.G4SepRep0Stmt :=
    ASep.g4SepRep0Stmt_of_iter hGC (ASep.g4SepIter0Stmt_of_path hP)
  have hZ2 : G1Z2SideGoodStmt := g1Z2SideGoodStmt_of_area
    (g1Z2SideAreaStmt_of_sel (g1Z2SideAreaSelStmt_of_top G1Top.g1Z2SideTopSelStmt_holds))
  have hRFac : G1RerootFactorStmt := g1RerootFactorStmt_of_good hZ2
  have hSSRA : G1SideShiftRegAStmt := g1SideShiftRegAStmt_of_good hZ2
  have hA1b : G1ZA1bSideExactArcStmt :=
    A1RF.g1ZA1bSideExactArcStmt_of_full hFull
  have hG1 := top18_g1Stmt hX1 hRFac hSSRA hWPZ hZ2 hA1b
  have hG3 : G3PaperStmt :=
    g3PaperStmt_of_nodes (g3JointConstInvStmt_of_regA hRFac hSSRA)
      (g3JointPalmConstStmt_of (top18_g3JointRerootStmt hX1 hRFac hZ2 hA1b)
        (top18_g1RerootStmt hX1 hRFac hZ2 hA1b)
        g1SideBdryRegStmt_holds
        (g1SideTranslMeasStmt_of_good (g1RegExStmt_of_rest g1RegRepRestStmt_holds) hZ2)
        (g1SideConstDataStmt_of (g1RegExStmt_of_rest g1RegRepRestStmt_holds) hZ2))
      (g3JointPalmToWedgeStmt_of (g1RegExStmt_of_rest g1RegRepRestStmt_holds)
        g1SideTransportIdStmt_holds)
      (g3WedgePalmDecStmt_of_transfer hT)
  have hZO : ZipOffExactAStmt := zipOffExactAStmt_of_good hX1 (zipGoodStmt_holds0 hX1 hSep0)
  have hG : UnzDriverGoodStmt := unzDriverGoodStmt_of_radial hX1 (unzRadialGoodStmt_holds hX1)
  have hSF : DownLenScaleFieldReadStmt :=
    RTMeas.downLenScaleFieldReadStmt_of_reg RTMeas.piecesLenRegStmt_holds RTMeas.areaRegStmt_holds
  have hCore := maskPullCoreStmt_of_growth_mass circAvgLogGrowthStmt_holds
    RTBeur.pullMassBoundStmt_holds
  have hMF := maskExactFull_of_pullCore hCore
  have hDM := downDataMeasCStmt_of_scaleField hSF
  have hGr' := g4GroupMOStmt_of_read (piecesReadStmt_of hDM RTMeas.upPiecesReadStmt_holds)
    (ASep.moLawContStmt_of0 hX1 hSep0 hMF hZO)
    (ASep.moInverseExactStmt_of0 hX1 hSep0 hMF hDM hZO (ASep.zipOffExactUnzAStmt_holds0 hX1 hSep0))
    (moNegCocycleExactStmt_of hX1 hMF (maskExactUnzAStmt_of hX1 hG (unzGrowthStmt_holds hX1)))
  intro γ hγ hγ2 Ω _ P _ B Y hB hY hI
  have hS : Thm18Setting γ P B Y := ⟨hγ, hγ2, hB, hY, hI⟩
  have hIn := thm18Inputs_of_setting hS
  have hEq := f1ArcStmt_of_X1 hX1 γ P B Y hS hIn
  obtain ⟨hL, hR⟩ := hG1 γ P B Y hS hIn
  refine ⟨⟨hL, hR, hG3 γ P B Y hS hIn hL hR hEq⟩, ?_,
    ASep.rt6_clause1MO_core0 hX1 hSep0 hCore hDM hZO hS hIn, hGr' γ P B Y hS hIn,
    fun t => ASep.lawMO_of0 hX1 hSep0 hMF hZO hS hIn t⟩
  filter_upwards [hEq, lenPosArcStmt_of_X1 hX1 γ P B Y hS hIn] with ω he hp
  exact fun t ht => ⟨he t ht, fun htp => hp t htp⟩

/-- **Theorem 1.8 (paper form, D87) from the remaining open leaves after D92.** -/
theorem theorem1_8PaperMO_of_open4Z (hCs : A1RFSmearContStmt) (hLim : G1WedgePalmLimStmt)
    (hResc : G3Zq.G3ZqResclRegStmt) (hPath : G3Zq.G3ZqPathSmallUStmt) : theorem1_8PaperMO :=
  theorem1_8PaperMO_of_leaves5T (a1rfFullYStmt_of_smear hCs) (g1WedgePalmZoomStmt_of_lim hLim)
    (G3Zq.g3WedgeFreeTransferStmt_of_pathU (G3Zq.g3ZqResclIdStmt_of_reg hResc) hPath)
    (ASep.g4SepPath0Stmt_of_scale ASep.g4SepScale0Stmt_holds) ASep.GC.goodCMeasStmt_holds

end R18
end QuantumZipper
