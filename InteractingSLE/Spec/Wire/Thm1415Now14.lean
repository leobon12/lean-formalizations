/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm1415Current14
import InteractingSLE.Spec.Supplement.GB6RelDrv
import InteractingSLE.Spec.Supplement.GW1LawsFinal
import InteractingSLE.Spec.Supplement.GW2TestClaims
import InteractingSLE.Spec.Supplement.WalkLeafWire
import InteractingSLE.Spec.Supplement.GW1PathLeft
import InteractingSLE.Spec.Supplement.GW4LeafWall
import InteractingSLE.Spec.Supplement.BRLeafGB6

/-!
# Theorem 1.4 after relative stopped determination and the repaired root rule

Conditional assembly of the four unchanged R51 clauses. The root-test input
uses the regularized counterflow record (R75). Its crossing and comparison
obligations remain open; the landed test bookkeeping does not discharge them.
GW1's conditional laws and the walk launch laws are proved, while the two
path identifications, relative stopped law, and sewing inputs remain explicit.
-/

set_option autoImplicit false
noncomputable section
universe u
namespace InteractingSLE.Wire
open Theorem14

/-- GB6 from its hull determination, with completeness supplied by Theorem 1.3. -/
theorem gb6RestartStatement_of_hullDet_now
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hD : Supp8.GB6.GB6HullDetStatement.{u}) : Supp8.GB6.GB6RestartStatement.{u} := by
  have hComplete : Supp8.GB6.CompleteSixteenDivStatement := by
    intro κ hκ _ nL nR xL xR ρL ρR hF
    exact completeForceWord_of_theorem13 h13₀ (div_pos (by norm_num) hκ) ρL ρR hF
  exact Supp8.GB6.gb6RestartStatement_of_hullDet
    (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12₀ h13₀) h13₀ hComplete hD

/-- Current conditional assembly: conditional restart laws, launch locality,
and the repaired root rule are all supplied by landed theorems. -/
theorem theorem14Statement_now
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hBR4a : BR4a.BR4aStatement.{u})
    (hD : Supp8.GB6.GB6HullDetStatement.{u})
    (hTests : GW2TipSystem.GW2RootTestStatement.{u}) (hA : GW2aContainmentStatement.{u})
    (hDS : SB.SB4DistinctSeedRegStatement.{u}) (hIA : SB.SB4InitialArcRegStatement.{u})
    (hTerminal : GW1Laws.TerminalPathStatement.{u}) (hRetarget : GW1Laws.RetargetPathStatement.{u})
    (hpair : WalkPiece.WalkPiecePairRegStatement.{u}) (hM : WalkLaw.WalkUnionMeanRegAEStatement.{u})
    (hB : GW4Reg.GW4BarrierSelfRegStatement.{u}) (hLaw : GW4Reg.GW4RelativeLawRegStatement.{u}) :
    Theorem14Statement.{u} := by
  have h12p := Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13
  have hGB6 := gb6RestartStatement_of_hullDet_now h12₀ h13₀ hD
  have hG := BRLeaf.gb6PrefixPairStatement_of_hullDet hD h12 h13 h12₀ h13₀
  have hU := GW2TipSystem.gw2TipJointUnboundedStatement_of_candR
    (GW2TipSystem.gw2RootCandRStatement_of_test hTests)
  have hClock := GW1Laws.walkLaunchClockStatement_of_paths hGB6 h12p h13 h13₀ hTerminal hRetarget
  exact theorem14Statement_current h12 h13 h13₀ hBR4a hGB6 hG hU hA hDS hIA hClock hpair
    (WalkLeaf.gw3UnionLawBetweenRegStatement_of_unionMean h12p h13 hM) hB hLaw

/-- Expanded open inputs. GB6's good-code and stopped-determination steps are
proved; its relative stopped coupling and exhausting measurable versions remain.
GW2's root tests retain the exact full stage-start filtration. -/
theorem theorem14Statement_now_expanded
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hBR4a : BR4a.BR4aStatement.{u})
    (hext : ∀ k : ℝ, 4 < k → Restart.StoppedExtend.StoppedHullExtendStatement.{0} k)
    (hV : Supp8.GB6.RelDrv.GB6RelVersionStatement.{u})
    (hK : Supp8.GB6.RelDrv.GB6RelStopKernelStatement.{u})
    (hTests : GW2TipSystem.GW2RootTestStatement.{u}) (hA : GW2aContainmentStatement.{u})
    (hDS : SB.SB4DistinctSeedRetainedTailStatement.{u})
    (hIA : SB.SB4InitialArcRetainedTailStatement.{u})
    (hTerminal : GW1Laws.TerminalPathStatement.{u})
    (hRetargetDet : GW1Path.DetRetargetStatement) (hConnector : GW1Path.ConnectorPhysStatement)
    (hpair : WalkPiece.WalkPiecePairRegStatement.{u}) (hM : WalkLaw.WalkUnionMeanRegAEStatement.{u})
    (hPS : GW4BarrierSelf.WalkPocketShapeRegStatement.{u})
    (hLaw : GW4Reg.GW4RelativeLawRegStatement.{u}) : Theorem14Statement.{u} := by
  have hD := Supp8.GB6.gb6HullDetStatement_of_relDrvDet
    (Supp8.GB6.RelDrv.gb6RelDrvDetStatement_of_stopKernel hext hV hK)
  have hGB6 := gb6RestartStatement_of_hullDet_now h12₀ h13₀ hD
  have hG := BRLeaf.gb6PrefixPairStatement_of_hullDet hD h12 h13 h12₀ h13₀
  have h12p := Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13
  have hDS' := SB.sb4DistinctSeedRegStatement_of_retainedTail hDS
  have hIA' := SB.sb4InitialArcRegStatement_of_retainedTail hIA
  have hU := GW2TipSystem.gw2TipJointUnboundedStatement_of_candR
    (GW2TipSystem.gw2RootCandRStatement_of_test hTests)
  have hEx := GW2Tip.gw2TipExhaustionAllQStatement_of_canonAllQ h12 h13
    (GW2Tip.gw2TipExhaustionCanonAllQStatement_of_jointUnbounded hU)
  have hCone : LightCone14Statement.{u} :=
    lightCone14Statement_of_inputs_current h13 h13₀ hBR4a hGB6 hG h12p hEx hA
  have hF := sbFrontierRegStatement_of_current hCone
    (SB.sbRegStatement_of_sb4_sb5 (SB.sb4RegStatement_of_distinctSeed hDS')
      (SB.sb5RegStatement_of_inputs (BR3Ref.gw0ForwardStatement_of_theorem13 h13₀) hIA' hDS'))
  have hRetarget := GW1Path.retargetPathStatement_of_det hBR4a h12p h13 h13₀ hRetargetDet hConnector
  have hClock := GW1Laws.walkLaunchClockStatement_of_paths hGB6 h12p h13 h13₀ hTerminal hRetarget
  obtain ⟨hGR, hGL⟩ := GW1WalkExit.paramEveryRegStatements_of_walkClock hGB6 h13 h13₀ hClock
  have hPR := GW1X.rightWalkProperRegStatement_of_gw1ParamR51
    (GW1X.gw1ParamR51Statement_of_everyReg hGR)
  have hPL := WalkProper.leftWalkProperRegStatement_of_everyReg hGL
  have hS := GW1X.walkConnectorSideRegStatement_of_theorem13 h13₀
  have hNP := WalkPiece.walkPieceContinuumRegStatement_of_pair hPR hPL hpair
  have hNC := WalkCont.walkNoCommonContinuumRegStatement_of_pieces hPR hS hNP
  have hCO := GW4Leaf.walkContactOrderRegStatement_of_inputs hGB6 h13 h13₀ hClock hA
  have hVO := GW4Leaf.counterflowWallOrderRegStatement_of_inputs hGB6 h13 h13₀ hClock hA
  have hB := GW4BarrierSelf.gw4BarrierSelfRegStatement_of_walks h13 hPR hPL hNC hF hCO hPS hVO
  exact theorem14Statement_now h12 h13 h12₀ h13₀ hBR4a hD hTests hA hDS' hIA'
    hTerminal hRetarget hpair hM hB hLaw

end InteractingSLE.Wire
