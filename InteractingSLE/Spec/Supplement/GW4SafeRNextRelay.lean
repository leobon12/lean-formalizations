/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRNextWire
import InteractingSLE.Spec.Supplement.GW4FixWire

/-!
# Theorem 1.4 relay with the conditional component line input

These are conditional assembly theorems. The only replacement of the previous
relay's `GW4RelSafeRStatement` input is the explicitly unproved mathematical
input `GW4ComponentLinesStatement`; the safe law is derived in `GW4SafeRNextWire`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW4Fix

open Wire

/-- The late assembly with GW4 reduced to the component line hypothesis. -/
theorem theorem14Statement_late_componentLines
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hBR : BR4aPath.BR4aHullDetStatement.{u}) (hD : Supp8.GB6.GB6HullDetStatement.{u})
    (hTests : GW2TipSystem.GW2RootTestStatement.{u}) (hA : GW2aCont.GW2aContainmentRegStatement.{u})
    (hDS : SB.SB4DistinctSeedRegStatement.{u}) (hIA : SB.SB4InitialArcRegStatement.{u})
    (hTerminal : GW1Laws.TerminalPathStatement.{u})
    (hpair : WalkPiece.WalkPiecePairRegStatement.{u}) (hM : WalkLaw.WalkUnionMeanRegAEStatement.{u})
    (hLines : GW4ComponentLinesStatement.{u}) :
    Theorem14Statement.{u} := by
  have hBR4a := BR4aPath.br4aStatement_of_hullDet hBR h12 h13
  have h12p := Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13
  have hGB6 := gb6RestartStatement_of_hullDet_now h12₀ h13₀ hD
  have hG := BRLeaf.gb6PrefixPairStatement_of_hullDet hD h12 h13 h12₀ h13₀
  have hRetarget := GW1Det.retargetPathStatement hBR4a h12p h13 h13₀
  have hClock := GW1Laws.walkLaunchClockStatement_of_paths hGB6 h12p h13 h13₀ hTerminal hRetarget
  have hU := GW2TipSystem.gw2TipJointUnboundedStatement_of_candR
    (GW2TipSystem.gw2RootCandRStatement_of_test hTests)
  have hEx := GW2Tip.gw2TipExhaustionAllQStatement_of_canonAllQ h12 h13
    (GW2Tip.gw2TipExhaustionCanonAllQStatement_of_jointUnbounded hU)
  have hCone : LightCone14Statement.{u} :=
    lightCone14Statement_of_inputs_late h13 h13₀ hBR4a hGB6 hG h12p hEx hA
  have hF := sbFrontierRegStatement_of_current hCone
    (SB.sbRegStatement_of_sb4_sb5 (SB.sb4RegStatement_of_distinctSeed hDS)
      (SB.sb5RegStatement_of_inputs (BR3Ref.gw0ForwardStatement_of_theorem13 h13₀) hIA hDS))
  obtain ⟨hGR, hGL⟩ := GW1WalkExit.paramEveryRegStatements_of_walkClock hGB6 h13 h13₀ hClock
  have hPR := GW1X.rightWalkProperRegStatement_of_gw1ParamR51
    (GW1X.gw1ParamR51Statement_of_everyReg hGR)
  have hPL := WalkProper.leftWalkProperRegStatement_of_everyReg hGL
  have hS := GW1X.walkConnectorSideRegStatement_of_theorem13 h13₀
  have hNP := WalkPiece.walkPieceContinuumRegStatement_of_pair hPR hPL hpair
  have hNC := WalkCont.walkNoCommonContinuumRegStatement_of_pieces hPR hS hNP
  have hGeom := LateReg.gw3GeometryRegStatement_of_walks_lateReg hPR hPL hA hF
    (GW3SidedProof.rightWalkNegRealRegStatement_of_pieces hPR hS hNP)
  have hCO := LateReg.walkContactOrderRegStatement_of_inputs_lateReg hGB6 h13 h13₀ hClock hA
  have hVO := LateReg.counterflowWallOrderRegStatement_of_inputs_lateReg hGB6 h13 h13₀ hClock hA
  have hPS := LateReg.walkPocketShapeRegStatement_of_det_lateReg PocketMirror.pocketShapeDetStatement hCO hNC hF hA
    hGeom
  have hB := GW4BarrierSelf.gw4BarrierSelfRegStatement_of_walks h13 hPR hPL hNC hF hCO hPS hVO
  have hO := GW3Sided.betweenComponentsOpenRegStatement_of_geometry hGeom
  have hWB := GW4R51.gw3WordBoundRegStatement_of_inputs hO
    (BR3Ref.gw0ForwardStatement_of_theorem13 h13₀) hS
  exact theorem14Statement_late h12 h13 h12₀ h13₀ hBR hD hTests hA hDS hIA hTerminal hpair hM
    (GW4Fix.gw4RelativeLawRegStatement_of_componentLines h12 h13 h12₀ h13₀
      (GW4Reg.gw4BarrierPocketRegStatement_of_self hB) hWB hLines)

/-- The relay assembly with GW4 reduced to the component line hypothesis. -/
theorem theorem14Statement_relay_componentLines
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hBR : Supp8.HullDetGen.BR4aRelChainStatement.{u})
    (hSafe : Supp8.Q3Stop.GB6RelSafeStatement.{u})
    (hTests : GW2TipSystem.GW2RootTestStatement.{u})
    (hSB3 : SB.SB3InductionGenStatement.{u})
    (hDS : SB.Leaf.SB4DistinctSeedLaunchTailStatement.{u})
    (hIA : SB.Leaf.SB4InitialArcLaunchTailStatement.{u})
    (hBW1 : BW1.BW1Statement.{u}) (hDetTerm : BW1Term.DetTerminalStatement)
    (hPhysTerm : BW1Term.TerminalPhysStatement)
    (hAR : WalkSide.PrefixMarkedLocalStatement.{u} (-(Real.pi / 2)) true)
    (hBRc : WalkSide.PrefixChartVersionStatement.{u} (-(Real.pi / 2)) true)
    (hAL : WalkSide.PrefixMarkedLocalStatement.{u} (Real.pi / 2) false)
    (hBLc : WalkSide.PrefixChartVersionStatement.{u} (Real.pi / 2) false)
    (hN : WalkBdry.WalkNormChartStatement.{u}) (hPG : WalkBdry.WalkPairGeomStatement.{u})
    (hLines : GW4ComponentLinesStatement.{u}) :
    Theorem14Statement.{u} := by
  have hBR' := Supp8.HullDetGen.br4aHullDetStatement_of_relChain hBR h12 h13 h12₀ h13₀
  have hBR4a := BR4aPath.br4aStatement_of_hullDet hBR' h12 h13
  have hD := Supp8.Q3Stop.gb6HullDetStatement_of_liveReadout_relSafe
    Supp8.GB6.GaugeE.gb6LiveReadoutStatement hSafe
  have hFix := GW2aForce.flowFixedTimeInteriorStatement_of_thm13 h13
  have hForce := GW2aConn.gw2aConnectorForcingStatement_of_theorem13 h13 h13₀
  have hA := GW2aStep.gw2aContainmentRegStatement_of_bw1 hD h12 h13 h12₀ h13₀ hBW1 hFix hForce hBR4a
  have hGB6 := gb6RestartStatement_of_hullDet_now h12₀ h13₀ hD
  have h12p := Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13
  have hTerminal := BW1Term.terminalPathStatement_of_bw1 hBW1 hDetTerm hPhysTerm h12p h13 h13₀
  have hRetarget := GW1Det.retargetPathStatement hBR4a h12p h13 h13₀
  have hClock := GW1Laws.walkLaunchClockStatement_of_paths hGB6 h12p h13 h13₀ hTerminal hRetarget
  obtain ⟨hGR, hGL⟩ := GW1WalkExit.paramEveryRegStatements_of_walkClock hGB6 h13 h13₀ hClock
  have hPR := GW1X.rightWalkProperRegStatement_of_gw1ParamR51
    (GW1X.gw1ParamR51Statement_of_everyReg hGR)
  have hPL := WalkProper.leftWalkProperRegStatement_of_everyReg hGL
  have hSR := WalkSide.walkPrefixSideStatement_of_prefix h12p h13
    (θ := -(Real.pi / 2)) ⟨le_rfl, by linarith [Real.pi_pos]⟩ hAR hBRc
  have hSL := WalkSide.walkPrefixSideStatement_of_prefix h12p h13
    (θ := Real.pi / 2) ⟨by linarith [Real.pi_pos], le_rfl⟩ hAL hBLc
  have hpair := WalkBdry.walkPiecePairRegStatement_of_side h12p h13 hPR hPL hSR hSL hPG
  have hM := WalkMean.walkUnionMeanRegAEStatement_of_bdry h12p h13
    (WalkBdry.walkUnionBdryStatement_of_side h12p h13 hPR hPL hSR hSL hN)
  obtain ⟨hDS', hIA'⟩ := SB.Leaf.sb4RetainedTailStatements_of_launch hSB3 h12 h13 hDS hIA
  exact theorem14Statement_late_componentLines h12 h13 h12₀ h13₀ hBR' hD hTests hA
    (SB.sb4DistinctSeedRegStatement_of_retainedTail hDS')
    (SB.sb4InitialArcRegStatement_of_retainedTail hIA') hTerminal hpair hM hLines

end InteractingSLE.Theorem14.GW4Fix
