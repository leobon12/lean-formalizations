/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Wire.Thm1415Late14
import InteractingSLE.Spec.Wire.Thm1415Now14
import InteractingSLE.Spec.Wire.Thm1415LateGB6
import InteractingSLE.Spec.Wire.Thm1415LateCone
import InteractingSLE.Spec.Supplement.HullDetGenBR4aWire
import InteractingSLE.Spec.Supplement.GW1Borel
import InteractingSLE.Spec.Supplement.BW1TermMain
import InteractingSLE.Spec.Supplement.PocketMirrorAssembly
import InteractingSLE.Spec.Supplement.GW2aStepWire
import InteractingSLE.Spec.Supplement.SBLeafLaunchWire
import InteractingSLE.Spec.Supplement.WalkSideDom
import InteractingSLE.Spec.Supplement.WalkBdryPair
import InteractingSLE.Spec.Supplement.WalkMeanBdry

import InteractingSLE.Spec.Supplement.GB6GaugeEVersion
import InteractingSLE.Spec.Supplement.Q3StopAnnounce
import InteractingSLE.Spec.Supplement.AbsMergeFlow
import InteractingSLE.Spec.Supplement.GW2aConnMain
import InteractingSLE.Spec.Supplement.BW1LifeSafe

/-! # Theorem 1.4 after the source GB6 readout and connector discharges -/
set_option autoImplicit false
noncomputable section
universe u
namespace InteractingSLE.Wire
open Theorem14

/-- All four original clauses with the landed source readout and flow/connector proofs. -/
theorem theorem14Statement_relay_expanded
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hBR : Supp8.HullDetGen.BR4aRelChainStatement.{u})
    (hSafe : Supp8.Q3Stop.GB6RelSafeStatement.{u})
    (hTests : GW2TipSystem.GW2RootTestStatement.{u})
    (hSB3 : SB.SB3InductionGenStatement.{u})
    (hDS : SB.Leaf.SB4DistinctSeedLaunchTailStatement.{u})
    (hIA : SB.Leaf.SB4InitialArcLaunchTailStatement.{u})
    (hBWVersion : BW1Life.BW1RelVersionStatement.{u})
    (hBWSL : BW1Life.BW1RelSafeSLStatement.{u}) (hBWEnd : BW1Life.BW1EndpointStatement.{u})
    (hDetTerm : BW1Term.DetTerminalStatement)
    (hPhysTerm : BW1Term.TerminalPhysStatement)
    (hAR : WalkSide.PrefixMarkedLocalStatement.{u} (-(Real.pi / 2)) true)
    (hBRc : WalkSide.PrefixChartVersionStatement.{u} (-(Real.pi / 2)) true)
    (hAL : WalkSide.PrefixMarkedLocalStatement.{u} (Real.pi / 2) false)
    (hBLc : WalkSide.PrefixChartVersionStatement.{u} (Real.pi / 2) false)
    (hN : WalkBdry.WalkNormChartStatement.{u}) (hPG : WalkBdry.WalkPairGeomStatement.{u})
    (hLaw : GW4Reg.GW4RelativeLawRegStatement.{u}) : Theorem14Statement.{u} := by
  have hBR' := Supp8.HullDetGen.br4aHullDetStatement_of_relChain hBR h12 h13 h12₀ h13₀
  have hBR4a := BR4aPath.br4aStatement_of_hullDet hBR' h12 h13
  have hD := Supp8.Q3Stop.gb6HullDetStatement_of_liveReadout_relSafe
    Supp8.GB6.GaugeE.gb6LiveReadoutStatement hSafe
  have hFix := GW2aForce.flowFixedTimeInteriorStatement_of_thm13 h13
  have hForce := GW2aConn.gw2aConnectorForcingStatement_of_theorem13 h13 h13₀
  have h12p := Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13
  have h12p₀ := Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12₀ h13₀
  have hBW1 := BW1Life.bw1Statement_of_inputs h12p h13 h13₀
    (Restart.canonicalDriverCodeStatement_of_param h12p₀ h13₀) hBWVersion
    (BW1Life.bw1RelSafeStatement_of_SL h13₀ hBWSL) hBWEnd
  have hA := GW2aStep.gw2aContainmentRegStatement_of_bw1 hD h12 h13 h12₀ h13₀ hBW1 hFix hForce hBR4a
  have hGB6 := gb6RestartStatement_of_hullDet_now h12₀ h13₀ hD
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
  exact theorem14Statement_late h12 h13 h12₀ h13₀ hBR' hD hTests hA
    (SB.sb4DistinctSeedRegStatement_of_retainedTail hDS')
    (SB.sb4InitialArcRegStatement_of_retainedTail hIA') hTerminal hpair hM hLaw

end InteractingSLE.Wire
