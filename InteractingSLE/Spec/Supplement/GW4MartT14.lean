/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4MartWire
import InteractingSLE.Spec.Wire.T14Asm

/-!
# GW4's protected martingales, part 9: Theorem 1.4 with GW4 reduced to the representation half

Packet PROVE-GW4-MART. `Wire.theorem14Statement_assembled` takes GW4's analytic input in the form
`GW4Fix.GW4ComponentPhaseInputsStatement` (the boundary representation together with the protected phase-word
martingales). The protected-martingale half is now proved (`GW4Fix.Mart.gw4ComponentBeforeInputsAStatement_of_rep`,
for the announced versions, which are the ones the relative stopped match uses), so Theorem 1.4 follows from the
same remaining inputs with GW4's input replaced by the representation half `GW4Fix.Mart.GW4ComponentRepAStatement`
(the proof of `theorem14Statement_assembled_of_locality_phaseInputs` and
`GW4Fix.theorem14Statement_late_componentLines`, with `GW4Fix.Mart.gw4RelativeLawRegStatement_of_repA` for GW4).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

namespace InteractingSLE.Wire

open Theorem14

/-- **Theorem 1.4 (all four clauses) from Theorems 1.2–1.3 and the remaining inputs, with GW4 reduced to the
boundary representation with a lattice phase**, for announced versions (`GW4Fix.Mart.GW4ComponentRepAStatement`;
it follows from `GW4Fix.Mart.GW4ComponentRepStatement` and from `GW4Fix.Mart.GW4ComponentRepDStatement`). -/
theorem theorem14Statement_assembled_of_repA
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hTests : GW2TipSystem.GW2RootTestStatement.{u})
    (hSB3 : SB.SB3InductionGenStatement.{u})
    (hDS : SB.Leaf.SB4DistinctSeedLaunchTailStatement.{u})
    (hIA : SB.Leaf.SB4InitialArcLaunchTailStatement.{u})
    (hBWMean : BW1Safe.BW1LineMeanStatement.{u})
    (hN : WalkBdry.WalkNormChartStatement.{u})
    (hPG : WalkBdry.WalkPairGeomStatement.{u})
    (hRep : GW4Fix.Mart.GW4ComponentRepAStatement.{u}) : Theorem14Statement.{u} := by
  have hBR := BR4aIn.br4aHullDetStatement_of_thm12_thm13 h12 h13 h12₀ h13₀
  have hBR4a := BR4aIn.br4aStatement_of_thm12_thm13 h12 h13 h12₀ h13₀
  have hD := Supp8.GB6LMean.gb6HullDetStatement_of_thm12_thm13 h12 h13
  have h12p := Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13
  have h12p₀ := Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12₀ h13₀
  have hBW1 := BW1Safe.bw1Statement_of_mean h12p h12 h13 h13₀
    (Restart.canonicalDriverCodeStatement_of_param h12p₀ h13₀) hBWMean
  have hFix := GW2aForce.flowFixedTimeInteriorStatement_of_thm13 h13
  have hForce := GW2aConn.gw2aConnectorForcingStatement_of_theorem13 h13 h13₀
  have hA := GW2aStep.gw2aContainmentRegStatement_of_bw1
    hD h12 h13 h12₀ h13₀ hBW1 hFix hForce hBR4a
  have hGB6 := gb6RestartStatement_of_hullDet_now h12₀ h13₀ hD
  have hTerminal := BW1Det.terminalPathStatement_of_bw1_graph hBW1 h12p h13 h13₀
  have hRetarget := GW1Det.retargetPathStatement hBR4a h12p h13 h13₀
  have hClock := GW1Laws.walkLaunchClockStatement_of_paths
    hGB6 h12p h13 h13₀ hTerminal hRetarget
  obtain ⟨hGR, hGL⟩ := GW1WalkExit.paramEveryRegStatements_of_walkClock
    hGB6 h13 h13₀ hClock
  have hPR := GW1X.rightWalkProperRegStatement_of_gw1ParamR51
    (GW1X.gw1ParamR51Statement_of_everyReg hGR)
  have hPL := WalkProper.leftWalkProperRegStatement_of_everyReg hGL
  obtain ⟨hAR, hBRc, hAL, hBLc⟩ := WalkMarkSeed.prefixInputs_of_thm12_thm13 h12 h13
  have hSR := WalkSide.walkPrefixSideStatement_of_prefix h12p h13
    (θ := -(Real.pi / 2)) ⟨le_rfl, by linarith only [Real.pi_pos]⟩ hAR hBRc
  have hSL := WalkSide.walkPrefixSideStatement_of_prefix h12p h13
    (θ := Real.pi / 2) ⟨by linarith only [Real.pi_pos], le_rfl⟩ hAL hBLc
  have hpair := WalkBdry.walkPiecePairRegStatement_of_side h12p h13 hPR hPL hSR hSL hPG
  have hM := WalkMean.walkUnionMeanRegAEStatement_of_bdry h12p h13
    (WalkBdry.walkUnionBdryStatement_of_side h12p h13 hPR hPL hSR hSL hN)
  obtain ⟨hDS', hIA'⟩ := SB.Leaf.sb4RetainedTailStatements_of_launch hSB3 h12 h13 hDS hIA
  have hDSreg := SB.sb4DistinctSeedRegStatement_of_retainedTail hDS'
  have hIAreg := SB.sb4InitialArcRegStatement_of_retainedTail hIA'
  have hG := BRLeaf.gb6PrefixPairStatement_of_hullDet hD h12 h13 h12₀ h13₀
  have hU := GW2TipSystem.gw2TipJointUnboundedStatement_of_candR
    (GW2TipSystem.gw2RootCandRStatement_of_test hTests)
  have hEx := GW2Tip.gw2TipExhaustionAllQStatement_of_canonAllQ h12 h13
    (GW2Tip.gw2TipExhaustionCanonAllQStatement_of_jointUnbounded hU)
  have hCone : LightCone14Statement.{u} :=
    lightCone14Statement_of_inputs_late h13 h13₀ hBR4a hGB6 hG h12p hEx hA
  have hF := sbFrontierRegStatement_of_current hCone
    (SB.sbRegStatement_of_sb4_sb5 (SB.sb4RegStatement_of_distinctSeed hDSreg)
      (SB.sb5RegStatement_of_inputs
        (BR3Ref.gw0ForwardStatement_of_theorem13 h13₀) hIAreg hDSreg))
  have hS := GW1X.walkConnectorSideRegStatement_of_theorem13 h13₀
  have hNP := WalkPiece.walkPieceContinuumRegStatement_of_pair hPR hPL hpair
  have hGeom := LateReg.gw3GeometryRegStatement_of_walks_lateReg hPR hPL hA hF
    (GW3SidedProof.rightWalkNegRealRegStatement_of_pieces hPR hS hNP)
  have hO := GW3Sided.betweenComponentsOpenRegStatement_of_geometry hGeom
  have hWB := GW4R51.gw3WordBoundRegStatement_of_inputs hO
    (BR3Ref.gw0ForwardStatement_of_theorem13 h13₀) hS
  have hNC := WalkCont.walkNoCommonContinuumRegStatement_of_pieces hPR hS hNP
  have hCO := LateReg.walkContactOrderRegStatement_of_inputs_lateReg hGB6 h13 h13₀ hClock hA
  have hVO := LateReg.counterflowWallOrderRegStatement_of_inputs_lateReg hGB6 h13 h13₀ hClock hA
  have hPS := LateReg.walkPocketShapeRegStatement_of_det_lateReg PocketMirror.pocketShapeDetStatement hCO hNC hF hA
    hGeom
  have hB := GW4BarrierSelf.gw4BarrierSelfRegStatement_of_walks h13 hPR hPL hNC hF hCO hPS hVO
  exact theorem14Statement_late h12 h13 h12₀ h13₀ hBR hD hTests hA hDSreg hIAreg hTerminal hpair hM
    (GW4Fix.Mart.gw4RelativeLawRegStatement_of_repA h12 h13 h12₀ h13₀
      (GW4Reg.gw4BarrierPocketRegStatement_of_self hB) hWB hRep)

end InteractingSLE.Wire
