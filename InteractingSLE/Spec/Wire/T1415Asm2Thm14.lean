/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4MartT14
import InteractingSLE.Spec.Supplement.BW1LMeanFinal
import InteractingSLE.Spec.Supplement.WalkWordsAccess
import InteractingSLE.Spec.Supplement.WalkNormChart
import InteractingSLE.Spec.Supplement.GW1PieceSimpleFiber
import InteractingSLE.Spec.Supplement.SBFinPositive

/-!
# Theorem 1.4 re-assembled on the inputs landed since PROVE-T14-ASSEMBLE

Packet PROVE-T1415-ASSEMBLE2. The start is `Wire.theorem14Statement_assembled_of_repA` (PROVE-GW4-MART: GW4's input
reduced to the representation half `GW4Fix.Mart.GW4ComponentRepAStatement`). Compared with it:

* **`hBWMean` is discharged**: BW1's union-mean identification is
  `BW1LMean.bw1LineMeanStatement_of_thm12_thm13`, so BW1 is `BW1LMean.bw1Statement_of_thm12_thm13`.
* **`hPG` is reduced to `WalkWords.WalkPairArcDataStatement`** (PROVE-WALK-WORDS: the left prime-end access is
  proved; what remains is arc bookkeeping) by `WalkWords.walkPairGeomStatement_of_arcData`. Its other four inputs are
  derived here: contact order (`LateReg.walkContactOrderRegStatement_of_inputs_lateReg`), the two proper walks, and
  GW1's piece simplicity (`GW1Z.gw1PieceSimpleStatement_of_walkClock`).
* **`hN` is reduced to `WalkNorm.WalkNormChartLocStatement`** (normalized charts up to the logarithm, with the
  between-region path facts as a hypothesis) by `WalkNorm.walkNormChartStatement_of_loc`. This is the form every
  geometric input of the WALKINT line gives (`WalkIntBridge.walkNormChartLocStatement_of_referenceGeometry`,
  `WalkIntGerm.walkNormChartLocStatement_of_incidentGeometry`,
  `WalkIntFiber.walkNormChartLocStatement_of_physicalGeometry`). Its piece matches carry more local data than
  `IsPieceMatch`, so it is not claimed weaker than the old leaf; `theorem14Statement_assembled2_of_normChart` keeps
  the old form.

The SB leaves stay as in PROVE-T14-ASSEMBLE. PROVE-SB-W5's `SB.W5Assembly.sb1Statement_of_dyCover`,
`s6Statement_of_dyCover` and `w5Statement_of_dyCover` prove SB1, S6 and W5, but no landed reduction of
`SB.SB3InductionGenStatement` or of the two SB4 launch-tail leaves consumes them. SB1 and S6 enter only SB3's base
comparison (`SB.Erase.ae_isOneSided_base_of_hybrid`); SB3's ordinary-stage step needs SB2, whose landed statements
have no consumer. A variant replaces the initial-arc launch leaf by PROVE-T14-SBFIN's positive-duration form, which
needs no SB3.

* `walkFacts_of_sb4Reg_arcData`, `walkNormChartStatement_of_sb4Reg_arcData_loc`: the walk facts and the chart leaf;
* `theorem14Statement_of_sb4Reg_arcData`: the core, from the regularized SB4 clauses and the chart leaf;
* `sb4Reg_of_launch`: the regularized SB4 clauses from the three SB leaves;
* **`theorem14Statement_assembled2`** (the main top, chart leaf in the logarithm form);
* `theorem14Statement_assembled2_of_normChart` (chart leaf in PROVE-T14-ASSEMBLE's form);
* `theorem14Statement_assembled2_of_initialArcPos` (the initial-arc variant).

R48: Theorems 1.2–1.3 are hypotheses of these Theorem 1.4 results only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

namespace InteractingSLE.Wire

open Theorem14

/-- **The walk facts of the late wiring**, from Theorems 1.2–1.3, GW2's root tests, the regularized SB4 clauses and
the common-arc data: both proper walks, contact order, GW1's piece simplicity, no common continuum and GW3's
geometry (the inputs of `WalkNorm.walkNormChartStatement_of_loc` other than the chart leaf). -/
theorem walkFacts_of_sb4Reg_arcData
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hTests : GW2TipSystem.GW2RootTestStatement.{u})
    (hDSreg : SB.SB4DistinctSeedRegStatement.{u}) (hIAreg : SB.SB4InitialArcRegStatement.{u})
    (hArc : WalkWords.WalkPairArcDataStatement.{u}) :
    WalkCont.RightWalkProperRegStatement.{u} ∧ GW3SidedProof.LeftWalkProperRegStatement.{u} ∧
      GW4BarrierSelf.WalkContactOrderRegStatement.{u} ∧ GW1Z.GW1PieceSimpleStatement.{u} ∧
      WalkCont.WalkNoCommonContinuumRegStatement.{u} ∧ GW3Sided.GW3GeometryRegStatement.{u} := by
  have hBR4a := BR4aIn.br4aStatement_of_thm12_thm13 h12 h13 h12₀ h13₀
  have hD := Supp8.GB6LMean.gb6HullDetStatement_of_thm12_thm13 h12 h13
  have h12p := Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13
  have h12p₀ := Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12₀ h13₀
  have hBW1 := BW1LMean.bw1Statement_of_thm12_thm13 h12p h12 h13 h13₀
    (Restart.canonicalDriverCodeStatement_of_param h12p₀ h13₀)
  have hA := GW2aStep.gw2aContainmentRegStatement_of_bw1 hD h12 h13 h12₀ h13₀ hBW1
    (GW2aForce.flowFixedTimeInteriorStatement_of_thm13 h13)
    (GW2aConn.gw2aConnectorForcingStatement_of_theorem13 h13 h13₀) hBR4a
  have hGB6 := gb6RestartStatement_of_hullDet_now h12₀ h13₀ hD
  have hClock := GW1Laws.walkLaunchClockStatement_of_paths hGB6 h12p h13 h13₀
    (BW1Det.terminalPathStatement_of_bw1_graph hBW1 h12p h13 h13₀)
    (GW1Det.retargetPathStatement hBR4a h12p h13 h13₀)
  obtain ⟨hGR, hGL⟩ := GW1WalkExit.paramEveryRegStatements_of_walkClock hGB6 h13 h13₀ hClock
  have hPR := GW1X.rightWalkProperRegStatement_of_gw1ParamR51
    (GW1X.gw1ParamR51Statement_of_everyReg hGR)
  have hPL := WalkProper.leftWalkProperRegStatement_of_everyReg hGL
  have hCO := LateReg.walkContactOrderRegStatement_of_inputs_lateReg hGB6 h13 h13₀ hClock hA
  have hSimple := GW1Z.gw1PieceSimpleStatement_of_walkClock hGB6 h13 h13₀ hClock
  have hPG := WalkWords.walkPairGeomStatement_of_arcData hCO hPR hPL hSimple hArc
  obtain ⟨hAR, hBRc, hAL, hBLc⟩ := WalkMarkSeed.prefixInputs_of_thm12_thm13 h12 h13
  have hpair := WalkBdry.walkPiecePairRegStatement_of_side h12p h13 hPR hPL
    (WalkSide.walkPrefixSideStatement_of_prefix h12p h13
      (θ := -(Real.pi / 2)) ⟨le_rfl, by linarith only [Real.pi_pos]⟩ hAR hBRc)
    (WalkSide.walkPrefixSideStatement_of_prefix h12p h13
      (θ := Real.pi / 2) ⟨by linarith only [Real.pi_pos], le_rfl⟩ hAL hBLc) hPG
  have hU := GW2TipSystem.gw2TipJointUnboundedStatement_of_candR
    (GW2TipSystem.gw2RootCandRStatement_of_test hTests)
  have hEx := GW2Tip.gw2TipExhaustionAllQStatement_of_canonAllQ h12 h13
    (GW2Tip.gw2TipExhaustionCanonAllQStatement_of_jointUnbounded hU)
  have hCone : LightCone14Statement.{u} := lightCone14Statement_of_inputs_late h13 h13₀ hBR4a hGB6
    (BRLeaf.gb6PrefixPairStatement_of_hullDet hD h12 h13 h12₀ h13₀) h12p hEx hA
  have hF := sbFrontierRegStatement_of_current hCone
    (SB.sbRegStatement_of_sb4_sb5 (SB.sb4RegStatement_of_distinctSeed hDSreg)
      (SB.sb5RegStatement_of_inputs
        (BR3Ref.gw0ForwardStatement_of_theorem13 h13₀) hIAreg hDSreg))
  have hS := GW1X.walkConnectorSideRegStatement_of_theorem13 h13₀
  have hNP := WalkPiece.walkPieceContinuumRegStatement_of_pair hPR hPL hpair
  exact ⟨hPR, hPL, hCO, hSimple, WalkCont.walkNoCommonContinuumRegStatement_of_pieces hPR hS hNP,
    LateReg.gw3GeometryRegStatement_of_walks_lateReg hPR hPL hA hF
      (GW3SidedProof.rightWalkNegRealRegStatement_of_pieces hPR hS hNP)⟩

/-- **The normalized component charts from their form up to the logarithm** (PROVE-T14-WALKNORM's
`WalkNorm.walkNormChartStatement_of_loc`, its walk facts supplied by `walkFacts_of_sb4Reg_arcData`). -/
theorem walkNormChartStatement_of_sb4Reg_arcData_loc
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hTests : GW2TipSystem.GW2RootTestStatement.{u})
    (hDSreg : SB.SB4DistinctSeedRegStatement.{u}) (hIAreg : SB.SB4InitialArcRegStatement.{u})
    (hArc : WalkWords.WalkPairArcDataStatement.{u}) (hNL : WalkNorm.WalkNormChartLocStatement.{u}) :
    WalkBdry.WalkNormChartStatement.{u} := by
  obtain ⟨hPR, hPL, hCO, hSimple, hNC, hGeom⟩ :=
    walkFacts_of_sb4Reg_arcData h12 h13 h12₀ h13₀ hTests hDSreg hIAreg hArc
  exact WalkNorm.walkNormChartStatement_of_loc hPR hPL hCO hSimple hNC hGeom hNL

/-- **Theorem 1.4 (all four clauses), core**: Theorems 1.2–1.3, GW2's root tests, the regularized SB4 clauses, the
normalized component charts, the common-arc data of the two walks and GW4's representation half. BW1's mean is
discharged (`BW1LMean.bw1Statement_of_thm12_thm13`); the common-arc geometry `hPG` comes from the arc data
(`WalkWords.walkPairGeomStatement_of_arcData`). -/
theorem theorem14Statement_of_sb4Reg_arcData
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hTests : GW2TipSystem.GW2RootTestStatement.{u})
    (hDSreg : SB.SB4DistinctSeedRegStatement.{u}) (hIAreg : SB.SB4InitialArcRegStatement.{u})
    (hN : WalkBdry.WalkNormChartStatement.{u}) (hArc : WalkWords.WalkPairArcDataStatement.{u})
    (hRep : GW4Fix.Mart.GW4ComponentRepAStatement.{u}) : Theorem14Statement.{u} := by
  have hBR := BR4aIn.br4aHullDetStatement_of_thm12_thm13 h12 h13 h12₀ h13₀
  have hBR4a := BR4aIn.br4aStatement_of_thm12_thm13 h12 h13 h12₀ h13₀
  have hD := Supp8.GB6LMean.gb6HullDetStatement_of_thm12_thm13 h12 h13
  have h12p := Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13
  have h12p₀ := Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12₀ h13₀
  have hBW1 := BW1LMean.bw1Statement_of_thm12_thm13 h12p h12 h13 h13₀
    (Restart.canonicalDriverCodeStatement_of_param h12p₀ h13₀)
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
  -- the common-arc geometry of the two walks from the arc data (PROVE-WALK-WORDS)
  have hCO := LateReg.walkContactOrderRegStatement_of_inputs_lateReg hGB6 h13 h13₀ hClock hA
  have hPG := WalkWords.walkPairGeomStatement_of_arcData hCO hPR hPL
    (GW1Z.gw1PieceSimpleStatement_of_walkClock hGB6 h13 h13₀ hClock) hArc
  obtain ⟨hAR, hBRc, hAL, hBLc⟩ := WalkMarkSeed.prefixInputs_of_thm12_thm13 h12 h13
  have hSR := WalkSide.walkPrefixSideStatement_of_prefix h12p h13
    (θ := -(Real.pi / 2)) ⟨le_rfl, by linarith only [Real.pi_pos]⟩ hAR hBRc
  have hSL := WalkSide.walkPrefixSideStatement_of_prefix h12p h13
    (θ := Real.pi / 2) ⟨by linarith only [Real.pi_pos], le_rfl⟩ hAL hBLc
  have hpair := WalkBdry.walkPiecePairRegStatement_of_side h12p h13 hPR hPL hSR hSL hPG
  have hM := WalkMean.walkUnionMeanRegAEStatement_of_bdry h12p h13
    (WalkBdry.walkUnionBdryStatement_of_side h12p h13 hPR hPL hSR hSL hN)
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
  have hVO := LateReg.counterflowWallOrderRegStatement_of_inputs_lateReg hGB6 h13 h13₀ hClock hA
  have hPS := LateReg.walkPocketShapeRegStatement_of_det_lateReg PocketMirror.pocketShapeDetStatement hCO hNC hF hA
    hGeom
  have hB := GW4BarrierSelf.gw4BarrierSelfRegStatement_of_walks h13 hPR hPL hNC hF hCO hPS hVO
  exact theorem14Statement_late h12 h13 h12₀ h13₀ hBR hD hTests hA hDSreg hIAreg hTerminal hpair hM
    (GW4Fix.Mart.gw4RelativeLawRegStatement_of_repA h12 h13 h12₀ h13₀
      (GW4Reg.gw4BarrierPocketRegStatement_of_self hB) hWB hRep)

/-- The regularized SB4 clauses from SB3 and the two launch-tail leaves (`SB.Leaf.sb4RetainedTailStatements_of_launch`,
as in PROVE-T14-ASSEMBLE). -/
theorem sb4Reg_of_launch (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hSB3 : SB.SB3InductionGenStatement.{u})
    (hDS : SB.Leaf.SB4DistinctSeedLaunchTailStatement.{u})
    (hIA : SB.Leaf.SB4InitialArcLaunchTailStatement.{u}) :
    SB.SB4DistinctSeedRegStatement.{u} ∧ SB.SB4InitialArcRegStatement.{u} := by
  obtain ⟨hDS', hIA'⟩ := SB.Leaf.sb4RetainedTailStatements_of_launch hSB3 h12 h13 hDS hIA
  exact ⟨SB.sb4DistinctSeedRegStatement_of_retainedTail hDS', SB.sb4InitialArcRegStatement_of_retainedTail hIA'⟩

/-- **Theorem 1.4 (all four clauses), main top**: Theorems 1.2–1.3 (universes `u` and `0`), GW2's root tests, the
three SB leaves (SB3's stage induction and SB4's two launch tails), the normalized component charts up to the
logarithm, the common-arc data of the two walks, and GW4's representation half. -/
theorem theorem14Statement_assembled2
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hTests : GW2TipSystem.GW2RootTestStatement.{u})
    (hSB3 : SB.SB3InductionGenStatement.{u})
    (hDS : SB.Leaf.SB4DistinctSeedLaunchTailStatement.{u})
    (hIA : SB.Leaf.SB4InitialArcLaunchTailStatement.{u})
    (hNL : WalkNorm.WalkNormChartLocStatement.{u})
    (hArc : WalkWords.WalkPairArcDataStatement.{u})
    (hRep : GW4Fix.Mart.GW4ComponentRepAStatement.{u}) : Theorem14Statement.{u} := by
  obtain ⟨hDSreg, hIAreg⟩ := sb4Reg_of_launch h12 h13 hSB3 hDS hIA
  exact theorem14Statement_of_sb4Reg_arcData h12 h13 h12₀ h13₀ hTests hDSreg hIAreg
    (walkNormChartStatement_of_sb4Reg_arcData_loc h12 h13 h12₀ h13₀ hTests hDSreg hIAreg hArc hNL) hArc hRep

/-- **Theorem 1.4, normalized-chart variant**: the main top with the chart leaf in PROVE-T14-ASSEMBLE's form
`WalkBdry.WalkNormChartStatement` (this is `Wire.theorem14Statement_assembled_of_repA` with `hBWMean` discharged and
`hPG` reduced to the arc data). -/
theorem theorem14Statement_assembled2_of_normChart
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hTests : GW2TipSystem.GW2RootTestStatement.{u})
    (hSB3 : SB.SB3InductionGenStatement.{u})
    (hDS : SB.Leaf.SB4DistinctSeedLaunchTailStatement.{u})
    (hIA : SB.Leaf.SB4InitialArcLaunchTailStatement.{u})
    (hN : WalkBdry.WalkNormChartStatement.{u})
    (hArc : WalkWords.WalkPairArcDataStatement.{u})
    (hRep : GW4Fix.Mart.GW4ComponentRepAStatement.{u}) : Theorem14Statement.{u} := by
  obtain ⟨hDSreg, hIAreg⟩ := sb4Reg_of_launch h12 h13 hSB3 hDS hIA
  exact theorem14Statement_of_sb4Reg_arcData h12 h13 h12₀ h13₀ hTests hDSreg hIAreg hN hArc hRep

/-- **Theorem 1.4, initial-arc variant**: the main top with SB4's initial-arc launch leaf replaced by
PROVE-T14-SBFIN's positive-duration form `SB.Fin.SB4InitialArcPositiveTailStatement` (sewing only on the
positive-duration branch; no SB3 for this clause). SB3 is still used by the distinct-seed clause. -/
theorem theorem14Statement_assembled2_of_initialArcPos
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hTests : GW2TipSystem.GW2RootTestStatement.{u})
    (hSB3 : SB.SB3InductionGenStatement.{u})
    (hDS : SB.Leaf.SB4DistinctSeedLaunchTailStatement.{u})
    (hIApos : SB.Fin.SB4InitialArcPositiveTailStatement.{u})
    (hNL : WalkNorm.WalkNormChartLocStatement.{u})
    (hArc : WalkWords.WalkPairArcDataStatement.{u})
    (hRep : GW4Fix.Mart.GW4ComponentRepAStatement.{u}) : Theorem14Statement.{u} := by
  have hDSreg := SB.sb4DistinctSeedRegStatement_of_retainedTail
    (SB.Leaf.sb4DistinctSeedRetainedTailStatement_of_relTail hSB3 h12 h13
      (SB.Leaf.sb4DistinctSeedRelTailStatement_of_launch h13 hDS))
  have hIAreg := SB.Fin.sb4InitialArcRegStatement_of_positiveTail hIApos
  exact theorem14Statement_of_sb4Reg_arcData h12 h13 h12₀ h13₀ hTests hDSreg hIAreg
    (walkNormChartStatement_of_sb4Reg_arcData_loc h12 h13 h12₀ h13₀ hTests hDSreg hIAreg hArc hNL) hArc hRep

end InteractingSLE.Wire
