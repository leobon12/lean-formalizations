/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLyTop
import InteractingSLE.Spec.Supplement.WalkIntRunChronPair
import InteractingSLE.Spec.Wire.T14Asm4Walk

/-!
# Theorem 1.4 re-assembled with the walk complete

Packet PROVE-T14-ASSEMBLE4. The start is `SB.Ly.theorem14Statement_assembled3` (PROVE-T14-SBLEAVES4: R95's amended
SB binders). Two of its binders are now discharged:

* **`hArc`** (`WalkWords.WalkPairArcDataStatement`) is `WalkIntRunChron.walkPairArcDataStatement h13 h13₀`
  (the actual-run chronology; no further input);
* **`hNL`** (`WalkNorm.WalkNormChartLocStatement`) is PROVE-WALK-TOUCH's walk chart. Its landed form
  `WalkTch.walkNormChartLocStatement_of_inputs` takes GW2a's containment unregularized, while this wiring proves only
  the R51 form; `WalkTch.Asm4.walkNormChartLocStatement_of_inputs_reg` (`Wire/T14Asm4Walk.lean`) is the same proof
  with the containment applied to regular families. Its five GW3 inputs are derived here exactly as
  `Wire.walkFacts_of_sb4Reg_arcData` derives them (`gw3WalkInputs_of_sb4Reg`).

* `gw3WalkInputs_of_sb4Reg`: the five GW3 inputs `hPR hPL hA hF hNR` from Theorems 1.2–1.3, GW2's root tests and
  the regularized SB4 clauses;
* `walkNormChartLocStatement_of_sb4Reg`: the walk chart `hNL` from the same;
* `theorem14Statement_of_sb4Reg4`: Theorem 1.4 from Theorems 1.2–1.3, GW2's root tests, the regularized SB4 clauses
  and GW4's representation half (the core: what the SB leaves are needed for);
* **`theorem14Statement_assembled4`**: Theorem 1.4 from Theorems 1.2–1.3 (both universes), `hTests` (GW2), the
  amended SB3 and the two amended SB4 launch-tail leaves, and `hRep` (GW4);
* `theorem14Statement_assembled4_of_sb3Inputs`: the same with the amended SB3 reduced to SB2(1) (ambient form), the
  small-gap fibre cover (SB1/S6 via `W5Assembly.*_of_dyCover`) and the three stage inputs;
* `theorem14Statement_assembled4_of_initialArcPos`: the initial-arc variant (PROVE-T14-SBFIN's positive-duration leaf).

R48: Theorems 1.2–1.3 are hypotheses of these Theorem 1.4 results only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

namespace InteractingSLE.Wire

open Theorem14

/-- **The five GW3 inputs of the walk chart** (`hPR hPL hA hF hNR`, GW2a's containment in the R51 form), from
Theorems 1.2–1.3, GW2's root tests and the regularized SB4 clauses; the derivation of
`walkFacts_of_sb4Reg_arcData` with the common-arc data proved (`WalkIntRunChron.walkPairArcDataStatement`). -/
theorem gw3WalkInputs_of_sb4Reg
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hTests : GW2TipSystem.GW2RootTestStatement.{u})
    (hDSreg : SB.SB4DistinctSeedRegStatement.{u}) (hIAreg : SB.SB4InitialArcRegStatement.{u}) :
    WalkCont.RightWalkProperRegStatement.{u} ∧ GW3SidedProof.LeftWalkProperRegStatement.{u} ∧
      GW2aCont.GW2aContainmentRegStatement.{u} ∧ SB.SBFrontierRegStatement.{u} ∧
      GW3SidedProof.RightWalkNegRealRegStatement.{u} := by
  have hArc := WalkIntRunChron.walkPairArcDataStatement h13 h13₀
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
  exact ⟨hPR, hPL, hA, hF, GW3SidedProof.rightWalkNegRealRegStatement_of_pieces hPR hS hNP⟩

/-- **Theorem 1.4's walk chart `hNL`** from Theorems 1.2–1.3, GW2's root tests and the regularized SB4 clauses
(PROVE-WALK-TOUCH's chart, GW2a's containment in the R51 form). -/
theorem walkNormChartLocStatement_of_sb4Reg
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hTests : GW2TipSystem.GW2RootTestStatement.{u})
    (hDSreg : SB.SB4DistinctSeedRegStatement.{u}) (hIAreg : SB.SB4InitialArcRegStatement.{u}) :
    WalkNorm.WalkNormChartLocStatement.{u} := by
  obtain ⟨hPR, hPL, hA, hF, hNR⟩ := gw3WalkInputs_of_sb4Reg h12 h13 h12₀ h13₀ hTests hDSreg hIAreg
  exact WalkTch.Asm4.walkNormChartLocStatement_of_inputs_reg h13 h13₀ hPR hPL hA hF hNR

/-- **Theorem 1.4 (all four clauses), core after the walk**: Theorems 1.2–1.3, GW2's root tests, the regularized SB4
clauses and GW4's representation half (`theorem14Statement_of_sb4Reg_arcData` with the chart leaf and the
common-arc data discharged). -/
theorem theorem14Statement_of_sb4Reg4
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hTests : GW2TipSystem.GW2RootTestStatement.{u})
    (hDSreg : SB.SB4DistinctSeedRegStatement.{u}) (hIAreg : SB.SB4InitialArcRegStatement.{u})
    (hRep : GW4Fix.Mart.GW4ComponentRepAStatement.{u}) : Theorem14Statement.{u} := by
  have hArc := WalkIntRunChron.walkPairArcDataStatement h13 h13₀
  exact theorem14Statement_of_sb4Reg_arcData h12 h13 h12₀ h13₀ hTests hDSreg hIAreg
    (walkNormChartStatement_of_sb4Reg_arcData_loc h12 h13 h12₀ h13₀ hTests hDSreg hIAreg hArc
      (walkNormChartLocStatement_of_sb4Reg h12 h13 h12₀ h13₀ hTests hDSreg hIAreg)) hArc hRep

/-- **Theorem 1.4 (all four clauses), main top with the walk complete**: Theorems 1.2–1.3 (universes `u` and `0`),
GW2's root tests `hTests`, R95's amended SB3 and the two amended SB4 launch-tail leaves, and GW4's representation half
`hRep` (`SB.Ly.theorem14Statement_assembled3` with `hNL` and `hArc` discharged). -/
theorem theorem14Statement_assembled4
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hTests : GW2TipSystem.GW2RootTestStatement.{u})
    (hSB3 : SB.Ly.SB3InductionGenRStatement.{u})
    (hDS : SB.Ly.SB4DistinctSeedLaunchTailRStatement.{u})
    (hIA : SB.Ly.SB4InitialArcLaunchTailRStatement.{u})
    (hRep : GW4Fix.Mart.GW4ComponentRepAStatement.{u}) : Theorem14Statement.{u} := by
  obtain ⟨hDSreg, hIAreg⟩ := SB.Ly.sb4Reg_of_launchR h12 h13 hSB3 hDS hIA
  exact SB.Ly.theorem14Statement_assembled3 h12 h13 h12₀ h13₀ hTests hSB3 hDS hIA
    (walkNormChartLocStatement_of_sb4Reg h12 h13 h12₀ h13₀ hTests hDSreg hIAreg)
    (WalkIntRunChron.walkPairArcDataStatement h13 h13₀) hRep

/-- **Theorem 1.4 with the walk complete, SB3 reduced**: the amended SB3 from SB2(1) at launch samples (ambient form,
R94/R96), the small-gap fibre cover (SB1 and S6 by `W5Assembly.*_of_dyCover`, PROVE-SB-W5) and the three remaining
stage inputs (`SB.Ly.sb3InductionGenRStatement_of_inputs_dyCover`). -/
theorem theorem14Statement_assembled4_of_sb3Inputs
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hTests : GW2TipSystem.GW2RootTestStatement.{u})
    (hSB2 : SB.Ly.SB2UpperLaunchEntryLAmbStatement.{u})
    (hDy : Sec5.Aux61Act.DyActFibreCoverOn.{u}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hDy₀ : Sec5.Aux61Act.DyActFibreCoverOn.{0}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hIn : SB.Ly.SB3StageInputsRStatement.{u})
    (hDS : SB.Ly.SB4DistinctSeedLaunchTailRStatement.{u})
    (hIA : SB.Ly.SB4InitialArcLaunchTailRStatement.{u})
    (hRep : GW4Fix.Mart.GW4ComponentRepAStatement.{u}) : Theorem14Statement.{u} :=
  theorem14Statement_assembled4 h12 h13 h12₀ h13₀ hTests
    (SB.Ly.sb3InductionGenRStatement_of_inputs_dyCover hSB2 h12 h13 h12₀ h13₀ hDy hDy₀ hIn) hDS hIA hRep

/-- **Theorem 1.4 with the walk complete, initial-arc variant**: SB4's initial-arc launch leaf replaced by
PROVE-T14-SBFIN's positive-duration form (no SB3 for that clause; SB3 still serves the distinct-seed clause). -/
theorem theorem14Statement_assembled4_of_initialArcPos
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hTests : GW2TipSystem.GW2RootTestStatement.{u})
    (hSB3 : SB.Ly.SB3InductionGenRStatement.{u})
    (hDS : SB.Ly.SB4DistinctSeedLaunchTailRStatement.{u})
    (hIApos : SB.Fin.SB4InitialArcPositiveTailStatement.{u})
    (hRep : GW4Fix.Mart.GW4ComponentRepAStatement.{u}) : Theorem14Statement.{u} := by
  have hDSreg := SB.sb4DistinctSeedRegStatement_of_retainedTail
    (SB.Ly.sb4DistinctSeedRetainedTailStatement_of_relTailR hSB3 h12 h13
      (SB.Ly.sb4DistinctSeedRelTailRStatement_of_launchR h13 hDS))
  have hIAreg := SB.Fin.sb4InitialArcRegStatement_of_positiveTail hIApos
  exact theorem14Statement_of_sb4Reg4 h12 h13 h12₀ h13₀ hTests hDSreg hIAreg hRep

end InteractingSLE.Wire
