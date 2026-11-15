/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLyLeaf
import InteractingSLE.Spec.Supplement.SBLyPath
import InteractingSLE.Spec.Wire.T1415Asm2Thm14

/-!
# Theorem 1.4's top with R95's amended SB3

Packet PROVE-T14-SBLEAVES4. `Wire.theorem14Statement_assembled2` takes `hSB3 : SB.SB3InductionGenStatement`, which
ruling R95 replaces by the amended `Ly.SB3InductionGenRStatement`; its consumers (SB4's two launch-tail leaves) then
carry the premise on their relative data (`Ly.SB4DistinctSeedLaunchTailRStatement`,
`Ly.SB4InitialArcLaunchTailRStatement`). The rest of the wiring is unchanged.

* `sb4Reg_of_launchR`: the regularized SB4 clauses from the amended SB3 and the two amended leaves;
* **`theorem14Statement_assembled3`**: `Wire.theorem14Statement_assembled2` with `hSB3`, `hDS`, `hIA` amended;
* `theorem14Statement_assembled3_of_sb3Inputs`: the same with the amended SB3 reduced to SB2(1) at launch samples in
  GW1's setting (R96), the
  small-gap fibre cover (for SB1/S6) and the three remaining stage inputs (`Ly.SB3StageInputsRStatement`);
* `theorem14Statement_assembled3_of_initialArcPos`: the initial-arc variant (PROVE-T14-SBFIN's positive-duration leaf);
* `gw1PieceSimpleStatement_of_thm12_thm13` (GW1's piece simplicity as the top derives it) and
  `sb3InductionRegStatement_of_thms`: the counterflow form of SB3 (R96) from SB2(1) in that setting, Theorems 1.2–1.3,
  the fibre cover, the run fact `WalkLaunchPrefixNontrivialStatement` and the two measurability inputs.

R48: Theorems 1.2–1.3 are hypotheses of these Theorem 1.4 results only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

namespace InteractingSLE.Theorem14.SB.Ly

/-- The regularized SB4 clauses from the amended SB3 and the two amended launch-tail leaves. -/
theorem sb4Reg_of_launchR (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (hSB3 : SB3InductionGenRStatement.{u})
    (hDS : SB4DistinctSeedLaunchTailRStatement.{u})
    (hIA : SB4InitialArcLaunchTailRStatement.{u}) :
    SB.SB4DistinctSeedRegStatement.{u} ∧ SB.SB4InitialArcRegStatement.{u} := by
  obtain ⟨hDS', hIA'⟩ := sb4RetainedTailStatements_of_launchR hSB3 h12 h13 hDS hIA
  exact ⟨SB.sb4DistinctSeedRegStatement_of_retainedTail hDS', SB.sb4InitialArcRegStatement_of_retainedTail hIA'⟩

/-- **Theorem 1.4 (all four clauses), main top after R95**: `Wire.theorem14Statement_assembled2` with SB3's leaf
`hSB3` amended (`SB3InductionGenRStatement`) and SB4's two launch-tail leaves carrying the premise on their relative
data. -/
theorem theorem14Statement_assembled3
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hTests : GW2TipSystem.GW2RootTestStatement.{u})
    (hSB3 : SB3InductionGenRStatement.{u})
    (hDS : SB4DistinctSeedLaunchTailRStatement.{u})
    (hIA : SB4InitialArcLaunchTailRStatement.{u})
    (hNL : WalkNorm.WalkNormChartLocStatement.{u})
    (hArc : WalkWords.WalkPairArcDataStatement.{u})
    (hRep : GW4Fix.Mart.GW4ComponentRepAStatement.{u}) : Wire.Theorem14Statement.{u} := by
  obtain ⟨hDSreg, hIAreg⟩ := sb4Reg_of_launchR h12 h13 hSB3 hDS hIA
  exact Wire.theorem14Statement_of_sb4Reg_arcData h12 h13 h12₀ h13₀ hTests hDSreg hIAreg
    (Wire.walkNormChartStatement_of_sb4Reg_arcData_loc h12 h13 h12₀ h13₀ hTests hDSreg hIAreg hArc hNL) hArc hRep

/-- **Theorem 1.4 after R95/R96, SB3 reduced**: the amended SB3 from SB2(1) at launch samples (R94) in GW1's setting
(R96), the small-gap fibre cover (SB1 and S6, PROVE-SB-W5) and the three remaining stage inputs. -/
theorem theorem14Statement_assembled3_of_sb3Inputs
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hTests : GW2TipSystem.GW2RootTestStatement.{u})
    (hSB2 : SB2UpperLaunchEntryLAmbStatement.{u})
    (hDy : Sec5.Aux61Act.DyActFibreCoverOn.{u}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hDy₀ : Sec5.Aux61Act.DyActFibreCoverOn.{0}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hIn : SB3StageInputsRStatement.{u})
    (hDS : SB4DistinctSeedLaunchTailRStatement.{u})
    (hIA : SB4InitialArcLaunchTailRStatement.{u})
    (hNL : WalkNorm.WalkNormChartLocStatement.{u})
    (hArc : WalkWords.WalkPairArcDataStatement.{u})
    (hRep : GW4Fix.Mart.GW4ComponentRepAStatement.{u}) : Wire.Theorem14Statement.{u} :=
  theorem14Statement_assembled3 h12 h13 h12₀ h13₀ hTests
    (sb3InductionGenRStatement_of_inputs_dyCover hSB2 h12 h13 h12₀ h13₀ hDy hDy₀ hIn) hDS hIA hNL hArc hRep

/-- **Theorem 1.4 after R95, initial-arc variant**: the initial-arc leaf replaced by PROVE-T14-SBFIN's
positive-duration form (no SB3 for that clause). -/
theorem theorem14Statement_assembled3_of_initialArcPos
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hTests : GW2TipSystem.GW2RootTestStatement.{u})
    (hSB3 : SB3InductionGenRStatement.{u})
    (hDS : SB4DistinctSeedLaunchTailRStatement.{u})
    (hIApos : SB.Fin.SB4InitialArcPositiveTailStatement.{u})
    (hNL : WalkNorm.WalkNormChartLocStatement.{u})
    (hArc : WalkWords.WalkPairArcDataStatement.{u})
    (hRep : GW4Fix.Mart.GW4ComponentRepAStatement.{u}) : Wire.Theorem14Statement.{u} := by
  have hDSreg := SB.sb4DistinctSeedRegStatement_of_retainedTail
    (sb4DistinctSeedRetainedTailStatement_of_relTailR hSB3 h12 h13
      (sb4DistinctSeedRelTailRStatement_of_launchR h13 hDS))
  have hIAreg := SB.Fin.sb4InitialArcRegStatement_of_positiveTail hIApos
  exact Wire.theorem14Statement_of_sb4Reg_arcData h12 h13 h12₀ h13₀ hTests hDSreg hIAreg
    (Wire.walkNormChartStatement_of_sb4Reg_arcData_loc h12 h13 h12₀ h13₀ hTests hDSreg hIAreg hArc hNL) hArc hRep

/-- **GW1's piece simplicity from Theorems 1.2–1.3** (the derivation used inside `Wire.walkFacts_of_sb4Reg_arcData`:
GB6's restart, BW1's terminal path, the retarget path and the walk launch clock). -/
theorem gw1PieceSimpleStatement_of_thm12_thm13
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0}) :
    GW1Z.GW1PieceSimpleStatement.{u} := by
  have hD := Supp8.GB6LMean.gb6HullDetStatement_of_thm12_thm13 h12 h13
  have h12p := Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13
  have h12p₀ := Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12₀ h13₀
  have hBW1 := BW1LMean.bw1Statement_of_thm12_thm13 h12p h12 h13 h13₀
    (Restart.canonicalDriverCodeStatement_of_param h12p₀ h13₀)
  have hBR4a := BR4aIn.br4aStatement_of_thm12_thm13 h12 h13 h12₀ h13₀
  have hGB6 := Wire.gb6RestartStatement_of_hullDet_now h12₀ h13₀ hD
  have hClock := GW1Laws.walkLaunchClockStatement_of_paths hGB6 h12p h13 h13₀
    (BW1Det.terminalPathStatement_of_bw1_graph hBW1 h12p h13 h13₀)
    (GW1Det.retargetPathStatement hBR4a h12p h13 h13₀)
  exact GW1Z.gw1PieceSimpleStatement_of_walkClock hGB6 h13 h13₀ hClock

/-- **SB3's induction in Theorem 1.4's counterflow setting** (`SB.SB3InductionRegStatement`, ruling R96) from SB2(1)
in that setting, Theorems 1.2–1.3, the small-gap fibre cover (SB1/S6), the run fact
`WalkLaunchPrefixNontrivialStatement` and the measurability inputs (I2), (I2′). -/
theorem sb3InductionRegStatement_of_thms (hSB2 : SB2UpperLaunchEntryLCfStatement.{u})
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hDy : Sec5.Aux61Act.DyActFibreCoverOn.{u}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hDy₀ : Sec5.Aux61Act.DyActFibreCoverOn.{0}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hNT : WalkLaunchPrefixNontrivialStatement.{u}) (hM : SB3StageMeasCfStatement.{u}) :
    SB3InductionRegStatement.{u} :=
  sb3InductionRegStatement_of_meas hSB2 (W5Assembly.sb1Statement_of_dyCover h12 h13 h12₀ h13₀ hDy hDy₀)
    (W5Assembly.s6Statement_of_dyCover h12 h13 h12₀ h13₀ hDy hDy₀) h13 h13₀
    (gw1PieceSimpleStatement_of_thm12_thm13 h12 h13 h12₀ h13₀) hNT hM

end InteractingSLE.Theorem14.SB.Ly
