/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB4RMirrorLeaf
import InteractingSLE.Spec.Wire.T14Asm4

/-!
# Theorem 1.4's two SB4 leaves from SB2(2) and its pointwise lift

Packet PROVE-T14-SB4LEAF. The two SB4 binders `hDS`, `hIA` of `Wire.theorem14Statement_assembled4` (rulings R95,
R96, R99) are proved from SB2(2) and its mirror and initial-arc variants, each with its pointwise lift:

* `walkProperRegStatements_of_thm12_thm13`: the properness of both completed walks from Theorems 1.2–1.3 (the GW1
  chain of `Wire.gw3WalkInputs_of_sb4Reg`, which does not use SB4);
* **`sb4DistinctSeedLaunchTailRStatement_of_lift`**: `Ly.SB4DistinctSeedLaunchTailRStatement` from SB2(2) in R99's
  form (`Lz.SB2LowerLaunchEntryAdmStatement`), `Lf.SB2LowerTailLiftStatement`, the mirror inputs
  `Lf.SB2LeftLaunchStatement`, `Lf.SB2LeftTailLiftStatement`, the walks' properness and Theorem 1.3;
* **`sb4InitialArcLaunchTailRStatement_of_lift`**: `Ly.SB4InitialArcLaunchTailRStatement` from
  `Lf.SB2ArcLaunchStatement`, `Lf.SB2ArcTailLiftStatement`, the lower walk's properness and Theorem 1.3;
* **`theorem14Statement_of_sb4Lift`**: Theorem 1.4 from Theorems 1.2–1.3, GW2's root tests, the amended SB3, the six
  SB2(2) inputs and GW4's representation half; `theorem14Statement_of_sb4Lift_sb3Inputs` with SB3 reduced as in
  `Wire.theorem14Statement_assembled4_of_sb3Inputs`. (PROVE-T14-ASSEMBLE5's `theorem14Statement_assembled5*` can
  consume the two leaf theorems directly.)

R48: Theorems 1.2–1.3 are hypotheses of these Theorem 1.4 results only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

namespace InteractingSLE.Wire

open Theorem14

/-- **Both completed walks are proper curves from `0`** (Theorems 1.2–1.3; the GW1 chain of
`gw3WalkInputs_of_sb4Reg`, which uses no SB4 input). -/
theorem walkProperRegStatements_of_thm12_thm13
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0}) :
    WalkCont.RightWalkProperRegStatement.{u} ∧ GW3SidedProof.LeftWalkProperRegStatement.{u} := by
  have hBR4a := BR4aIn.br4aStatement_of_thm12_thm13 h12 h13 h12₀ h13₀
  have hD := Supp8.GB6LMean.gb6HullDetStatement_of_thm12_thm13 h12 h13
  have h12p := Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13
  have h12p₀ := Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12₀ h13₀
  have hBW1 := BW1LMean.bw1Statement_of_thm12_thm13 h12p h12 h13 h13₀
    (Restart.canonicalDriverCodeStatement_of_param h12p₀ h13₀)
  have hGB6 := gb6RestartStatement_of_hullDet_now h12₀ h13₀ hD
  have hClock := GW1Laws.walkLaunchClockStatement_of_paths hGB6 h12p h13 h13₀
    (BW1Det.terminalPathStatement_of_bw1_graph hBW1 h12p h13 h13₀)
    (GW1Det.retargetPathStatement hBR4a h12p h13 h13₀)
  obtain ⟨hGR, hGL⟩ := GW1WalkExit.paramEveryRegStatements_of_walkClock hGB6 h13 h13₀ hClock
  exact ⟨GW1X.rightWalkProperRegStatement_of_gw1ParamR51 (GW1X.gw1ParamR51Statement_of_everyReg hGR),
    WalkProper.leftWalkProperRegStatement_of_everyReg hGL⟩

/-- **SB4's distinct-seed leaf `hDS` with R95's premise**, from SB2(2) (R99), its mirror and their pointwise lifts. -/
theorem sb4DistinctSeedLaunchTailRStatement_of_lift (hSB2 : SB.Lz.SB2LowerLaunchEntryAdmStatement.{u})
    (hLift : SB.Lf.SB2LowerTailLiftStatement.{u}) (hSB2L : SB.Lf.SB2LeftLaunchStatement.{u})
    (hLiftL : SB.Lf.SB2LeftTailLiftStatement.{u}) (hPR : WalkCont.RightWalkProperRegStatement.{u})
    (hPL : GW3SidedProof.LeftWalkProperRegStatement.{u}) (h13 : Exist.Theorem13Statement.{u}) :
    SB.Ly.SB4DistinctSeedLaunchTailRStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg l hl h41
  exact ⟨fun u hu hθ hL _ => SB.Lf.scheduleLaunchTailR_lower hSB2 hLift hPR h13 hκ hκ4 hb hh hcf hζ' hE hreg
      hl hu hθ hL,
    fun v hv hθ hR hH => SB.Lf.scheduleRelativeTailR_left hSB2L hLiftL hPL h13 hκ hκ4 hb hh hcf hζ' hE hreg
      hl h41 hv hθ hR hH⟩

/-- **SB4's initial-arc leaf `hIA` with R95's premise**, from SB2(2) at the arc seed and its pointwise lift. -/
theorem sb4InitialArcLaunchTailRStatement_of_lift (hArc : SB.Lf.SB2ArcLaunchStatement.{u})
    (hArcLift : SB.Lf.SB2ArcTailLiftStatement.{u}) (hPR : WalkCont.RightWalkProperRegStatement.{u})
    (h13 : Exist.Theorem13Statement.{u}) : SB.Ly.SB4InitialArcLaunchTailRStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg v hv hlow0 hlow l hl _ hθ
  exact SB.Lf.scheduleLaunchTailR_arc hArc hArcLift hPR h13 hκ hκ4 hb hh hcf hζ' hE hreg hv hlow0 hlow hl hθ

/-- **Theorem 1.4 (all four clauses)** from Theorems 1.2–1.3 (universes `u` and `0`), GW2's root tests `hTests`,
R95's amended SB3, SB2(2) in R99's form with its mirror and initial-arc variants and their pointwise lifts, and GW4's
representation half `hRep` (`theorem14Statement_assembled4` with the two SB4 leaves discharged). -/
theorem theorem14Statement_of_sb4Lift
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hTests : GW2TipSystem.GW2RootTestStatement.{u})
    (hSB3 : SB.Ly.SB3InductionGenRStatement.{u})
    (hSB2 : SB.Lz.SB2LowerLaunchEntryAdmStatement.{u}) (hLift : SB.Lf.SB2LowerTailLiftStatement.{u})
    (hSB2L : SB.Lf.SB2LeftLaunchStatement.{u}) (hLiftL : SB.Lf.SB2LeftTailLiftStatement.{u})
    (hArc : SB.Lf.SB2ArcLaunchStatement.{u}) (hArcLift : SB.Lf.SB2ArcTailLiftStatement.{u})
    (hRep : GW4Fix.Mart.GW4ComponentRepAStatement.{u}) : Theorem14Statement.{u} := by
  obtain ⟨hPR, hPL⟩ := walkProperRegStatements_of_thm12_thm13 h12 h13 h12₀ h13₀
  exact theorem14Statement_assembled4 h12 h13 h12₀ h13₀ hTests hSB3
    (sb4DistinctSeedLaunchTailRStatement_of_lift hSB2 hLift hSB2L hLiftL hPR hPL h13)
    (sb4InitialArcLaunchTailRStatement_of_lift hArc hArcLift hPR h13) hRep

/-- **Theorem 1.4 with SB3 reduced**: as `theorem14Statement_of_sb4Lift`, with the amended SB3 from SB2(1) at launch
samples (ambient form), the small-gap fibre cover and the three stage inputs
(`SB.Ly.sb3InductionGenRStatement_of_inputs_dyCover`). -/
theorem theorem14Statement_of_sb4Lift_sb3Inputs
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hTests : GW2TipSystem.GW2RootTestStatement.{u})
    (hSB2up : SB.Ly.SB2UpperLaunchEntryLAmbStatement.{u})
    (hDy : Sec5.Aux61Act.DyActFibreCoverOn.{u}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hDy₀ : Sec5.Aux61Act.DyActFibreCoverOn.{0}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hIn : SB.Ly.SB3StageInputsRStatement.{u})
    (hSB2 : SB.Lz.SB2LowerLaunchEntryAdmStatement.{u}) (hLift : SB.Lf.SB2LowerTailLiftStatement.{u})
    (hSB2L : SB.Lf.SB2LeftLaunchStatement.{u}) (hLiftL : SB.Lf.SB2LeftTailLiftStatement.{u})
    (hArc : SB.Lf.SB2ArcLaunchStatement.{u}) (hArcLift : SB.Lf.SB2ArcTailLiftStatement.{u})
    (hRep : GW4Fix.Mart.GW4ComponentRepAStatement.{u}) : Theorem14Statement.{u} :=
  theorem14Statement_of_sb4Lift h12 h13 h12₀ h13₀ hTests
    (SB.Ly.sb3InductionGenRStatement_of_inputs_dyCover hSB2up h12 h13 h12₀ h13₀ hDy hDy₀ hIn)
    hSB2 hLift hSB2L hLiftL hArc hArcLift hRep

end InteractingSLE.Wire
