/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB4RSymLeft
import InteractingSLE.Spec.Supplement.SB4RTop

/-!
# Theorem 1.4's two SB4 leaves from SB2(2)'s combined target (ruling R104a)

Packet PROVE-T14-SB4LEAF, round 2. With the reflection symmetry of staged histories (`SB4RSym*.lean`), the mirrored
left-walk input is no longer needed: the two SB4 binders `hDS`, `hIA` of `Wire.theorem14Statement_assembled4` follow
from

* SB2(2)'s combined target `SB.Lh.SB2LowerLaunchLiftStatement` (PROVE-T14-SB2LOW; an output whose completed lower
  tail lifts), which gives both halves of the distinct-seed leaf (the left half by
  `SB.Lf.sb2LeftLaunchLiftStatement_of_lower`);
* the initial-arc version `SB.Lf.SB2ArcLaunchLiftStatement` (named input, R104a's combined form);
* Theorems 1.2–1.3 (universes `u` and `0`).

Results: **`sb4DistinctSeedLaunchTailRStatement_of_sb2Lift`**, **`sb4InitialArcLaunchTailRStatement_of_arcLift`**,
**`theorem14Statement_of_sb2Lift`** and `theorem14Statement_of_sb2Lift_sb3Inputs`.

R48: Theorems 1.2–1.3 are hypotheses of these Theorem 1.4 results only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

namespace InteractingSLE.Wire

open Theorem14

/-- **SB4's distinct-seed leaf `hDS` with R95's premise from SB2(2)'s combined target** (both halves: the left one by
the reflection symmetry). -/
theorem sb4DistinctSeedLaunchTailRStatement_of_sb2Lift (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h13₀ : Exist.Theorem13Statement.{0})
    (hC : SB.Lh.SB2LowerLaunchLiftStatement.{u}) (hPR : WalkCont.RightWalkProperRegStatement.{u})
    (hPL : GW3SidedProof.LeftWalkProperRegStatement.{u}) : SB.Ly.SB4DistinctSeedLaunchTailRStatement.{u} := by
  have hCL := SB.Lf.sb2LeftLaunchLiftStatement_of_lower h12 h13 h13₀ hC
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg l hl h41
  exact ⟨fun u hu hθ hL _ => SB.Lf.scheduleLaunchTailR_lower_lift hC hPR h13 hκ hκ4 hb hh hcf hζ' hE hreg
      hl hu hθ hL,
    fun v hv hθ hR hH => SB.Lf.scheduleRelativeTailR_left_lift hCL hPL h13 hκ hκ4 hb hh hcf hζ' hE hreg
      hl h41 hv hθ hR hH⟩

/-- **SB4's initial-arc leaf `hIA` with R95's premise**, from SB2(2) at the arc seed in R104a's combined form. -/
theorem sb4InitialArcLaunchTailRStatement_of_arcLift (hA : SB.Lf.SB2ArcLaunchLiftStatement.{u})
    (hPR : WalkCont.RightWalkProperRegStatement.{u}) (h13 : Exist.Theorem13Statement.{u}) :
    SB.Ly.SB4InitialArcLaunchTailRStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg v hv hlow0 hlow l hl _ hθ
  exact SB.Lf.scheduleLaunchTailR_arc_lift hA hPR h13 hκ hκ4 hb hh hcf hζ' hE hreg hv hlow0 hlow hl hθ

/-- **Theorem 1.4 (all four clauses)** from Theorems 1.2–1.3 (universes `u` and `0`), GW2's root tests `hTests`,
R95's amended SB3, SB2(2)'s combined target, its initial-arc version (both R104a) and GW4's representation half
`hRep` (`theorem14Statement_assembled4` with the two SB4 leaves discharged). -/
theorem theorem14Statement_of_sb2Lift
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hTests : GW2TipSystem.GW2RootTestStatement.{u})
    (hSB3 : SB.Ly.SB3InductionGenRStatement.{u})
    (hC : SB.Lh.SB2LowerLaunchLiftStatement.{u}) (hA : SB.Lf.SB2ArcLaunchLiftStatement.{u})
    (hRep : GW4Fix.Mart.GW4ComponentRepAStatement.{u}) : Theorem14Statement.{u} := by
  obtain ⟨hPR, hPL⟩ := walkProperRegStatements_of_thm12_thm13 h12 h13 h12₀ h13₀
  exact theorem14Statement_assembled4 h12 h13 h12₀ h13₀ hTests hSB3
    (sb4DistinctSeedLaunchTailRStatement_of_sb2Lift h12 h13 h13₀ hC hPR hPL)
    (sb4InitialArcLaunchTailRStatement_of_arcLift hA hPR h13) hRep

/-- **Theorem 1.4 with SB3 reduced**: as `theorem14Statement_of_sb2Lift`, with the amended SB3 from SB2(1) at launch
samples (ambient form), the small-gap fibre cover and the three stage inputs
(`SB.Ly.sb3InductionGenRStatement_of_inputs_dyCover`). -/
theorem theorem14Statement_of_sb2Lift_sb3Inputs
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hTests : GW2TipSystem.GW2RootTestStatement.{u})
    (hSB2up : SB.Ly.SB2UpperLaunchEntryLAmbStatement.{u})
    (hDy : Sec5.Aux61Act.DyActFibreCoverOn.{u}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hDy₀ : Sec5.Aux61Act.DyActFibreCoverOn.{0}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hIn : SB.Ly.SB3StageInputsRStatement.{u})
    (hC : SB.Lh.SB2LowerLaunchLiftStatement.{u}) (hA : SB.Lf.SB2ArcLaunchLiftStatement.{u})
    (hRep : GW4Fix.Mart.GW4ComponentRepAStatement.{u}) : Theorem14Statement.{u} :=
  theorem14Statement_of_sb2Lift h12 h13 h12₀ h13₀ hTests
    (SB.Ly.sb3InductionGenRStatement_of_inputs_dyCover hSB2up h12 h13 h12₀ h13₀ hDy hDy₀ hIn) hC hA hRep

end InteractingSLE.Wire
