/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB4RTrArc
import InteractingSLE.Spec.Supplement.SB4RSymTop

/-!
# Theorem 1.4's SB4 leaves from SB2(2)'s combined target alone

Packet PROVE-T14-SB4LEAF, round 3. With the reflection symmetry (left walk) and the translation symmetry with the
walk restart (initial arc), both SB4 binders `hDS`, `hIA` of `Wire.theorem14Statement_assembled4` follow from SB2(2)'s
combined target `SB.Lh.SB2LowerLaunchLiftStatement` (PROVE-T14-SB2LOW), the free real point of the completed lower walk
`SB.Lh.LowerWalkLeftFreeStatement` (PROVE-T14-SB2LIFT) and Theorems 1.2–1.3:

* **`sb4InitialArcLaunchTailRStatement_of_sb2Lift`**;
* **`theorem14Statement_of_sb2Lift_free`**, `theorem14Statement_of_sb2Lift_free_sb3Inputs`.

R48: Theorems 1.2–1.3 are hypotheses of these Theorem 1.4 results only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

namespace InteractingSLE.Wire

open Theorem14

/-- **SB4's initial-arc leaf `hIA` from SB2(2)'s combined target** (by translation and restart). -/
theorem sb4InitialArcLaunchTailRStatement_of_sb2Lift (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hC : SB.Lh.SB2LowerLaunchLiftStatement.{u}) (hfree : SB.Lh.LowerWalkLeftFreeStatement.{u}) :
    SB.Ly.SB4InitialArcLaunchTailRStatement.{u} :=
  sb4InitialArcLaunchTailRStatement_of_arcLift (SB.Lf.sb2ArcLaunchLiftStatement_of_lower h12 h13 h12₀ h13₀ hC hfree)
    (walkProperRegStatements_of_thm12_thm13 h12 h13 h12₀ h13₀).1 h13

/-- **Theorem 1.4 (all four clauses)** from Theorems 1.2–1.3 (universes `u` and `0`), GW2's root tests `hTests`,
R95's amended SB3, SB2(2)'s combined target, the free real point of the completed lower walk and GW4's
representation half `hRep`. -/
theorem theorem14Statement_of_sb2Lift_free
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hTests : GW2TipSystem.GW2RootTestStatement.{u})
    (hSB3 : SB.Ly.SB3InductionGenRStatement.{u})
    (hC : SB.Lh.SB2LowerLaunchLiftStatement.{u}) (hfree : SB.Lh.LowerWalkLeftFreeStatement.{u})
    (hRep : GW4Fix.Mart.GW4ComponentRepAStatement.{u}) : Theorem14Statement.{u} :=
  theorem14Statement_of_sb2Lift h12 h13 h12₀ h13₀ hTests hSB3 hC
    (SB.Lf.sb2ArcLaunchLiftStatement_of_lower h12 h13 h12₀ h13₀ hC hfree) hRep

/-- **Theorem 1.4 with SB3 reduced**: as `theorem14Statement_of_sb2Lift_free`, with the amended SB3 from SB2(1) at
launch samples (ambient form), the small-gap fibre cover and the three stage inputs. -/
theorem theorem14Statement_of_sb2Lift_free_sb3Inputs
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hTests : GW2TipSystem.GW2RootTestStatement.{u})
    (hSB2up : SB.Ly.SB2UpperLaunchEntryLAmbStatement.{u})
    (hDy : Sec5.Aux61Act.DyActFibreCoverOn.{u}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hDy₀ : Sec5.Aux61Act.DyActFibreCoverOn.{0}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hIn : SB.Ly.SB3StageInputsRStatement.{u})
    (hC : SB.Lh.SB2LowerLaunchLiftStatement.{u}) (hfree : SB.Lh.LowerWalkLeftFreeStatement.{u})
    (hRep : GW4Fix.Mart.GW4ComponentRepAStatement.{u}) : Theorem14Statement.{u} :=
  theorem14Statement_of_sb2Lift_free h12 h13 h12₀ h13₀ hTests
    (SB.Ly.sb3InductionGenRStatement_of_inputs_dyCover hSB2up h12 h13 h12₀ h13₀ hDy hDy₀ hIn) hC hfree hRep

end InteractingSLE.Wire
