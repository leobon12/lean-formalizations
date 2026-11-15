/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLuAmb
import InteractingSLE.Spec.Wire.T14Asm4

/-!
# Theorem 1.4 with SB3 reduced to SB2(1)

Packet PROVE-T14-SBLEAVES6. `Wire.theorem14Statement_assembled4` with its binder `hSB3` (R95's amended SB3)
discharged by `sb3InductionGenRStatement_of_sb2`: SB3's stage inputs (I2), (I2′), (I5) are proved, so SB3 needs only
SB2(1) in GW1's ambient setting, Theorems 1.2–1.3 and the small-gap fibre cover.

R48: Theorems 1.2–1.3 are hypotheses of this Theorem 1.4 result only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

namespace InteractingSLE.Theorem14.SB.LuM

/-- **Theorem 1.4 (all four clauses)** from Theorems 1.2–1.3 (universes `u` and `0`), GW2's root tests, SB2(1) in GW1's
ambient setting (`Ly.SB2UpperLaunchEntryLAmbStatement`), the small-gap fibre cover, the two amended SB4 launch-tail
leaves and GW4's representation half. -/
theorem theorem14Statement_assembled4_of_sb2
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hTests : GW2TipSystem.GW2RootTestStatement.{u})
    (hSB2 : Ly.SB2UpperLaunchEntryLAmbStatement.{u})
    (hDy : Sec5.Aux61Act.DyActFibreCoverOn.{u}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hDy₀ : Sec5.Aux61Act.DyActFibreCoverOn.{0}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hDS : Ly.SB4DistinctSeedLaunchTailRStatement.{u})
    (hIA : Ly.SB4InitialArcLaunchTailRStatement.{u})
    (hRep : GW4Fix.Mart.GW4ComponentRepAStatement.{u}) : Wire.Theorem14Statement.{u} :=
  Wire.theorem14Statement_assembled4 h12 h13 h12₀ h13₀ hTests
    (sb3InductionGenRStatement_of_sb2 hSB2 h12 h13 h12₀ h13₀ hDy hDy₀) hDS hIA hRep

end InteractingSLE.Theorem14.SB.LuM
