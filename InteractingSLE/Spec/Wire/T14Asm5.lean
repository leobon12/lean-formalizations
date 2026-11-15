/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLuTop
import InteractingSLE.Spec.Supplement.GW4SafeRMuWire
import InteractingSLE.Spec.Supplement.GW2RootC24Assembly
import InteractingSLE.Spec.Supplement.GW2FbReduce

/-!
# Theorem 1.4 with GW4 complete and SB3 reduced to SB2

Packet PROVE-T14-ASSEMBLE5. `theorem14Statement_assembled5_of_rootTests` discharges
`hRep` and `hSB3` of `theorem14Statement_assembled4` using the proved GW4 representation
and SB3 reduction. `theorem14Statement_assembled5` also replaces `hTests` by ROOT2's
conditional construction, retaining its four open assertions explicitly.

The remaining SB inputs are SB2(1) in ambient form, the small-gap fibre cover at
universes `u` and `0`, and the two amended SB4 launch-tail leaves. These are the latest
committed leaves; the in-flight `SB4R*` modules are not imported.

`gw2JointKernelC2Statement_of_relDetGen_thm13` supplies FABLE's joint determination
reduction and the corrected joint kernel with nonreturn discharged by Theorem 1.3.
This does not discharge ROOT2's one-sided comparisons: no proved adapter from joint
determination to those all-history comparisons is available. The main top therefore
retains them, rather than assuming that the root-test statement follows from (Det).

All results are conditional helpers; no frozen declaration changes. Theorems 1.2–1.3
are permitted inputs on this Theorem 1.4 route (R48).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

namespace InteractingSLE.Wire

open Theorem14

/-- FABLE's general relative determination gives GW2's corrected joint kernel;
Theorem 1.3 supplies the counterflow's nonreturn to its base. -/
theorem gw2JointKernelC2Statement_of_relDetGen_thm13
    (h13 : Exist.Theorem13Statement.{u}) (hD : GW2Fb.RelDetGenStatement.{u}) :
    GW2JointKernel.GW2JointKernelC2Statement.{u} :=
  GW2JointKernel.gw2JointKernelC2Statement_of_detC2
    (GW2Fb.gw2JointDetC2Statement_of_relDetGen
      (counterflowNoReturnStatement_of_theorem13 h13) hD)

/-- All four clauses of Theorem 1.4 with GW4's representation proved and SB3
reduced to SB2(1), Theorems 1.2–1.3 and the small-gap fibre cover. -/
theorem theorem14Statement_assembled5_of_rootTests
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hTests : GW2TipSystem.GW2RootTestStatement.{u})
    (hSB2 : SB.Ly.SB2UpperLaunchEntryLAmbStatement.{u})
    (hDy : Sec5.Aux61Act.DyActFibreCoverOn.{u}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hDy₀ : Sec5.Aux61Act.DyActFibreCoverOn.{0}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hDS : SB.Ly.SB4DistinctSeedLaunchTailRStatement.{u})
    (hIA : SB.Ly.SB4InitialArcLaunchTailRStatement.{u}) : Theorem14Statement.{u} :=
  SB.LuM.theorem14Statement_assembled4_of_sb2 h12 h13 h12₀ h13₀ hTests
    hSB2 hDy hDy₀ hDS hIA (GW4Fix.gw4ComponentRepAStatement h12 h13)

/-- All four clauses of Theorem 1.4 from ROOT2's concrete construction and its
four open assertions, SB2(1), the fibre cover and the committed SB4 leaves.
GW4's representation and SB3's stage inputs require no further hypotheses. -/
theorem theorem14Statement_assembled5
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (D : GW2TipSystem.RootC24.ConstructionFamily.{u})
    (hCover : GW2TipSystem.RootC24.RootCoverStatement D)
    (hGeometry : GW2TipSystem.RootC24.RootGeometryStatement D)
    (hNear : GW2TipSystem.RootC24.RetainedNearModelsStatement D)
    (hSlow : GW2TipSystem.RootC24.RetainedSlowComparisonsStatement D)
    (hSB2 : SB.Ly.SB2UpperLaunchEntryLAmbStatement.{u})
    (hDy : Sec5.Aux61Act.DyActFibreCoverOn.{u}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hDy₀ : Sec5.Aux61Act.DyActFibreCoverOn.{0}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hDS : SB.Ly.SB4DistinctSeedLaunchTailRStatement.{u})
    (hIA : SB.Ly.SB4InitialArcLaunchTailRStatement.{u}) : Theorem14Statement.{u} :=
  theorem14Statement_assembled5_of_rootTests h12 h13 h12₀ h13₀
    (GW2TipSystem.RootC24.gw2RootTestStatement_of_oneSided_comparisons
      h13 D hCover hGeometry hNear hSlow) hSB2 hDy hDy₀ hDS hIA

end InteractingSLE.Wire
