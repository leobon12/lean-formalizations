/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB4RTrTop
import InteractingSLE.Spec.Supplement.SBLuAmb
import InteractingSLE.Spec.Supplement.SB2LkSplit
import InteractingSLE.Spec.Supplement.SB2LkFree
import InteractingSLE.Spec.Supplement.SB2DrvHint
import InteractingSLE.Spec.Supplement.SB2WdFinal
import InteractingSLE.Spec.Supplement.GW2CvStatement
import InteractingSLE.Spec.Supplement.GW2RdLocUnion
import InteractingSLE.Spec.Supplement.GW4SafeRMuWire
import InteractingSLE.Spec.Exist.Param12Canonical
import InteractingSLE.Spec.Wire.T12Asm6

/-!
# Theorem 1.4 re-assembled with the reductions landed up to e58a61b63

Packet PROVE-T14-ASSEMBLE6. `Wire.theorem14Statement_assembled5` (14 binders) is re-assembled with:

* **SB2(1)** from SB2DRV's route A: `Lv.sb2UpperLaunchEntryLAmbStatement_of_driverLink` with
  `Lv.sb2DriverLinkAmbStatement_of_entranceK2N` (`Theorem12ParamStatement` from Theorems 1.2–1.3); open:
  `Lv.SB2EntranceK2NStatement`;
* **SB2(2) and SB4** from SB4LEAF's `theorem14Statement_of_sb2Lift_free` (both SB4 leaves from SB2(2)'s combined
  target), with SB2LIFT's split `Lk.sb2LowerLaunchLiftStatement_of_split` (open: `Lk.SB2LowerRelWalkStatement`,
  `Lk.SB2LowerRelStageCondStatement`) and the proved `Lk.lowerWalkLeftFreeStatement_of_thm12_thm13`;
* **SB3** from SB2(1) by `LuM.sb3InductionGenRStatement_of_sb2`; **GW4** by `GW4Fix.gw4ComponentRepAStatement`;
* **GW2's root cover** discharged by COVER (`RootCv.gw2RootTestStatement_of_scaledCover`, and the unscaled
  `RootCv.gw2RootTestStatement_of_cover`); ROOT2's construction `D`, `hGeometry`, `hNear`, `hSlow` stay binders
  (no committed theorem produces them; JOINTDET's committed core does not reach them);
* **Theorems 1.2–1.3** either as binders (R48 allows them for Theorem 1.4) or from the fibre covers alone
  (`T12Asm6.theorem12Statement_of_covers`, `theorem13Statement_of_covers`).

Lemma S3 (`S3.s3RegStatement_of_rationalJointComparison`) is not a binder: no committed module on this route consumes
`S3RegStatement`; it enters only inside the open SB2 inputs (SB2DRV's (E3/E5), SB2LIFT's geometric half).
RELDET's `GW2Rd.gw2JointDetC2Statement_of_thm12_thm13_mean_thr` is likewise not consumed on this route;
`gw2JointKernelC2Statement_of_thm12_thm13_mean_thr` records its current form.

All results are conditional helpers; no frozen declaration changes.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

namespace InteractingSLE.Wire

open MeasureTheory Theorem14

/-- **SB2(1) in the ambient form** (`hSB2` of `theorem14Statement_assembled5`) from Theorems 1.2–1.3 and SB2DRV's
route-A input `SB2EntranceK2NStatement` (the (E4) integrability clause is proved). -/
theorem sb2UpperLaunchEntryLAmbStatement_of_entranceK2N (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (hN : SB.Lv.SB2EntranceK2NStatement.{u}) :
    SB.Ly.SB2UpperLaunchEntryLAmbStatement.{u} :=
  SB.Lv.sb2UpperLaunchEntryLAmbStatement_of_driverLink h13
    (SB.Lv.sb2DriverLinkAmbStatement_of_entranceK2N
      (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13) h13 hN)

/-- **GW2's corrected joint kernel** from Theorems 1.2–1.3 and RELDET's two open statements (union mean, threshold).
Not consumed by the Theorem 1.4 tops below: no committed theorem turns it into ROOT2's near/slow comparisons. -/
theorem gw2JointKernelC2Statement_of_thm12_thm13_mean_thr (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0})
    (h13₀ : Exist.Theorem13Statement.{0}) (hM : GW2Rd.GW2RdUnionMeanStatement.{u})
    (hT : GW2Rd.GW2RdThrStatement.{u}) : GW2JointKernel.GW2JointKernelC2Statement.{u} :=
  GW2JointKernel.gw2JointKernelC2Statement_of_detC2
    (GW2Rd.gw2JointDetC2Statement_of_thm12_thm13_mean_thr
      (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12₀ h13₀) h13₀ h12 h13 hM hT)

/-- **Theorem 1.4 (all four clauses) from GW2's root tests**: SB2(1) from SB2DRV's route A, SB3 from SB2(1), SB2(2)
from SB2LIFT's two halves, both SB4 leaves from SB2(2) (SB4LEAF), GW4's representation proved. -/
theorem theorem14Statement_assembled6_of_rootTests
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hTests : GW2TipSystem.GW2RootTestStatement.{u})
    (hN : SB.Lv.SB2EntranceK2NStatement.{u})
    (hgeo : SB.Lk.SB2LowerRelWalkStatement.{u}) (hcond : SB.Lk.SB2LowerRelStageCondStatement.{u})
    (hDy : Sec5.Aux61Act.DyActFibreCoverOn.{u}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hDy₀ : Sec5.Aux61Act.DyActFibreCoverOn.{0}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin) :
    Theorem14Statement.{u} :=
  theorem14Statement_of_sb2Lift_free h12 h13 h12₀ h13₀ hTests
    (SB.LuM.sb3InductionGenRStatement_of_sb2 (sb2UpperLaunchEntryLAmbStatement_of_entranceK2N h12 h13 hN)
      h12 h13 h12₀ h13₀ hDy hDy₀)
    (SB.Lk.sb2LowerLaunchLiftStatement_of_split h12 h13 h12₀ h13₀ hgeo hcond)
    (SB.Lk.lowerWalkLeftFreeStatement_of_thm12_thm13 h12 h13 h12₀ h13₀)
    (GW4Fix.gw4ComponentRepAStatement h12 h13)

/-- **Theorem 1.4 (all four clauses), main top.** GW2's root tests from ROOT2's construction `D` with COVER's scaled
root cover (label gap `gap`, stage-start measurable and a.s. positive on the cover events) and the three remaining
C24 assertions for `withScaledCover D gap`; the SB inputs as in `theorem14Statement_assembled6_of_rootTests`. -/
theorem theorem14Statement_assembled6
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (D : GW2TipSystem.RootC24.ConstructionFamily.{u}) (gap : GW2TipSystem.RootCv.GapFamily.{u})
    (hgap : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : GW2TipSystem.RootC24.SourceData Ω)
      (r : GW2TipSystem.ScaledRootIdx c.Θ c.Q), Measurable[c.sigma r []] (gap Ω c r.1))
    (hpos : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : GW2TipSystem.RootC24.SourceData Ω)
      (x : GW2TipSystem.RootIdx c.Θ c.Q),
      ∀ᵐ ω ∂c.P, ω ∈ GW2TipSystem.RootCv.coverEvent c (x, 0) → 0 < gap Ω c x ω)
    (hGeometry : GW2TipSystem.RootC24.RootGeometryStatement (GW2TipSystem.RootCv.withScaledCover D gap))
    (hNear : GW2TipSystem.RootC24.RetainedNearModelsStatement (GW2TipSystem.RootCv.withScaledCover D gap))
    (hSlow : GW2TipSystem.RootC24.RetainedSlowComparisonsStatement (GW2TipSystem.RootCv.withScaledCover D gap))
    (hN : SB.Lv.SB2EntranceK2NStatement.{u})
    (hgeo : SB.Lk.SB2LowerRelWalkStatement.{u}) (hcond : SB.Lk.SB2LowerRelStageCondStatement.{u})
    (hDy : Sec5.Aux61Act.DyActFibreCoverOn.{u}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hDy₀ : Sec5.Aux61Act.DyActFibreCoverOn.{0}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin) :
    Theorem14Statement.{u} :=
  theorem14Statement_assembled6_of_rootTests h12 h13 h12₀ h13₀
    (GW2TipSystem.RootCv.gw2RootTestStatement_of_scaledCover h13 h13₀ D gap hgap hpos hGeometry hNear hSlow)
    hN hgeo hcond hDy hDy₀

/-- **Theorem 1.4, unscaled-cover variant**: as `theorem14Statement_assembled6` with COVER's unscaled root cover
(`withCover D`), so the label-gap binders disappear (usable if ROOT2's experiment needs no dilation). -/
theorem theorem14Statement_assembled6_unscaled
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (D : GW2TipSystem.RootC24.ConstructionFamily.{u})
    (hGeometry : GW2TipSystem.RootC24.RootGeometryStatement (GW2TipSystem.RootCv.withCover D))
    (hNear : GW2TipSystem.RootC24.RetainedNearModelsStatement (GW2TipSystem.RootCv.withCover D))
    (hSlow : GW2TipSystem.RootC24.RetainedSlowComparisonsStatement (GW2TipSystem.RootCv.withCover D))
    (hN : SB.Lv.SB2EntranceK2NStatement.{u})
    (hgeo : SB.Lk.SB2LowerRelWalkStatement.{u}) (hcond : SB.Lk.SB2LowerRelStageCondStatement.{u})
    (hDy : Sec5.Aux61Act.DyActFibreCoverOn.{u}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hDy₀ : Sec5.Aux61Act.DyActFibreCoverOn.{0}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin) :
    Theorem14Statement.{u} :=
  theorem14Statement_assembled6_of_rootTests h12 h13 h12₀ h13₀
    (GW2TipSystem.RootCv.gw2RootTestStatement_of_cover h13 h13₀ D hGeometry hNear hSlow)
    hN hgeo hcond hDy hDy₀

/-- **Theorem 1.4 with Theorems 1.2–1.3 from the fibre covers** (`T12Asm6`): the binders are exactly the open
inputs — the fibre covers `hDy` (universe `u`) and `hDy₀` (universe `0`), ROOT2's construction with COVER's scaled
cover and the three C24 assertions, SB2DRV's `SB2EntranceK2NStatement` and SB2LIFT's two halves. -/
theorem theorem14Statement_assembled6_covers
    (D : GW2TipSystem.RootC24.ConstructionFamily.{u}) (gap : GW2TipSystem.RootCv.GapFamily.{u})
    (hgap : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : GW2TipSystem.RootC24.SourceData Ω)
      (r : GW2TipSystem.ScaledRootIdx c.Θ c.Q), Measurable[c.sigma r []] (gap Ω c r.1))
    (hpos : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : GW2TipSystem.RootC24.SourceData Ω)
      (x : GW2TipSystem.RootIdx c.Θ c.Q),
      ∀ᵐ ω ∂c.P, ω ∈ GW2TipSystem.RootCv.coverEvent c (x, 0) → 0 < gap Ω c x ω)
    (hGeometry : GW2TipSystem.RootC24.RootGeometryStatement (GW2TipSystem.RootCv.withScaledCover D gap))
    (hNear : GW2TipSystem.RootC24.RetainedNearModelsStatement (GW2TipSystem.RootCv.withScaledCover D gap))
    (hSlow : GW2TipSystem.RootC24.RetainedSlowComparisonsStatement (GW2TipSystem.RootCv.withScaledCover D gap))
    (hN : SB.Lv.SB2EntranceK2NStatement.{u})
    (hgeo : SB.Lk.SB2LowerRelWalkStatement.{u}) (hcond : SB.Lk.SB2LowerRelStageCondStatement.{u})
    (hDy : Sec5.Aux61Act.DyActFibreCoverOn.{u}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hDy₀ : Sec5.Aux61Act.DyActFibreCoverOn.{0}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin) :
    Theorem14Statement.{u} :=
  theorem14Statement_assembled6
    (T12Asm6.theorem12Statement_of_covers.{u} hDy hDy₀) (T12Asm6.theorem13Statement_of_covers.{u} hDy₀)
    (T12Asm6.theorem12Statement_of_covers.{0} hDy₀ hDy₀) (T12Asm6.theorem13Statement_of_covers.{0} hDy₀)
    D gap hgap hpos hGeometry hNear hSlow hN hgeo hcond hDy hDy₀

/-- **Theorem 1.4 from nine open inputs**: as `theorem14Statement_assembled6_covers` with COVER's unscaled root
cover (`withCover D`): the fibre covers, ROOT2's construction with its three C24 assertions, SB2DRV's
`SB2EntranceK2NStatement` and SB2LIFT's two halves. -/
theorem theorem14Statement_assembled6_covers_unscaled
    (D : GW2TipSystem.RootC24.ConstructionFamily.{u})
    (hGeometry : GW2TipSystem.RootC24.RootGeometryStatement (GW2TipSystem.RootCv.withCover D))
    (hNear : GW2TipSystem.RootC24.RetainedNearModelsStatement (GW2TipSystem.RootCv.withCover D))
    (hSlow : GW2TipSystem.RootC24.RetainedSlowComparisonsStatement (GW2TipSystem.RootCv.withCover D))
    (hN : SB.Lv.SB2EntranceK2NStatement.{u})
    (hgeo : SB.Lk.SB2LowerRelWalkStatement.{u}) (hcond : SB.Lk.SB2LowerRelStageCondStatement.{u})
    (hDy : Sec5.Aux61Act.DyActFibreCoverOn.{u}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hDy₀ : Sec5.Aux61Act.DyActFibreCoverOn.{0}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin) :
    Theorem14Statement.{u} :=
  theorem14Statement_assembled6_unscaled
    (T12Asm6.theorem12Statement_of_covers.{u} hDy hDy₀) (T12Asm6.theorem13Statement_of_covers.{u} hDy₀)
    (T12Asm6.theorem12Statement_of_covers.{0} hDy₀ hDy₀) (T12Asm6.theorem13Statement_of_covers.{0} hDy₀)
    D hGeometry hNear hSlow hN hgeo hcond hDy hDy₀

end InteractingSLE.Wire
