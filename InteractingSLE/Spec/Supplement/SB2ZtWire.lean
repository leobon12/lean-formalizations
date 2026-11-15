/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2ZtFin
import InteractingSLE.Spec.Supplement.SBS3DzWire

/-!
# SB2(1)'s final gluing, part 4: wiring (the endpoint input dropped)

Packet PROVE-T14-SB2DRV (round 16). With the identification at the stops (decision D4), SB2(1) for `ψ ≤ π/2` needs
only E7 (`Vh.SB2RemainderLifeLeStatement`) beyond Theorems 1.2–1.3: the relative endpoint
(`Vk.SB2RelEndpointLeStatement`, the second input of the R route) is no longer an input.

* **`Lv.sb2UpperLaunchEntryLAmbLeStatement_of_remainderLife`**: SB2(1) in GW1's ambient setting;
* **`Wire.theorem14Statement_assembled6Le_of_rootTests'`**, **`Wire.theorem14Statement_assembled6Le'`**: Theorem
  1.4's D22 tops (`theorem14Statement_assembled6Le(_of_rootTests)`) without the input `hEnd`.

**R48.** Theorems 1.2–1.3 are hypotheses. No source theorem is replaced.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

universe u

namespace InteractingSLE.Theorem14.SB

/-- **SB2(1) in GW1's ambient setting, `ψ ≤ π/2`**, from Theorems 1.2–1.3 (universes `u` and `0`) and E7 alone. -/
theorem Lv.sb2UpperLaunchEntryLAmbLeStatement_of_remainderLife (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hE7 : Vh.SB2RemainderLifeLeStatement.{u}) : Ly.SB2UpperLaunchEntryLAmbLeStatement.{u} :=
  Lv.sb2UpperLaunchEntryLAmbStatement_of_driverLinkLe h13
    (Zt.sb2DriverLinkAmbLeStatement_of_remainderLife (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13)
      h13 (Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12₀ h13₀) h13₀ hE7)

end InteractingSLE.Theorem14.SB

namespace InteractingSLE.Wire

open MeasureTheory Theorem14

/-- **Theorem 1.4 from GW2's root tests, D22 form, without the endpoint input** (`theorem14Statement_assembled6Le_of_
rootTests` with SB2(1) from E7 alone). -/
theorem theorem14Statement_assembled6Le_of_rootTests'
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hTests : GW2TipSystem.GW2RootTestStatement.{u})
    (hE7 : SB.Vh.SB2RemainderLifeLeStatement.{u})
    (hgeo : SB.Lk.SB2LowerRelWalkStatement.{u}) (hcond : SB.Lk.SB2LowerRelStageCondStatement.{u})
    (hDy : Sec5.Aux61Act.DyActFibreCoverOn.{u}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hDy₀ : Sec5.Aux61Act.DyActFibreCoverOn.{0}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin) :
    Theorem14Statement.{u} :=
  theorem14Statement_of_sb2Lift_freeLe h12 h13 h12₀ h13₀ hTests
    (SB.LuM.sb3InductionGenRStatement_of_sb2Le
      (SB.Lv.sb2UpperLaunchEntryLAmbLeStatement_of_remainderLife h12 h13 h12₀ h13₀ hE7) h12 h13 h12₀ h13₀ hDy hDy₀)
    (SB.Lk.sb2LowerLaunchLiftStatement_of_split h12 h13 h12₀ h13₀ hgeo hcond)
    (SB.Lk.lowerWalkLeftFreeStatement_of_thm12_thm13 h12 h13 h12₀ h13₀)
    (GW4Fix.gw4ComponentRepAStatement h12 h13)

/-- **Theorem 1.4, main top, D22 form, without the endpoint input** (`theorem14Statement_assembled6Le` with SB2(1)
from E7 alone). -/
theorem theorem14Statement_assembled6Le'
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
    (hE7 : SB.Vh.SB2RemainderLifeLeStatement.{u})
    (hgeo : SB.Lk.SB2LowerRelWalkStatement.{u}) (hcond : SB.Lk.SB2LowerRelStageCondStatement.{u})
    (hDy : Sec5.Aux61Act.DyActFibreCoverOn.{u}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hDy₀ : Sec5.Aux61Act.DyActFibreCoverOn.{0}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin) :
    Theorem14Statement.{u} :=
  theorem14Statement_assembled6Le_of_rootTests' h12 h13 h12₀ h13₀
    (GW2TipSystem.RootCv.gw2RootTestStatement_of_scaledCover h13 h13₀ D gap hgap hpos hGeometry hNear hSlow)
    hE7 hgeo hcond hDy hDy₀

end InteractingSLE.Wire
