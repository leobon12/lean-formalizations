/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdjTop

/-!
# Theorem 1.4's top with the lossy near binder on COVER's SCALED cover (the corrected frame for the near words)

Packet PROVE-GW2-SDE (round 8). `GW2SdkNec` shows that the near words force a stage-word label beyond `±3/(2^{r.2} λ)`,
which the unscaled cover does not provide (the source rescales per configuration, spec p. 621). COVER's scaled cover
`scaledCoverEvent c gap (x, k) = coverEvent c (x, k) ∩ {3 < 2^k · gap x}` is the event that does. This file gives
the lossy
Theorem 1.4 top on the scaled cover (GEOM2's `Gm.theorem14Statement_scaled_V` with the lossy near binder):

* `gw2RootTestStatement_of_scaledCover_V_lossy`, **`theorem14Statement_scaled_V_lossy`**;
* **`theorem14Statement_J32_scaled_lossy`**: J32 on the scaled cover.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Sdk

open GW2TipSystem GW2TipSystem.Gm GW2TipSystem.RootC24 GW2Sdj

/-- **The root-test assembly with COVER's scaled cover and the lossy near binder.** -/
theorem gw2RootTestStatement_of_scaledCover_V_lossy (h13 : Exist.Theorem13Statement.{u})
    (h13₀ : Exist.Theorem13Statement.{0}) (D : ConstructionFamily.{u}) (gap : RootCv.GapFamily.{u})
    (hgap : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q), Measurable[c.sigma r []] (gap Ω c r.1))
    (hpos : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (x : RootIdx c.Θ c.Q), ∀ᵐ ω ∂c.P, ω ∈ RootCv.coverEvent c (x, 0) → 0 < gap Ω c x ω)
    (hGeometry : RootGeometryVStatement (RootCv.withScaledCover D gap))
    (hNear : GW2Sdi.RetainedNearModelsLossyStatement (RootCv.withScaledCover D gap))
    (hSlow : RetainedSlowComparisonsStatement (RootCv.withScaledCover D gap)) :
    GW2RootTestStatement.{u} :=
  gw2RootTestStatement_of_oneSided_comparisons_V_lossy h13 (RootCv.withScaledCover D gap)
    (RootCv.rootCoverStatement_withScaledCover h13 h13₀ D gap hgap hpos) hGeometry hNear hSlow

/-- **Theorem 1.4 (all four clauses) on the scaled cover with the lossy near binder** (Theorems 1.2–1.3 from the
proved fibre leaf). -/
theorem theorem14Statement_scaled_V_lossy (D : ConstructionFamily.{u}) (gap : RootCv.GapFamily.{u})
    (hgap : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q), Measurable[c.sigma r []] (gap Ω c r.1))
    (hpos : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (x : RootIdx c.Θ c.Q), ∀ᵐ ω ∂c.P, ω ∈ RootCv.coverEvent c (x, 0) → 0 < gap Ω c x ω)
    (hGeometry : RootGeometryVStatement (RootCv.withScaledCover D gap))
    (hNear : GW2Sdi.RetainedNearModelsLossyStatement (RootCv.withScaledCover D gap))
    (hSlow : RetainedSlowComparisonsStatement (RootCv.withScaledCover D gap))
    (hN : SB.Lv.SB2EntranceK2NStatement.{u})
    (hgeo : SB.Lk.SB2LowerRelWalkStatement.{u}) (hcond : SB.Lk.SB2LowerRelStageCondStatement.{u}) :
    Wire.Theorem14Statement.{u} :=
  Wire.theorem14Statement_assembled6_of_rootTests
    Sec5.Aux61Cpt.theorem12Statement_of_cptCover.{u} Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{u}
    Sec5.Aux61Cpt.theorem12Statement_of_cptCover.{0} Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{0}
    (gw2RootTestStatement_of_scaledCover_V_lossy Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{u}
      Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{0} D gap hgap hpos hGeometry hNear hSlow)
    hN hgeo hcond Sec5.Aux61Cpt.cptFibreCover.{u} Sec5.Aux61Cpt.cptFibreCover₀

/-- **Theorem 1.4 with J32 on the scaled cover and the lossy near binder.** -/
theorem theorem14Statement_J32_scaled_lossy (gap : RootCv.GapFamily.{u})
    (hgap : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q), Measurable[c.sigma r []] (gap Ω c r.1))
    (hpos : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (x : RootIdx c.Θ c.Q), ∀ᵐ ω ∂c.P, ω ∈ RootCv.coverEvent c (x, 0) → 0 < gap Ω c x ω)
    (hGeometry : RootGeometryVStatement (RootCv.withScaledCover RootJ32.constructionFamily.{u} gap))
    (hNear : GW2Sdi.RetainedNearModelsLossyStatement (RootCv.withScaledCover RootJ32.constructionFamily.{u} gap))
    (hSlow : RetainedSlowComparisonsStatement (RootCv.withScaledCover RootJ32.constructionFamily.{u} gap))
    (hN : SB.Lv.SB2EntranceK2NStatement.{u})
    (hgeo : SB.Lk.SB2LowerRelWalkStatement.{u}) (hcond : SB.Lk.SB2LowerRelStageCondStatement.{u}) :
    Wire.Theorem14Statement.{u} :=
  theorem14Statement_scaled_V_lossy RootJ32.constructionFamily gap hgap hpos hGeometry hNear hSlow hN hgeo hcond

end InteractingSLE.Theorem14.GW2Sdk
