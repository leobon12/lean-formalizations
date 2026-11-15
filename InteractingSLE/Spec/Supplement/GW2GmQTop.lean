/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2GmQTest
import InteractingSLE.Spec.Supplement.GW2SdkTop

/-!
# Theorem 1.4's top with the D2 geometry (observation on alive histories)

Packet PROVE-GW2-GEOM2 (round 5; decision D2). Copies of PROVE-GW2-SDE's lossy tops (`GW2SdjTop`, `GW2SdkTop`) with
`RootGeometryAStatement` in place of `RootGeometryVStatement` (the top's hypothesis gets weaker):

* `gw2RootTestStatement_of_oneSided_comparisons_A_lossy`, `gw2RootTestStatement_of_scaledCover_A_lossy`;
* **`theorem14Statement_scaled_A_lossy`**, **`theorem14Statement_J32_scaled_lossy_A`**.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.Gm

open GW2Schedule Exist Staged StagedLaw Restart LQGMetric RootC24 RootK3 GW2Sdj

/-- **The complete root-test statement with the D2 geometry and the lossy near binder** (successor of
`GW2Sdj.gw2RootTestStatement_of_oneSided_comparisons_V_lossy`). -/
theorem gw2RootTestStatement_of_oneSided_comparisons_A_lossy
    (h13 : Theorem13Statement.{u}) (D : ConstructionFamily.{u})
    (hCover : RootCoverStatement D) (hGeometry : RootGeometryAStatement D)
    (hNear : GW2Sdi.RetainedNearModelsLossyStatement D)
    (hSlow : RetainedSlowComparisonsStatement D) :
    GW2RootTestStatement.{u} := by
  intro κ hκ hκ4 h12p βA hβA b jumps c₀ hb hc₀J hc₀ Ω _ _ P hP h hh
    W ζ hcf hζ Θ hΘ hΘc hΘd Q hQc hQd hQpos α hα s
  let c : SourceData Ω :=
    { κ := κ, hκ := hκ, hκ4 := hκ4, h12p := h12p, βA := βA, hβA := hβA
      b := b, jumps := jumps, c₀ := c₀, hb := hb, hc₀J := hc₀J, hc₀ := hc₀
      P := P, probability := hP, h := h, hh := hh, W := W, ζ := ζ
      hcf := hcf, hζ := hζ, Θ := Θ, hΘ := hΘ, hΘc := hΘc, hΘd := hΘd
      Q := Q, hQc := hQc, hQd := hQd, hQpos := hQpos, α := α, hα := hα, s := s }
  obtain ⟨hcov, hG⟩ := hCover Ω c
  refine ⟨(D Ω c).G, hcov, ?_⟩
  intro r
  let e := (D Ω c).experiment r
  obtain ⟨p₀, A, T, hp₀⟩ := ExperimentGeometryA.exists_testClaims_lossy (hGeometry Ω c r) h13 (hG r)
    (hNear Ω c r) (hSlow Ω c r)
  exact ⟨A, e.data.ang, T, RootF27.unitEvent c r, p₀, hp₀⟩

/-- **The root-test assembly with COVER's scaled cover, the D2 geometry and the lossy near binder** (successor of
`GW2Sdk.gw2RootTestStatement_of_scaledCover_V_lossy`). -/
theorem gw2RootTestStatement_of_scaledCover_A_lossy (h13 : Exist.Theorem13Statement.{u})
    (h13₀ : Exist.Theorem13Statement.{0}) (D : ConstructionFamily.{u}) (gap : RootCv.GapFamily.{u})
    (hgap : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q), Measurable[c.sigma r []] (gap Ω c r.1))
    (hpos : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (x : RootIdx c.Θ c.Q), ∀ᵐ ω ∂c.P, ω ∈ RootCv.coverEvent c (x, 0) → 0 < gap Ω c x ω)
    (hGeometry : RootGeometryAStatement (RootCv.withScaledCover D gap))
    (hNear : GW2Sdi.RetainedNearModelsLossyStatement (RootCv.withScaledCover D gap))
    (hSlow : RetainedSlowComparisonsStatement (RootCv.withScaledCover D gap)) :
    GW2RootTestStatement.{u} :=
  gw2RootTestStatement_of_oneSided_comparisons_A_lossy h13 (RootCv.withScaledCover D gap)
    (RootCv.rootCoverStatement_withScaledCover h13 h13₀ D gap hgap hpos) hGeometry hNear hSlow

/-- **Theorem 1.4 (all four clauses) on the scaled cover with the D2 geometry and the lossy near binder** (successor of
`GW2Sdk.theorem14Statement_scaled_V_lossy`; Theorems 1.2–1.3 from the proved fibre leaf). -/
theorem theorem14Statement_scaled_A_lossy (D : ConstructionFamily.{u}) (gap : RootCv.GapFamily.{u})
    (hgap : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q), Measurable[c.sigma r []] (gap Ω c r.1))
    (hpos : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (x : RootIdx c.Θ c.Q), ∀ᵐ ω ∂c.P, ω ∈ RootCv.coverEvent c (x, 0) → 0 < gap Ω c x ω)
    (hGeometry : RootGeometryAStatement (RootCv.withScaledCover D gap))
    (hNear : GW2Sdi.RetainedNearModelsLossyStatement (RootCv.withScaledCover D gap))
    (hSlow : RetainedSlowComparisonsStatement (RootCv.withScaledCover D gap))
    (hN : SB.Lv.SB2EntranceK2NStatement.{u})
    (hgeo : SB.Lk.SB2LowerRelWalkStatement.{u}) (hcond : SB.Lk.SB2LowerRelStageCondStatement.{u}) :
    Wire.Theorem14Statement.{u} :=
  Wire.theorem14Statement_assembled6_of_rootTests
    Sec5.Aux61Cpt.theorem12Statement_of_cptCover.{u} Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{u}
    Sec5.Aux61Cpt.theorem12Statement_of_cptCover.{0} Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{0}
    (gw2RootTestStatement_of_scaledCover_A_lossy Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{u}
      Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{0} D gap hgap hpos hGeometry hNear hSlow)
    hN hgeo hcond Sec5.Aux61Cpt.cptFibreCover.{u} Sec5.Aux61Cpt.cptFibreCover₀

/-- **Theorem 1.4 with J32 on the scaled cover, the D2 geometry and the lossy near binder** (successor of
`GW2Sdk.theorem14Statement_J32_scaled_lossy`). -/
theorem theorem14Statement_J32_scaled_lossy_A (gap : RootCv.GapFamily.{u})
    (hgap : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q), Measurable[c.sigma r []] (gap Ω c r.1))
    (hpos : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (x : RootIdx c.Θ c.Q), ∀ᵐ ω ∂c.P, ω ∈ RootCv.coverEvent c (x, 0) → 0 < gap Ω c x ω)
    (hGeometry : RootGeometryAStatement (RootCv.withScaledCover RootJ32.constructionFamily.{u} gap))
    (hNear : GW2Sdi.RetainedNearModelsLossyStatement (RootCv.withScaledCover RootJ32.constructionFamily.{u} gap))
    (hSlow : RetainedSlowComparisonsStatement (RootCv.withScaledCover RootJ32.constructionFamily.{u} gap))
    (hN : SB.Lv.SB2EntranceK2NStatement.{u})
    (hgeo : SB.Lk.SB2LowerRelWalkStatement.{u}) (hcond : SB.Lk.SB2LowerRelStageCondStatement.{u}) :
    Wire.Theorem14Statement.{u} :=
  theorem14Statement_scaled_A_lossy RootJ32.constructionFamily gap hgap hpos hGeometry hNear hSlow hN hgeo hcond

end InteractingSLE.Theorem14.GW2TipSystem.Gm
