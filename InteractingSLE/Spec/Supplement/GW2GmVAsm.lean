/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2GmVTest

/-!
# The root-test assembly and Theorem 1.4's top with the successor geometry (ruling R111)

Packet PROVE-GW2-GEOM2. SWITCH's chain (`Swc.gw2RootTestStatement_of_oneSided_comparisons_unitEvent`,
`…_of_cover_unitEvent`, `…_of_scaledCover_unitEvent`, `Swc.theorem14Statement_unscaled_unitEvent`,
`Swc.theorem14Statement_scaled_unitEvent`) with `RootGeometryVStatement` (regularity on alive histories,
observation measurable up to null sets) in place of `Swc.RootGeometryUStatement`. `GW2RootTestStatement` quantifies
its tests and alive events existentially, so the per-root claims are supplied for measurable versions of the tests
(`ExperimentGeometryV.exists_testClaims`); every other binder is unchanged. Since
`rootGeometryVStatement_of_rootGeometryUStatement` holds, the successor tops are weaker in their hypotheses than
SWITCH's.

* `gw2RootTestStatement_of_oneSided_comparisons_V`, `gw2RootTestStatement_of_cover_V`,
  `gw2RootTestStatement_of_scaledCover_V`;
* **`theorem14Statement_unscaled_V`**, **`theorem14Statement_scaled_V`**.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.Gm

open GW2Schedule Exist Staged StagedLaw Restart LQGMetric RootC24 RootK3

/-- **The complete root-test statement without literal capacity measurability**: as
`RootC24.gw2RootTestStatement_of_oneSided_comparisons`, with `RootGeometryVStatement`. -/
theorem gw2RootTestStatement_of_oneSided_comparisons_V
    (h13 : Theorem13Statement.{u}) (D : ConstructionFamily.{u})
    (hCover : RootCoverStatement D) (hGeometry : RootGeometryVStatement D)
    (hNear : RetainedNearModelsStatement D)
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
  obtain ⟨p₀, A, T, hp₀⟩ := (hGeometry Ω c r).exists_testClaims h13 (hG r)
    (hNear Ω c r) (hSlow Ω c r)
  exact ⟨A, e.data.ang, T, RootF27.unitEvent c r, p₀, hp₀⟩

/-- **The root-test assembly with COVER's unscaled cover and without capacity measurability.** -/
theorem gw2RootTestStatement_of_cover_V (h13 : Theorem13Statement.{u})
    (h13₀ : Theorem13Statement.{0}) (D : ConstructionFamily.{u})
    (hGeometry : RootGeometryVStatement (RootCv.withCover D))
    (hNear : RetainedNearModelsStatement (RootCv.withCover D))
    (hSlow : RetainedSlowComparisonsStatement (RootCv.withCover D)) :
    GW2RootTestStatement.{u} :=
  gw2RootTestStatement_of_oneSided_comparisons_V h13 (RootCv.withCover D)
    (RootCv.rootCoverStatement_withCover h13 h13₀ D) hGeometry hNear hSlow

/-- **The root-test assembly with COVER's scaled cover and without capacity measurability.** -/
theorem gw2RootTestStatement_of_scaledCover_V (h13 : Theorem13Statement.{u})
    (h13₀ : Theorem13Statement.{0}) (D : ConstructionFamily.{u}) (gap : RootCv.GapFamily.{u})
    (hgap : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q), Measurable[c.sigma r []] (gap Ω c r.1))
    (hpos : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (x : RootIdx c.Θ c.Q), ∀ᵐ ω ∂c.P, ω ∈ RootCv.coverEvent c (x, 0) → 0 < gap Ω c x ω)
    (hGeometry : RootGeometryVStatement (RootCv.withScaledCover D gap))
    (hNear : RetainedNearModelsStatement (RootCv.withScaledCover D gap))
    (hSlow : RetainedSlowComparisonsStatement (RootCv.withScaledCover D gap)) :
    GW2RootTestStatement.{u} :=
  gw2RootTestStatement_of_oneSided_comparisons_V h13 (RootCv.withScaledCover D gap)
    (RootCv.rootCoverStatement_withScaledCover h13 h13₀ D gap hgap hpos) hGeometry hNear hSlow

/-- **Theorem 1.4 (all four clauses), unscaled cover, without capacity measurability**: as
`Wire.theorem14Statement_assembled6_covers_unscaled` with `RootGeometryVStatement` in place of
`RootGeometryStatement`, and with Theorems 1.2–1.3 from the proved fibre leaf (`Aux61Cpt`). The
binders are GW2's construction `D` with its geometry and two one-sided comparisons, SB2DRV's
`SB2EntranceK2NStatement` and SB2LIFT's two halves. -/
theorem theorem14Statement_unscaled_V (D : ConstructionFamily.{u})
    (hGeometry : RootGeometryVStatement (RootCv.withCover D))
    (hNear : RetainedNearModelsStatement (RootCv.withCover D))
    (hSlow : RetainedSlowComparisonsStatement (RootCv.withCover D))
    (hN : SB.Lv.SB2EntranceK2NStatement.{u})
    (hgeo : SB.Lk.SB2LowerRelWalkStatement.{u}) (hcond : SB.Lk.SB2LowerRelStageCondStatement.{u}) :
    Wire.Theorem14Statement.{u} :=
  Wire.theorem14Statement_assembled6_of_rootTests
    Sec5.Aux61Cpt.theorem12Statement_of_cptCover.{u} Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{u}
    Sec5.Aux61Cpt.theorem12Statement_of_cptCover.{0} Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{0}
    (gw2RootTestStatement_of_cover_V Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{u}
      Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{0} D hGeometry hNear hSlow)
    hN hgeo hcond Sec5.Aux61Cpt.cptFibreCover.{u} Sec5.Aux61Cpt.cptFibreCover₀

/-- **Theorem 1.4 (all four clauses), scaled cover, without capacity measurability**: as
`Wire.theorem14Statement_assembled6_covers` with `RootGeometryVStatement` and Theorems 1.2–1.3 from
the proved fibre leaf. -/
theorem theorem14Statement_scaled_V (D : ConstructionFamily.{u})
    (gap : RootCv.GapFamily.{u})
    (hgap : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q), Measurable[c.sigma r []] (gap Ω c r.1))
    (hpos : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (x : RootIdx c.Θ c.Q), ∀ᵐ ω ∂c.P, ω ∈ RootCv.coverEvent c (x, 0) → 0 < gap Ω c x ω)
    (hGeometry : RootGeometryVStatement (RootCv.withScaledCover D gap))
    (hNear : RetainedNearModelsStatement (RootCv.withScaledCover D gap))
    (hSlow : RetainedSlowComparisonsStatement (RootCv.withScaledCover D gap))
    (hN : SB.Lv.SB2EntranceK2NStatement.{u})
    (hgeo : SB.Lk.SB2LowerRelWalkStatement.{u}) (hcond : SB.Lk.SB2LowerRelStageCondStatement.{u}) :
    Wire.Theorem14Statement.{u} :=
  Wire.theorem14Statement_assembled6_of_rootTests
    Sec5.Aux61Cpt.theorem12Statement_of_cptCover.{u} Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{u}
    Sec5.Aux61Cpt.theorem12Statement_of_cptCover.{0} Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{0}
    (gw2RootTestStatement_of_scaledCover_V Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{u}
      Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{0} D gap hgap hpos hGeometry hNear hSlow)
    hN hgeo hcond Sec5.Aux61Cpt.cptFibreCover.{u} Sec5.Aux61Cpt.cptFibreCover₀

end InteractingSLE.Theorem14.GW2TipSystem.Gm
