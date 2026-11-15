/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SwcUnit
import InteractingSLE.Spec.Wire.T14Asm6
import InteractingSLE.Spec.Sec5.Aux61CptThm

/-!
# GW2's root-test assembly without literal capacity measurability

Packet PROVE-GW2-SWITCH. `RootC24.ExperimentGeometry` has eight fields. Its field `capacity` does not
mention the experiment: it asks, for every admissible schedule, for Borel measurability at EVERY
sample of the attached/preconnected event and of the filling of the canonical prefix image (the
literal exceptional branch of `capOf`). The assembly uses it only to make the literal unit events
`TestEvents.capacityUnit capR` measurable. With ROOT2's observable unit events (`RootF27.unitEvent`,
`GW2SwcUnit`) that requirement disappears.

* `ExperimentGeometryU`: the seven experiment fields of `RootC24.ExperimentGeometry` (all but
  `capacity`), verbatim; `RootC24.ExperimentGeometry.toU`;
* `RootGeometryUStatement`, `rootGeometryUStatement_of_rootGeometryStatement`;
* `ExperimentGeometryU.exists_testClaims`, **`gw2RootTestStatement_of_oneSided_comparisons_unitEvent`**:
  `RootC24.gw2RootTestStatement_of_oneSided_comparisons` with `RootGeometryUStatement`;
* `gw2RootTestStatement_of_cover_unitEvent`, `gw2RootTestStatement_of_scaledCover_unitEvent`: COVER's
  cover discharged (as `RootCv.gw2RootTestStatement_of_cover` / `_of_scaledCover`);
* **`theorem14Statement_unscaled_unitEvent`**, `theorem14Statement_scaled_unitEvent`: Theorem 1.4's
  statement as `Wire.theorem14Statement_assembled6_covers_unscaled` / `_covers`, with
  `RootGeometryUStatement` and with Theorems 1.2–1.3 from the proved fibre leaf (no `hDy` binders).

All results are conditional helpers with distinct names; no frozen declaration changes.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.Swc

open GW2Schedule Exist Staged StagedLaw Restart LQGMetric RootC24 RootK3

section Geometry

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **The experiment geometry without the capacity field**: the seven fields of
`RootC24.ExperimentGeometry` that concern the supplied experiment, verbatim. -/
structure ExperimentGeometryU (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (G : Set Ω) (e : Experiment c r) : Prop where
  band_open : ∀ l a, IsOpen (e.data.I l a)
  observation : ∀ l a (q q' : c.Q), q ≤ q' →
    Measurable[c.sigma r ((e.data.ang a, q') :: l)] (e.data.observation l a q)
  regularity : ∀ l a, ∀ᵐ ω ∂c.P, e.data.S l a ω < e.data.F l a ω →
    0 ≤ e.data.S l a ω ∧ ContinuousAt (e.data.X l a ω) (e.data.S l a ω) ∧
    e.data.X l a ω (e.data.S l a ω) ∈ e.data.I l a ∧
    ContinuousOn (e.data.γ l a ω) (Ioo (e.data.S l a ω) (e.data.F l a ω)) ∧
    volume {t | t ∈ Ioo (e.data.S l a ω) (e.data.F l a ω) ∧
      e.data.γ l a ω t ∉ H} = 0
  reach_measurable : ∀ l a, MeasurableSet (e.data.reach l a)
  reach_identification : ∀ l a, e.data.sample l a ⁻¹' e.data.reach l a =ᵐ[c.P]
    {ω | e.data.S l a ω < e.data.F l a ω}
  record_read : ∀ l a, ∀ᵐ ω ∂c.P, ω ∈ e.data.alive G l →
    ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < (e.data.sample l a ω).1 →
      (e.data.sample l a ω).2 q = e.Y l a ω q
  clock_spec : ∀ l a, ∀ᵐ ω ∂c.P, ω ∈ e.data.alive G l → ∀ q : c.Q,
    ω ∈ e.data.tests l a q →
      ContinuousAt (e.Y l a ω) (e.clock l a q ω) ∧
      (e.clock l a q ω : ℝ≥0∞) < (e.data.sample l a ω).1 ∧
      7 / 4 < e.Y l a ω (e.clock l a q ω) ∧
      capR c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s r l ω +
          e.clock l a q ω ≤
        capR c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s r
          ((e.data.ang a, q) :: l) ω

omit [StandardBorelSpace Ω] in
/-- C24's geometry gives the geometry without the capacity field. -/
theorem _root_.InteractingSLE.Theorem14.GW2TipSystem.RootC24.ExperimentGeometry.toU
    {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q} {G : Set Ω} {e : Experiment c r}
    (hg : ExperimentGeometry c r G e) : ExperimentGeometryU c r G e :=
  ⟨hg.band_open, hg.observation, hg.regularity, hg.reach_measurable, hg.reach_identification,
    hg.record_read, hg.clock_spec⟩

/-- **All per-root claims from the geometry without the capacity field**, with ROOT2's observable
unit events (as `RootC24.ExperimentGeometry.exists_testClaims`). -/
theorem ExperimentGeometryU.exists_testClaims {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q}
    {G : Set Ω} {e : Experiment c r}
    (hg : ExperimentGeometryU c r G e) (h13 : Theorem13Statement.{u})
    (hG : MeasurableSet[c.sigma r []] G)
    (hNear : RootN4.HasNearCrossingModels.{u} c.κ c.P (e.data.alive G)
      (fun l a ω => e.retained.kernel l a ω (e.data.reach l a)))
    (hSlow : RootS5.HasSlowComparisonModels.{u} c.κ e.driftBound
      (Icc (-Sec5.angleWeightBound c.κ) (Sec5.angleWeightBound c.κ)) c.P
      (e.data.alive G) List.length
      (fun l a ω => e.retained.kernel l a ω RootV7.slowSet)) :
    ∃ p₀ : ℝ, TestClaims c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s c.P r G
      (e.data.alive G) e.data.ang e.data.tests (RootF27.unitEvent c r) p₀ := by
  have hJ2 : Icc (-Sec5.angleWeightBound c.κ) (Sec5.angleWeightBound c.κ) ⊆
      Ioi (-2) := by
    intro x hx
    exact (neg_lt_neg (Sec5.angleWeightBound_lt_two c.hκ)).trans_le hx.1
  obtain ⟨p₀, hp₀, hp₀1, hModelSlow⟩ := hSlow.exists_modelSlow c.hκ isCompact_Icc hJ2
  let d' : StageModelData Ω c.Θ c.Q RootV7.DriverRecord (c.sigma r) :=
    { e.retained with p₀ := p₀ }
  have hUnit := RootV7.ae_unit_of_record_clock (d := d') (fun _ _ => rfl)
    e.Y e.clock hg.record_read hg.clock_spec
  exact ⟨p₀, testClaims_of_nearModels_unitEvent (d := d') h13 c r hNear hG hg.band_open
    hg.observation hg.regularity e.sampleMeas hg.reach_measurable
    (fun _ _ => RootV7.measurableSet_slowSet)
    (fun _ _ => Eventually.of_forall fun _ _ => rfl)
    hg.reach_identification hp₀ hp₀1 hModelSlow hUnit⟩

end Geometry

/-- **The open physical experiment geometry without the capacity field**, for a construction family
(`RootC24.RootGeometryStatement` without `ExperimentGeometry.capacity`). -/
def RootGeometryUStatement (D : ConstructionFamily.{u}) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q),
    ExperimentGeometryU c r ((D Ω c).G r) ((D Ω c).experiment r)

theorem rootGeometryUStatement_of_rootGeometryStatement {D : ConstructionFamily.{u}}
    (hGeometry : RootGeometryStatement D) : RootGeometryUStatement D :=
  fun Ω _ _ c r => (hGeometry Ω c r).toU

/-- **The complete root-test statement without literal capacity measurability**: as
`RootC24.gw2RootTestStatement_of_oneSided_comparisons`, with `RootGeometryUStatement`. -/
theorem gw2RootTestStatement_of_oneSided_comparisons_unitEvent
    (h13 : Theorem13Statement.{u}) (D : ConstructionFamily.{u})
    (hCover : RootCoverStatement D) (hGeometry : RootGeometryUStatement D)
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
  obtain ⟨p₀, hp₀⟩ := (hGeometry Ω c r).exists_testClaims h13 (hG r)
    (hNear Ω c r) (hSlow Ω c r)
  exact ⟨e.data.alive ((D Ω c).G r), e.data.ang, e.data.tests,
    RootF27.unitEvent c r, p₀, hp₀⟩

/-- **The root-test assembly with COVER's unscaled cover and without capacity measurability.** -/
theorem gw2RootTestStatement_of_cover_unitEvent (h13 : Theorem13Statement.{u})
    (h13₀ : Theorem13Statement.{0}) (D : ConstructionFamily.{u})
    (hGeometry : RootGeometryUStatement (RootCv.withCover D))
    (hNear : RetainedNearModelsStatement (RootCv.withCover D))
    (hSlow : RetainedSlowComparisonsStatement (RootCv.withCover D)) :
    GW2RootTestStatement.{u} :=
  gw2RootTestStatement_of_oneSided_comparisons_unitEvent h13 (RootCv.withCover D)
    (RootCv.rootCoverStatement_withCover h13 h13₀ D) hGeometry hNear hSlow

/-- **The root-test assembly with COVER's scaled cover and without capacity measurability.** -/
theorem gw2RootTestStatement_of_scaledCover_unitEvent (h13 : Theorem13Statement.{u})
    (h13₀ : Theorem13Statement.{0}) (D : ConstructionFamily.{u}) (gap : RootCv.GapFamily.{u})
    (hgap : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q), Measurable[c.sigma r []] (gap Ω c r.1))
    (hpos : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (x : RootIdx c.Θ c.Q), ∀ᵐ ω ∂c.P, ω ∈ RootCv.coverEvent c (x, 0) → 0 < gap Ω c x ω)
    (hGeometry : RootGeometryUStatement (RootCv.withScaledCover D gap))
    (hNear : RetainedNearModelsStatement (RootCv.withScaledCover D gap))
    (hSlow : RetainedSlowComparisonsStatement (RootCv.withScaledCover D gap)) :
    GW2RootTestStatement.{u} :=
  gw2RootTestStatement_of_oneSided_comparisons_unitEvent h13 (RootCv.withScaledCover D gap)
    (RootCv.rootCoverStatement_withScaledCover h13 h13₀ D gap hgap hpos) hGeometry hNear hSlow

/-- **Theorem 1.4 (all four clauses), unscaled cover, without capacity measurability**: as
`Wire.theorem14Statement_assembled6_covers_unscaled` with `RootGeometryUStatement` in place of
`RootGeometryStatement`, and with Theorems 1.2–1.3 from the proved fibre leaf (`Aux61Cpt`). The
binders are GW2's construction `D` with its geometry and two one-sided comparisons, SB2DRV's
`SB2EntranceK2NStatement` and SB2LIFT's two halves. -/
theorem theorem14Statement_unscaled_unitEvent (D : ConstructionFamily.{u})
    (hGeometry : RootGeometryUStatement (RootCv.withCover D))
    (hNear : RetainedNearModelsStatement (RootCv.withCover D))
    (hSlow : RetainedSlowComparisonsStatement (RootCv.withCover D))
    (hN : SB.Lv.SB2EntranceK2NStatement.{u})
    (hgeo : SB.Lk.SB2LowerRelWalkStatement.{u}) (hcond : SB.Lk.SB2LowerRelStageCondStatement.{u}) :
    Wire.Theorem14Statement.{u} :=
  Wire.theorem14Statement_assembled6_of_rootTests
    Sec5.Aux61Cpt.theorem12Statement_of_cptCover.{u} Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{u}
    Sec5.Aux61Cpt.theorem12Statement_of_cptCover.{0} Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{0}
    (gw2RootTestStatement_of_cover_unitEvent Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{u}
      Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{0} D hGeometry hNear hSlow)
    hN hgeo hcond Sec5.Aux61Cpt.cptFibreCover.{u} Sec5.Aux61Cpt.cptFibreCover₀

/-- **Theorem 1.4 (all four clauses), scaled cover, without capacity measurability**: as
`Wire.theorem14Statement_assembled6_covers` with `RootGeometryUStatement` and Theorems 1.2–1.3 from
the proved fibre leaf. -/
theorem theorem14Statement_scaled_unitEvent (D : ConstructionFamily.{u})
    (gap : RootCv.GapFamily.{u})
    (hgap : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q), Measurable[c.sigma r []] (gap Ω c r.1))
    (hpos : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (x : RootIdx c.Θ c.Q), ∀ᵐ ω ∂c.P, ω ∈ RootCv.coverEvent c (x, 0) → 0 < gap Ω c x ω)
    (hGeometry : RootGeometryUStatement (RootCv.withScaledCover D gap))
    (hNear : RetainedNearModelsStatement (RootCv.withScaledCover D gap))
    (hSlow : RetainedSlowComparisonsStatement (RootCv.withScaledCover D gap))
    (hN : SB.Lv.SB2EntranceK2NStatement.{u})
    (hgeo : SB.Lk.SB2LowerRelWalkStatement.{u}) (hcond : SB.Lk.SB2LowerRelStageCondStatement.{u}) :
    Wire.Theorem14Statement.{u} :=
  Wire.theorem14Statement_assembled6_of_rootTests
    Sec5.Aux61Cpt.theorem12Statement_of_cptCover.{u} Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{u}
    Sec5.Aux61Cpt.theorem12Statement_of_cptCover.{0} Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{0}
    (gw2RootTestStatement_of_scaledCover_unitEvent Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{u}
      Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{0} D gap hgap hpos hGeometry hNear hSlow)
    hN hgeo hcond Sec5.Aux61Cpt.cptFibreCover.{u} Sec5.Aux61Cpt.cptFibreCover₀

end InteractingSLE.Theorem14.GW2TipSystem.Swc
