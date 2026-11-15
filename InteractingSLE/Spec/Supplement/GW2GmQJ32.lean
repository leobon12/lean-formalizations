/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2GmQTop
import InteractingSLE.Spec.Supplement.GW2GmQGateAe
import InteractingSLE.Spec.Supplement.GW2GmJ32RegT
import InteractingSLE.Spec.Supplement.GW2GmJ32Geom

/-!
# J32's geometry (decision D2): all seven fields, and the J32 top without a geometry binder

Packet PROVE-GW2-GEOM2 (round 5).

* **`RootJ32.observation_alive`**: J32's observation on alive histories agrees almost surely with a function retained
  by the next history (the gated next readers `nextX`, `nextTip` on the retained gate `nextGate`);
* **`RootJ32.experimentGeometryA`**, **`RootJ32.rootGeometryAStatement`**: `RootGeometryAStatement` for J32, from
  Theorem 1.3 (band, reach, record read, clock: round 2; regularity: round 4; observation: here);
* `RootJ32.rootGeometryAStatement_withScaledCover`: the same on every scaled cover;
* **`theorem14Statement_J32_scaled_lossy_geom`**: Theorem 1.4 with J32 on the scaled cover and the lossy near binder,
  with the geometry binder discharged.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootJ32

open Exist Staged StagedLaw Restart GW2Schedule GW2Tip RootC24 Gm

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **J32's observation on alive histories** is retained by the next history up to a null set. -/
theorem observation_alive (h13 : Theorem13Statement.{u}) (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (q q' : c.Q) (hqq' : q ≤ q') :
    ∃ g : Ω → ℝ × ℂ, Measurable[c.sigma r (((experiment c r).data.ang a, q') :: l)] g ∧
      ∀ᵐ ω ∂c.P, ω ∈ (experiment c r).data.alive ((construction c).G r) l →
        (experiment c r).data.observation l a q ω = g ω := by
  refine exists_observation_alive_of_gate h13 c r l a hqq' (measurableSet_nextGate c r l a q q') ?_
  filter_upwards [ae_mem_nextGate_iff h13 c r] with ω h halive
  exact h l a q q' (alive_spec c r l ω halive).2.2 hqq'

/-- **J32's geometry** (decision D2): all seven fields of `Gm.ExperimentGeometryA`. -/
theorem experimentGeometryA (h13 : Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) :
    ExperimentGeometryA c r ((construction c).G r) (experiment c r) where
  band_open := experiment_band_open c r
  observation := observation_alive h13 c r
  regularity := RootJ32.regularity h13 c r
  reach_measurable := experiment_reach_measurable c r
  reach_identification := reach_identification h13 c r
  record_read := experiment_record_read c r
  clock_spec := clock_spec h13 c r

end InteractingSLE.Theorem14.GW2TipSystem.RootJ32

namespace InteractingSLE.Theorem14.GW2TipSystem.RootJ32

open RootC24 Gm

/-- **`RootGeometryAStatement` for J32**, from Theorem 1.3. -/
theorem rootGeometryAStatement (h13 : Exist.Theorem13Statement.{u}) :
    RootGeometryAStatement constructionFamily.{u} :=
  fun _ _ _ c r => experimentGeometryA h13 c r

/-- J32's geometry on every scaled cover. -/
theorem rootGeometryAStatement_withScaledCover (h13 : Exist.Theorem13Statement.{u})
    (gap : RootCv.GapFamily.{u}) :
    RootGeometryAStatement (RootCv.withScaledCover constructionFamily.{u} gap) :=
  Gm.rootGeometryAStatement_withScaledCover gap
    (by rw [withCover_constructionFamily]; exact rootGeometryAStatement h13)

end InteractingSLE.Theorem14.GW2TipSystem.RootJ32

namespace InteractingSLE.Theorem14.GW2TipSystem.Gm

open RootC24 GW2Sdj

/-- **Theorem 1.4 with J32 on the scaled cover and the lossy near binder, geometry discharged**: the successor of
`GW2Sdk.theorem14Statement_J32_scaled_lossy` without its `hGeometry` binder (J32's geometry is proved from the
fibre leaf's Theorem 1.3). -/
theorem theorem14Statement_J32_scaled_lossy_geom (gap : RootCv.GapFamily.{u})
    (hgap : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (r : ScaledRootIdx c.Θ c.Q), Measurable[c.sigma r []] (gap Ω c r.1))
    (hpos : ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω)
      (x : RootIdx c.Θ c.Q), ∀ᵐ ω ∂c.P, ω ∈ RootCv.coverEvent c (x, 0) → 0 < gap Ω c x ω)
    (hNear : GW2Sdi.RetainedNearModelsLossyStatement (RootCv.withScaledCover RootJ32.constructionFamily.{u} gap))
    (hSlow : RetainedSlowComparisonsStatement (RootCv.withScaledCover RootJ32.constructionFamily.{u} gap))
    (hN : SB.Lv.SB2EntranceK2NStatement.{u})
    (hgeo : SB.Lk.SB2LowerRelWalkStatement.{u}) (hcond : SB.Lk.SB2LowerRelStageCondStatement.{u}) :
    Wire.Theorem14Statement.{u} :=
  theorem14Statement_J32_scaled_lossy_A gap hgap hpos
    (RootJ32.rootGeometryAStatement_withScaledCover Sec5.Aux61Cpt.theorem13Statement_of_cptCover.{u} gap)
    hNear hSlow hN hgeo hcond

end InteractingSLE.Theorem14.GW2TipSystem.Gm
