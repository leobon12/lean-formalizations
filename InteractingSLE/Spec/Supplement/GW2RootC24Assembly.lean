/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootC24Gaps

/-!
# The complete GW2 root-test statement from the named open inputs

Packet PROVE-T14-GW2ROOT2. This is the conditional full `hTests` requested
by the orchestrator. All crossing/slow estimates, retained-law transfers,
the common positive constant and the unit conclusion use landed proofs.
Following FABLE's handoff, the four open inputs concern the root cover,
actual geometry and two one-sided event comparisons. The stopped-kernel
construction and complete finite-force law equality are not inputs.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootC24

open Exist Staged StagedLaw Restart LQGMetric RootK3

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
  {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q} {G : Set Ω} {e : Experiment c r}

/-- All per-root claims follow from the stated remaining geometry and
one-sided finite-force comparisons. Capacity measurability, the conditional
kernel, estimates, probability constant and unit clause are derived. -/
theorem ExperimentGeometry.exists_testClaims
    (hg : ExperimentGeometry c r G e) (h13 : Theorem13Statement.{u})
    (hG : MeasurableSet[c.sigma r []] G)
    (hNear : RootN4.HasNearCrossingModels.{u} c.κ c.P (e.data.alive G)
      (fun l a ω => e.retained.kernel l a ω (e.data.reach l a)))
    (hSlow : RootS5.HasSlowComparisonModels.{u} c.κ e.driftBound
      (Icc (-Sec5.angleWeightBound c.κ) (Sec5.angleWeightBound c.κ)) c.P
      (e.data.alive G) List.length
      (fun l a ω => e.retained.kernel l a ω RootV7.slowSet)) :
    ∃ p₀ : ℝ, TestClaims c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s c.P r G
      (e.data.alive G) e.data.ang e.data.tests
      (TestEvents.capacityUnit
        (capR c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s r)) p₀ := by
  have hJ2 : Icc (-Sec5.angleWeightBound c.κ) (Sec5.angleWeightBound c.κ) ⊆
      Ioi (-2) := by
    intro x hx
    exact (neg_lt_neg (Sec5.angleWeightBound_lt_two c.hκ)).trans_le hx.1
  obtain ⟨p₀, hp₀, hp₀1, hModelSlow⟩ := hSlow.exists_modelSlow c.hκ isCompact_Icc hJ2
  let d' : StageModelData Ω c.Θ c.Q RootV7.DriverRecord (c.sigma r) :=
    { e.retained with p₀ := p₀ }
  have hUnit := RootV7.ae_unit_of_record_clock (d := d') (fun _ _ => rfl)
    e.Y e.clock hg.record_read hg.clock_spec
  refine ⟨p₀, ?_⟩
  exact RootN4.testClaims_of_nearModels (d := d') h13 c.hκ4 c.hβA.1 c.hh.1 c.hcf c.hQd
    hNear hG hg.band_open hg.observation
    (fun l => RootC11.measurable_capR_of_geometry c.hκ c.h12p c.βA c.b c.jumps c.c₀
      c.h c.W c.s c.Θ c.Q c.ζ r hg.capacity l)
    hg.regularity e.sampleMeas hg.reach_measurable
    (fun _ _ => RootV7.measurableSet_slowSet)
    (fun _ _ => Eventually.of_forall fun _ _ => rfl)
    hg.reach_identification hp₀ hp₀1 hModelSlow hUnit

/-- The exact complete root-test statement, with the open cover,
experiment geometry and two one-sided event comparisons named separately.
This theorem does not assume the complete root-model statement or `hTests`. -/
theorem gw2RootTestStatement_of_oneSided_comparisons
    (h13 : Theorem13Statement.{u}) (D : ConstructionFamily.{u})
    (hCover : RootCoverStatement D) (hGeometry : RootGeometryStatement D)
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
    TestEvents.capacityUnit (capR hκ h12p βA b jumps c₀ h W ζ s r), p₀, hp₀⟩

end InteractingSLE.Theorem14.GW2TipSystem.RootC24
