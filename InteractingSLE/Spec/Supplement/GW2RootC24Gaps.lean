/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootC24Data

/-!
# Precisely named open inputs to the full GW2 root-test assembly

Packet PROVE-T14-GW2ROOT2. These assertions are unproved mathematical
inputs, explicitly authorized by the current orchestrator order. They
are not providers for the source theorem. Probability estimates, the
retained kernel construction and the unit conclusion are excluded: the
landed results prove them from the inputs stated here. Following FABLE's
route, both model inputs are one-sided event comparisons; neither a
stopped-kernel construction nor equality of complete model laws is required.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootC24

open Exist Staged StagedLaw Restart LQGMetric RootK3

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- The remaining actual geometry for the supplied experiment. In
particular, observations are gated actual observations, and the capacity
input concerns the literal exceptional branches, not an a.e. version. -/
structure ExperimentGeometry (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (G : Set Ω) (e : Experiment c r) : Prop where
  band_open : ∀ l a, IsOpen (e.data.I l a)
  observation : ∀ l a (q q' : c.Q), q ≤ q' →
    Measurable[c.sigma r ((e.data.ang a, q') :: l)] (e.data.observation l a q)
  capacity : ∀ xs, SchedAdm c.b c.jumps c.Θ c.Q (κ := c.κ)
      (rootPt r.1) (rootEntry r.1) xs →
    RootC11.MeasurableCapacityGeometry (fun ω =>
      prefixImage c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h (regW c.s c.W c.ζ) c.s
        (rootPt r.1) (schedOf (rootEntry r.1) xs) ω)
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

/-- Open root initialization and cover, with the exact initial retained sigma algebra. -/
def RootCoverStatement (D : ConstructionFamily.{u}) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω] (c : SourceData Ω),
    (∀ᵐ ω ∂c.P, c.α ω c.s ∈ H → ∃ r, ω ∈ (D Ω c).G r) ∧
      ∀ r, MeasurableSet[c.sigma r []] ((D Ω c).G r)

/-- Open physical experiment geometry for the supplied choices, without any
model probability estimate, retained-law assumption, or unit inequality. -/
def RootGeometryStatement (D : ConstructionFamily.{u}) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q),
    ExperimentGeometry c r ((D Ω c).G r) ((D Ω c).experiment r)

/-- Open near-extreme comparison under the full retained kernel.
Only one-sided model-family domination is assumed; the
arbitrarily high crossing probability is derived by the landed TIP11 result. -/
def RetainedNearModelsStatement (D : ConstructionFamily.{u}) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q),
    let d := D Ω c
    let e := d.experiment r
    RootN4.HasNearCrossingModels.{u} c.κ c.P (e.data.alive (d.G r))
      (fun l a ω => e.retained.kernel l a ω (e.data.reach l a))

/-- Open one-sided slow-event comparison at the required even depths.
The finite-force window probability is bounded by the actual conditional
slow-event probability. Lemma 5.10 supplies the positive uniform constant. -/
def RetainedSlowComparisonsStatement (D : ConstructionFamily.{u}) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q),
    let d := D Ω c
    let e := d.experiment r
    RootS5.HasSlowComparisonModels.{u} c.κ e.driftBound
      (Icc (-Sec5.angleWeightBound c.κ) (Sec5.angleWeightBound c.κ)) c.P
      (e.data.alive (d.G r)) List.length
      (fun l a ω => e.retained.kernel l a ω RootV7.slowSet)

end InteractingSLE.Theorem14.GW2TipSystem.RootC24
