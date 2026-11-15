/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SwcAssembly

/-!
# The successor geometry statement (ruling R111)

Packet PROVE-GW2-GEOM2. `Swc.ExperimentGeometryU` (C24's `ExperimentGeometry` without `capacity`) has two fields
that are too strong for the actual constructions (handoff round 2, F1–F2):

* `regularity` quantifies over every sample with `S < F`; off alive histories the stage driver may start
  above the band, so `X(S) ∉ I`. Its consumer (`TestCross.ae_exists_candidate_probability`) only uses it under
  conditional laws at alive points.
* `observation` asks for exact measurability in the retained σ-algebra; the actual gated observation is only
  measurable up to a null set (a piece dying before its cap without a left limit).

`ExperimentGeometryV` replaces them by
* `regularity` on alive histories: `∀ᵐ ω, ω ∈ alive G l → S < F → …`;
* `observation` up to null sets: for `q ≤ q'` the gated observation agrees almost surely with a function
  measurable in `c.sigma r ((ang a, q') :: l)` (as R58).

The other five fields are verbatim. `Swc.ExperimentGeometryU.toV` shows the old form implies the new one, so nothing
is strengthened.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.Gm

open GW2Schedule Exist Staged StagedLaw Restart LQGMetric RootC24 RootK3

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **The successor experiment geometry** (ruling R111): `Swc.ExperimentGeometryU` with `regularity` on alive
histories and `observation` measurable up to null sets. -/
structure ExperimentGeometryV (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (G : Set Ω) (e : Experiment c r) : Prop where
  band_open : ∀ l a, IsOpen (e.data.I l a)
  observation : ∀ l a (q q' : c.Q), q ≤ q' → ∃ g : Ω → ℝ × ℂ,
    Measurable[c.sigma r ((e.data.ang a, q') :: l)] g ∧ e.data.observation l a q =ᵐ[c.P] g
  regularity : ∀ l a, ∀ᵐ ω ∂c.P, ω ∈ e.data.alive G l → e.data.S l a ω < e.data.F l a ω →
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
/-- The old geometry implies the successor geometry. -/
theorem _root_.InteractingSLE.Theorem14.GW2TipSystem.Swc.ExperimentGeometryU.toV
    {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q} {G : Set Ω} {e : Experiment c r}
    (hg : Swc.ExperimentGeometryU c r G e) : ExperimentGeometryV c r G e :=
  ⟨hg.band_open, fun l a q q' hqq' => ⟨_, hg.observation l a q q' hqq', EventuallyEq.rfl⟩,
    fun l a => (hg.regularity l a).mono fun _ h _ => h, hg.reach_measurable,
    hg.reach_identification, hg.record_read, hg.clock_spec⟩

end InteractingSLE.Theorem14.GW2TipSystem.Gm

namespace InteractingSLE.Theorem14.GW2TipSystem.Gm

open RootC24

/-- **The successor root geometry statement** (ruling R111). -/
def RootGeometryVStatement (D : ConstructionFamily.{u}) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q),
    ExperimentGeometryV c r ((D Ω c).G r) ((D Ω c).experiment r)

theorem rootGeometryVStatement_of_rootGeometryUStatement {D : ConstructionFamily.{u}}
    (hGeometry : Swc.RootGeometryUStatement D) : RootGeometryVStatement D :=
  fun Ω _ _ c r => (hGeometry Ω c r).toV

end InteractingSLE.Theorem14.GW2TipSystem.Gm
