/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2GmVStmt
import InteractingSLE.Spec.Supplement.GW2CvStatement

/-!
# The successor geometry statement with observation on alive histories (decision D2)

Packet PROVE-GW2-GEOM2 (round 5; `planning/reviews/DECISIONS-FABLE-1.md`, D2). `ExperimentGeometryV`'s `observation`
quantifies over all histories; on histories that are not time-ordered (never alive) J32's readers are not causal.
**`ExperimentGeometryA`** is `ExperimentGeometryV` with `observation` required almost surely on the alive histories
only (as R111 did for `regularity`); the other six fields are verbatim.

* `ExperimentGeometryV.toA` (the old form implies the new one, so nothing is strengthened);
* `RootGeometryAStatement`, `rootGeometryAStatement_of_rootGeometryVStatement`;
* `TestEvents.aliveTests_mono`, `ExperimentGeometryA.mono` (every field mentioning `G` does so through `alive G l`);
* **`rootGeometryAStatement_withScaledCover`**: geometry for `withCover D` gives geometry for `withScaledCover D gap`.
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

/-- **The successor experiment geometry** (decision D2): `ExperimentGeometryV` with `observation` measurable up to
null sets on the alive histories. -/
structure ExperimentGeometryA (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (G : Set Ω) (e : Experiment c r) : Prop where
  band_open : ∀ l a, IsOpen (e.data.I l a)
  observation : ∀ l a (q q' : c.Q), q ≤ q' → ∃ g : Ω → ℝ × ℂ,
    Measurable[c.sigma r ((e.data.ang a, q') :: l)] g ∧
    ∀ᵐ ω ∂c.P, ω ∈ e.data.alive G l → e.data.observation l a q ω = g ω
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
/-- The R111 geometry implies the D2 geometry. -/
theorem ExperimentGeometryV.toA {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q} {G : Set Ω}
    {e : Experiment c r} (hg : ExperimentGeometryV c r G e) : ExperimentGeometryA c r G e :=
  ⟨hg.band_open, fun l a q q' hqq' => by
      obtain ⟨g, hgm, hgeq⟩ := hg.observation l a q q' hqq'
      exact ⟨g, hgm, hgeq.mono fun _ h _ => h⟩,
    hg.regularity, hg.reach_measurable, hg.reach_identification, hg.record_read, hg.clock_spec⟩

/-- Alive events grow with the initial event. -/
theorem _root_.InteractingSLE.Theorem14.GW2TipSystem.TestEvents.aliveTests_mono {Ω' Θ : Type*}
    {Q : Type*} {G G' : Set Ω'} (hGG' : G ⊆ G') (ang : ℕ → Θ) (T : List (Θ × Q) → ℕ → Q → Set Ω') :
    ∀ l, TestEvents.aliveTests G ang T l ⊆ TestEvents.aliveTests G' ang T l
  | [] => hGG'
  | _ :: l => inter_subset_inter_left _ (TestEvents.aliveTests_mono hGG' ang T l)

omit [StandardBorelSpace Ω] in
/-- **The geometry passes to a smaller initial event.** -/
theorem ExperimentGeometryA.mono {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q} {G G' : Set Ω}
    {e : Experiment c r} (hg : ExperimentGeometryA c r G' e) (hGG' : G ⊆ G') :
    ExperimentGeometryA c r G e := by
  have hal : ∀ l, e.data.alive G l ⊆ e.data.alive G' l :=
    TestEvents.aliveTests_mono hGG' e.data.ang e.data.tests
  refine ⟨hg.band_open, fun l a q q' hqq' => ?_, fun l a => ?_, hg.reach_measurable,
    hg.reach_identification, fun l a => ?_, fun l a => ?_⟩
  · obtain ⟨g, hgm, hgeq⟩ := hg.observation l a q q' hqq'
    exact ⟨g, hgm, hgeq.mono fun _ h hω => h (hal l hω)⟩
  · exact (hg.regularity l a).mono fun _ h hω => h (hal l hω)
  · exact (hg.record_read l a).mono fun _ h hω => h (hal l hω)
  · exact (hg.clock_spec l a).mono fun _ h hω => h (hal l hω)

end InteractingSLE.Theorem14.GW2TipSystem.Gm

namespace InteractingSLE.Theorem14.GW2TipSystem.Gm

open RootC24

/-- **The successor root geometry statement** (decision D2). -/
def RootGeometryAStatement (D : ConstructionFamily.{u}) : Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q),
    ExperimentGeometryA c r ((D Ω c).G r) ((D Ω c).experiment r)

theorem rootGeometryAStatement_of_rootGeometryVStatement {D : ConstructionFamily.{u}}
    (hGeometry : RootGeometryVStatement D) : RootGeometryAStatement D :=
  fun Ω _ _ c r => (hGeometry Ω c r).toA

/-- **Geometry on the cover gives geometry on the scaled cover**: the two constructions share the experiment, and
the scaled cover is smaller. -/
theorem rootGeometryAStatement_withScaledCover {D : ConstructionFamily.{u}} (gap : RootCv.GapFamily.{u})
    (hGeometry : RootGeometryAStatement (RootCv.withCover D)) :
    RootGeometryAStatement (RootCv.withScaledCover D gap) :=
  fun Ω _ _ c r => (hGeometry Ω c r).mono (RootCv.scaledCoverEvent_subset c (gap Ω c) r)

end InteractingSLE.Theorem14.GW2TipSystem.Gm
