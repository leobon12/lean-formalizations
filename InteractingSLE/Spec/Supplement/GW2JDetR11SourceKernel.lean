/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JDetR11SourceLife
import InteractingSLE.Spec.Sec7.Aux122Disint

/-!
# The landed source buffer facts under the literal retained kernel

At the initial zero root, COVER supplies protection. Disintegration over
the actual root sigma algebra preserves positive buffered lifetimes and
the physical-entry interpretation. The recorded sample and its live reads
are exact at every outcome, including exceptional records.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

universe u

namespace InteractingSLE.Theorem14.GW2JDetR11

open GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootG28
  GW2TipSystem.RootD25 GW2Schedule GW2Tip Exist Staged StagedLaw Restart Supp8.GB6

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- Both actual buffer conclusions on COVER, with no new source premise. -/
theorem ae_initial_bufferedGeometry_on_cover (h13 : Theorem13Statement.{u})
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (hroot : rootPt r.1 = 0) :
    ∀ᵐ ω ∂c.P, ω ∈ RootCv.coverEvent c r →
      ∀ b : c.Q, (b : ℝ≥0) < (rootEntry r.1).2 → ∀ m : ℕ,
        let p := RootCv.rootRecs c r.1 ω
        let a : ℝ≥0 := 2 ^ r.2
        let v := (rootEntry r.1).2
        0 < (bufferedSample a c.s v b m p).1 ∧
          (bufferedSample a c.s v b m p ∈ reachSet ↔
            entryPhysical a c.s v p < contactBuffer c.s v b m p) := by
  have hpos := ae_initial_bufferedSample_pos_on_cover h13 c r hroot
  have hentry := ae_initial_buffered_entry_regular h13 c r hroot
  have hcov := RootCv.ae_coverEvent_spec_zero h13 c r hroot
  dsimp only at hentry hcov ⊢
  filter_upwards [hpos, hentry, hcov] with ω hp he hc hω
  intro b hb m
  exact ⟨hp hω b hb m, (he (hc hω).1 (hc hω).2.2 b hb.le m).1⟩

/-- The same proved buffer facts hold almost surely under the exact
initial retained-history kernel at almost every COVER state. -/
theorem ae_conditional_initial_bufferedGeometry (h13 : Theorem13Statement.{u})
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (hroot : rootPt r.1 = 0) :
    ∀ᵐ ω₀ ∂c.P, ω₀ ∈ RootCv.coverEvent c r →
      ∀ᵐ ξ ∂condExpKernel c.P (c.sigma r []) ω₀,
        ∀ b : c.Q, (b : ℝ≥0) < (rootEntry r.1).2 → ∀ m : ℕ,
          let p := RootCv.rootRecs c r.1 ξ
          let a : ℝ≥0 := 2 ^ r.2
          let v := (rootEntry r.1).2
          0 < (bufferedSample a c.s v b m p).1 ∧
            (bufferedSample a c.s v b m p ∈ reachSet ↔
              entryPhysical a c.s v p < contactBuffer c.s v b m p) := by
  have hσ : c.sigma r [] ≤ ‹MeasurableSpace Ω› :=
    stageSigma_le c.hβA.1 c.hh.1 c.hcf c.s _ _
  have hgeom := Sec7.Aux122Disint.ae_ae_condExpKernel hσ
    (ae_initial_bufferedGeometry_on_cover h13 c r hroot)
  have hmem := Sec7.Aux122Disint.ae_ae_condExpKernel_mem (P := c.P) hσ
    (RootCv.measurableSet_coverEvent c r)
  filter_upwards [hgeom, hmem] with ω₀ hg hm hω₀
  filter_upwards [hg, hm hω₀] with ξ hξ hmemξ
  exact hξ hmemξ

omit [StandardBorelSpace Ω] in
/-- The entire actual initial buffered sample is known in the literal
root sigma algebra; no good-event condition is used. -/
theorem measurable_initial_bufferedSample (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (b : ℝ≥0) (m : ℕ) :
    Measurable[c.sigma r []] (fun ξ =>
      bufferedSample (2 ^ r.2) c.s (rootEntry r.1).2 b m (RootCv.rootRecs c r.1 ξ)) :=
  (measurable_bufferedSample _ _ _ _ _).comp (RootCv.measurable_rootRecs c r)

/-- The observed initial buffer is fixed under the retained kernel.
This is a record identity, rather than an SDE assertion about a future piece. -/
theorem ae_conditional_initial_bufferedSample_eq (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (b : ℝ≥0) (m : ℕ) :
    ∀ᵐ ω₀ ∂c.P, ∀ᵐ ξ ∂condExpKernel c.P (c.sigma r []) ω₀,
      bufferedSample (2 ^ r.2) c.s (rootEntry r.1).2 b m (RootCv.rootRecs c r.1 ξ) =
        bufferedSample (2 ^ r.2) c.s (rootEntry r.1).2 b m (RootCv.rootRecs c r.1 ω₀) := by
  exact Sec7.Aux122Disint.ae_ae_condExpKernel_eq
    (stageSigma_le c.hβA.1 c.hh.1 c.hcf c.s _ _)
    (measurable_initial_bufferedSample c r b m)

omit [StandardBorelSpace Ω] in
/-- The exact live read required by the sample clause is already a
pointwise identity of the actual source records. -/
theorem initial_bufferedSample_read (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (b : ℝ≥0) (m : ℕ) (ξ : Ω) {q : ℚ≥0}
    (hq : ((q : ℝ≥0) : ℝ≥0∞) <
      (bufferedSample (2 ^ r.2) c.s (rootEntry r.1).2 b m (RootCv.rootRecs c r.1 ξ)).1) :
    (bufferedSample (2 ^ r.2) c.s (rootEntry r.1).2 b m (RootCv.rootRecs c r.1 ξ)).2 q =
      RootB23.scaledRelativeDriverRead (2 ^ r.2) c.s (rootEntry r.1).2 q
        (RootCv.rootRecs c r.1 ξ) :=
  bufferedSample_read _ _ _ _ _ _ hq

end InteractingSLE.Theorem14.GW2JDetR11
