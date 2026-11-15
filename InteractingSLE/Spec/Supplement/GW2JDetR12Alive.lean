/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JDetR12Retained
import InteractingSLE.Spec.Supplement.GW2CvStatement

/-!
# The source buffer facts on the construction's actual alive events

For every underlying construction, the landed scaled-cover construction
has its alive events inside COVER. The all-history source facts therefore
apply directly with the same alive binder as the two comparison properties.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

universe u

namespace InteractingSLE.Theorem14.GW2JDetR12

open GW2TipSystem GW2TipSystem.RootC24 GW2Schedule GW2Tip Exist Staged StagedLaw

/-- Each alive history retains membership in its initial event. -/
theorem aliveTests_subset {Ω Θ Q : Type*} (G : Set Ω) (ang : ℕ → Θ)
    (T : List (Θ × Q) → ℕ → Q → Set Ω) (l : List (Θ × Q)) :
    TestEvents.aliveTests G ang T l ⊆ G := by
  induction l with
  | nil => exact Subset.rfl
  | cons x l ih => exact inter_subset_left.trans ih

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

omit [StandardBorelSpace Ω] in
/-- Every alive state of a scaled-cover experiment is a COVER state. -/
theorem alive_scaledCover_subset (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (e : Experiment c r) (gap : RootIdx c.Θ c.Q → Ω → ℝ)
    (l : List (EntryIdx c.Θ c.Q)) :
    e.data.alive (RootCv.scaledCoverEvent c gap r) l ⊆ RootCv.coverEvent c r :=
  (aliveTests_subset _ _ _ l).trans (RootCv.scaledCoverEvent_subset c gap r)

/-- The actual scaled-cover construction has a positive observed initial
capacity below every conditional current running capacity, at all histories. -/
theorem ae_conditional_capR_lowerBound_on_alive
    (h13 : Theorem13Statement.{u}) (D : ConstructionFamily.{u}) (gap : RootCv.GapFamily.{u})
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) :
    ∀ᵐ ω₀ ∂c.P,
      ω₀ ∈ (((RootCv.withScaledCover D gap) Ω c).experiment r).data.alive
        (((RootCv.withScaledCover D gap) Ω c).G r) l →
      ∀ᵐ ξ ∂condExpKernel c.P (c.sigma r l) ω₀,
        0 < capR c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s r [] ω₀ ∧
          capR c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s r [] ω₀ ≤
            capR c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s r l ξ := by
  filter_upwards [ae_conditional_capR_lowerBound h13 c r l] with ω₀ hω₀ halive
  exact hω₀ (alive_scaledCover_subset c r ((D Ω c).experiment r) (gap Ω c) l halive)

/-- At every actual alive state, original-Q buffers are conditionally
positive and exhaust the observed initial capacity. This asserts only facts
about the initial observed prefix, not the unconstructed future sample. -/
theorem ae_conditional_capacityBuffers_on_alive
    (h13 : Theorem13Statement.{u}) (D : ConstructionFamily.{u}) (gap : RootCv.GapFamily.{u})
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) :
    ∀ᵐ ω₀ ∂c.P,
      ω₀ ∈ (((RootCv.withScaledCover D gap) Ω c).experiment r).data.alive
        (((RootCv.withScaledCover D gap) Ω c).G r) l →
      ∀ᵐ ξ ∂condExpKernel c.P (c.sigma r l) ω₀,
        (∀ b : c.Q, (b : ℝ≥0) < (rootEntry r.1).2 →
          0 < normalizedRootClock c r ξ b ∧
            (normalizedRootClock c r ξ b : ℝ) <
              capR c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s r [] ω₀) ∧
        ∀ u : ℝ≥0,
          (u : ℝ) < capR c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s r [] ω₀ →
          ∃ b : c.Q, 0 < (b : ℝ≥0) ∧ (b : ℝ≥0) < (rootEntry r.1).2 ∧
            u < normalizedRootClock c r ξ b := by
  filter_upwards [ae_conditional_capacityBuffer_bounds h13 c r l,
    ae_conditional_exists_capacityBuffer h13 c r l] with ω₀ hb he halive
  have hcover := alive_scaledCover_subset c r ((D Ω c).experiment r) (gap Ω c) l halive
  exact (hb hcover).and (he hcover)

end InteractingSLE.Theorem14.GW2JDetR12
