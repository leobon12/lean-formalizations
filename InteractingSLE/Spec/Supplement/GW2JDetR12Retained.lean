/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JDetR12Capacity

/-!
# Actual initial buffer facts in every retained-history kernel

The history may contain any finite sequence of switches. All roots are
allowed for the normalized clock and dense cap bounds; the older physical
entry equivalence still applies at the initial zero root.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped ENNReal NNReal

universe u

namespace InteractingSLE.Theorem14.GW2JDetR12

open GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootG28
  GW2TipSystem.RootD25 GW2Schedule GW2Tip Exist Staged StagedLaw

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- The complete observed initial clock is fixed under every retained
kernel, simultaneously at all physical times. -/
theorem ae_conditional_rootClock_eq (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) :
    ∀ᵐ ω₀ ∂c.P, ∀ᵐ ξ ∂condExpKernel c.P (c.sigma r l) ω₀,
      ∀ t : ℝ≥0, normalizedRootClock c r ξ t = normalizedRootClock c r ω₀ t := by
  filter_upwards [ae_conditional_rootRecs_eq c r l] with ω₀ hω₀
  filter_upwards [hω₀] with ξ hξ t
  simp only [normalizedRootClock, hξ]

/-- Every retained kernel preserves the source's strict continuous clock
and exact literal endpoint identity at each COVER root. -/
theorem ae_conditional_normalizedRootClock (h13 : Theorem13Statement.{u})
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) :
    ∀ᵐ ω₀ ∂c.P, ω₀ ∈ RootCv.coverEvent c r →
      ∀ᵐ ξ ∂condExpKernel c.P (c.sigma r l) ω₀,
        let v := (rootEntry r.1).2
        normalizedRootClock c r ξ 0 = 0 ∧
        StrictMonoOn (normalizedRootClock c r ξ) (Icc 0 v) ∧
        ContinuousOn (normalizedRootClock c r ξ) (Icc 0 v) ∧
        (normalizedRootClock c r ξ v : ℝ) =
          capR c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s r [] ξ :=
  ae_conditional_on_cover c r l (ae_cover_normalizedRootClock h13 c r)

/-- The literal initial capacity is fixed by every retained kernel on
COVER, without global measurability of that literal capacity being assumed. -/
theorem ae_conditional_capR_nil_eq (h13 : Theorem13Statement.{u})
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) :
    ∀ᵐ ω₀ ∂c.P, ω₀ ∈ RootCv.coverEvent c r →
      ∀ᵐ ξ ∂condExpKernel c.P (c.sigma r l) ω₀,
        capR c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s r [] ξ =
          capR c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s r [] ω₀ := by
  filter_upwards [ae_cover_normalizedRootClock h13 c r,
    ae_conditional_normalizedRootClock h13 c r l, ae_conditional_rootClock_eq c r l]
    with ω₀ hs hc he hω₀
  filter_upwards [hc hω₀, he] with ξ hξ heq
  rw [← hξ.2.2.2, ← (hs hω₀).2.2.2, heq]

omit [StandardBorelSpace Ω] in
/-- The literal running capacity includes its initial value, at every
sample and after every switched history, even an inadmissible one. -/
theorem capR_nil_le (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (ξ : Ω) :
    capR c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s r [] ξ ≤
      capR c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s r l ξ := by
  induction l with
  | nil => exact le_rfl
  | cons x l ih =>
    refine ih.trans ?_
    unfold capR
    rw [entryList_cons]
    exact mul_le_mul_of_nonneg_left
      (schedCap_le_cons c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h
        (regW c.s c.W c.ζ) c.s c.Θ c.Q (rootPt r.1) (rootEntry r.1)
        ((x.1 : ℝ), (x.2 : ℝ≥0)) (entryList l) ξ) (by positivity)

/-- Every conditional current running capacity exceeds the positive
initial capacity observed at the retained state. -/
theorem ae_conditional_capR_lowerBound (h13 : Theorem13Statement.{u})
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) :
    ∀ᵐ ω₀ ∂c.P, ω₀ ∈ RootCv.coverEvent c r →
      ∀ᵐ ξ ∂condExpKernel c.P (c.sigma r l) ω₀,
        0 < capR c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s r [] ω₀ ∧
          capR c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s r [] ω₀ ≤
            capR c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s r l ξ := by
  filter_upwards [RootI30.ae_cover_capR_pos h13 c r,
    ae_conditional_capR_nil_eq h13 c r l] with ω₀ hp he hω₀
  filter_upwards [he hω₀] with ξ hξ
  exact ⟨hp hω₀, hξ ▸ capR_nil_le c r l ξ⟩

/-- All original-Q buffer capacities are positive and strictly below the
observed literal endpoint, under every full retained-history kernel. -/
theorem ae_conditional_capacityBuffer_bounds (h13 : Theorem13Statement.{u})
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) :
    ∀ᵐ ω₀ ∂c.P, ω₀ ∈ RootCv.coverEvent c r →
      ∀ᵐ ξ ∂condExpKernel c.P (c.sigma r l) ω₀,
        ∀ b : c.Q, (b : ℝ≥0) < (rootEntry r.1).2 →
          0 < normalizedRootClock c r ξ b ∧
            (normalizedRootClock c r ξ b : ℝ) <
              capR c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s r [] ω₀ := by
  have hlocal := ae_conditional_on_cover c r l (ae_cover_capacityBuffer_bounds h13 c r)
  filter_upwards [hlocal, ae_conditional_capR_nil_eq h13 c r l] with ω₀ hb he hω₀
  filter_upwards [hb hω₀, he hω₀] with ξ hξ heq b hbv
  simpa only [heq] using hξ b hbv

/-- Every earlier capacity is exceeded by an original-Q cap inside the
recorded root horizon, under every retained-history kernel. -/
theorem ae_conditional_exists_capacityBuffer (h13 : Theorem13Statement.{u})
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) :
    ∀ᵐ ω₀ ∂c.P, ω₀ ∈ RootCv.coverEvent c r →
      ∀ᵐ ξ ∂condExpKernel c.P (c.sigma r l) ω₀, ∀ u : ℝ≥0,
        (u : ℝ) < capR c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s r [] ω₀ →
        ∃ b : c.Q, 0 < (b : ℝ≥0) ∧ (b : ℝ≥0) < (rootEntry r.1).2 ∧
          u < normalizedRootClock c r ξ b := by
  have hlocal := ae_conditional_on_cover c r l (ae_cover_exists_capacityBuffer h13 c r)
  filter_upwards [hlocal, ae_conditional_capR_nil_eq h13 c r l] with ω₀ hb he hω₀
  filter_upwards [hb hω₀, he hω₀] with ξ hξ heq u hu
  apply hξ u
  rwa [heq]

/-- The actual initial zero-root geometric buffers keep their positive
sample lifetimes and physical entry equivalence after ANY retained history. -/
theorem ae_conditional_initial_bufferedGeometry (h13 : Theorem13Statement.{u})
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))
    (hroot : rootPt r.1 = 0) :
    ∀ᵐ ω₀ ∂c.P, ω₀ ∈ RootCv.coverEvent c r →
      ∀ᵐ ξ ∂condExpKernel c.P (c.sigma r l) ω₀,
        ∀ b : c.Q, (b : ℝ≥0) < (rootEntry r.1).2 → ∀ m : ℕ,
          let p := RootCv.rootRecs c r.1 ξ
          let a : ℝ≥0 := 2 ^ r.2
          let v := (rootEntry r.1).2
          0 < (bufferedSample a c.s v b m p).1 ∧
            (bufferedSample a c.s v b m p ∈ reachSet ↔
              entryPhysical a c.s v p < contactBuffer c.s v b m p) :=
  ae_conditional_on_cover c r l
    (GW2JDetR11.ae_initial_bufferedGeometry_on_cover h13 c r hroot)

/-- A single conditional event fixes every initial buffered sample, even
for all real caps simultaneously. No countable intersection is required. -/
theorem ae_conditional_bufferedSamples_eq (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) :
    ∀ᵐ ω₀ ∂c.P, ∀ᵐ ξ ∂condExpKernel c.P (c.sigma r l) ω₀,
      ∀ b : ℝ≥0, ∀ m : ℕ,
        bufferedSample (2 ^ r.2) c.s (rootEntry r.1).2 b m (RootCv.rootRecs c r.1 ξ) =
          bufferedSample (2 ^ r.2) c.s (rootEntry r.1).2 b m (RootCv.rootRecs c r.1 ω₀) := by
  filter_upwards [ae_conditional_rootRecs_eq c r l] with ω₀ hω₀
  filter_upwards [hω₀] with ξ hξ b m
  rw [hξ]

end InteractingSLE.Theorem14.GW2JDetR12
