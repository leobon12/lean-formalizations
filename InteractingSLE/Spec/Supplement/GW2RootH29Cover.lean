/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootH29Capacity
import InteractingSLE.Spec.Supplement.GW2CvProps

/-!
# The low-arc cover supplies switched capacity geometry and readers

Packet PROVE-T14-GW2ROOT2. Discharge the untouched-arc and nonnegative
root premises from the actual COVER event. The resulting countable
family reads all admissible switched capacities on a common conull set.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H)

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootH29

open GW2Schedule GW2Tip Exist Staged StagedLaw Restart LQGMetric RootC24 Supp8.GB6

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

omit [StandardBorelSpace Ω] in
/-- Every seed admitted by the actual cover is a nonnegative real root. -/
theorem rootPt_nonneg_of_seedOK (c : SourceData Ω) {x : RootIdx c.Θ c.Q}
    (hx : RootCv.RootSeedOK c x) : 0 ≤ rootPt x := by
  rcases hx.2 with hzero | hpos
  · simp only [rootPt, hzero, le_refl]
  · exact hpos.1.le

/-- On COVER's event, every switched relative prefix has the required
capacity geometry before contact. The root-arc bound is a conclusion. -/
theorem ae_cover_prefixImage_geometry (h13 : Theorem13Statement.{u})
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (ℝ × ℝ≥0)) :
    ∀ᵐ ω ∂c.P, ω ∈ RootCv.coverEvent c r →
      Disjoint (c.α ω '' Icc 0 c.s) ((fun z : ℂ => -z⁻¹) ''
        (prefixSet c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h (rootPt r.1) l ω \ {0})) →
      let A := prefixImage c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h
        (regW c.s c.W c.ζ) c.s (rootPt r.1) l ω
      Bornology.IsBounded A ∧ IsPreconnected (A ∪ {z : ℂ | z.im ≤ 0}) ∧
        ∃ K : Set ℂ, IsCompact K ∧ fillH A = fillH K := by
  by_cases hx : RootCv.RootSeedOK c r.1
  · filter_upwards [RootCv.ae_coverEvent_spec h13 c r,
      ae_prefixImage_geometry h13 c (rootPt r.1) (rootPt_nonneg_of_seedOK c hx) l]
      with ω hcover hgeom hω hsep
    exact hgeom (hcover hω).2.2.2.2.2 hsep
  · exact Eventually.of_forall fun ω hω => (hx hω.1).elim

/-- A Borel reader of the literal root capacity on the full low-arc
cover, including every admissible switched history before contact. -/
theorem exists_measurable_capR_on_cover (h13 : Theorem13Statement.{u})
    (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) :
    ∃ C : Ω → ℝ, Measurable C ∧ (∀ ω, 0 ≤ C ω) ∧
      ∀ᵐ ω ∂c.P, ω ∈ RootCv.coverEvent c r →
        SchedAdm c.b c.jumps c.Θ c.Q (κ := c.κ)
          (rootPt r.1) (rootEntry r.1) (entryList l) →
        Disjoint (c.α ω '' Icc 0 c.s) ((fun z : ℂ => -z⁻¹) ''
          (prefixSet c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h (rootPt r.1)
            (schedOf (rootEntry r.1) (entryList l)) ω \ {0})) →
        C ω = capR c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s r l ω := by
  by_cases hx : RootCv.RootSeedOK c r.1
  · obtain ⟨C, hCm, hC0, hC⟩ := exists_measurable_capR_before_contact h13 c r
      (rootPt_nonneg_of_seedOK c hx) l
    refine ⟨C, hCm, hC0, ?_⟩
    filter_upwards [hC, RootCv.ae_coverEvent_spec h13 c r]
      with ω hCω hcover hω hadm hsep
    exact hCω (hcover hω).2.2.2.2.2 hadm hsep
  · exact ⟨fun _ => 0, measurable_const, (fun _ => le_rfl),
      Eventually.of_forall fun ω hω => (hx hω.1).elim⟩

/-- The same family simultaneously covers every countable root and
switched history; no extra regularity or capacity premise is supplied. -/
theorem exists_measurable_capR_family_on_cover (h13 : Theorem13Statement.{u})
    (c : SourceData Ω) :
    ∃ C : ScaledRootIdx c.Θ c.Q → List (EntryIdx c.Θ c.Q) → Ω → ℝ,
      (∀ r l, Measurable (C r l)) ∧ (∀ r l ω, 0 ≤ C r l ω) ∧
      ∀ᵐ ω ∂c.P, ∀ r l, ω ∈ RootCv.coverEvent c r →
        SchedAdm c.b c.jumps c.Θ c.Q (κ := c.κ)
          (rootPt r.1) (rootEntry r.1) (entryList l) →
        Disjoint (c.α ω '' Icc 0 c.s) ((fun z : ℂ => -z⁻¹) ''
          (prefixSet c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h (rootPt r.1)
            (schedOf (rootEntry r.1) (entryList l)) ω \ {0})) →
        C r l ω = capR c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s r l ω := by
  have : Countable c.Θ := c.hΘc.to_subtype
  have : Countable c.Q := c.hQc.to_subtype
  choose C hCm hC0 hC using fun r l => exists_measurable_capR_on_cover h13 c r l
  exact ⟨C, hCm, hC0, ae_all_iff.mpr fun r => ae_all_iff.mpr (hC r)⟩

end InteractingSLE.Theorem14.GW2TipSystem.RootH29
