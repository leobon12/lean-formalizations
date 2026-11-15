/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootC24Data

/-!
# Literal capacity increments are determined by the extended root record

Packet PROVE-T14-GW2ROOT2. The landed fibre identities determine the
new capacity. Truncating the extended stopped record determines the
previous capacity as well. This includes every exceptional sample and
uses no capacity measurability or almost-sure geometric regularity.
-/

set_option autoImplicit false
noncomputable section

open Set MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootF27

open GW2Schedule GW2Tip Exist Staged StagedLaw Restart LQGMetric RootC24

variable {Ω : Type u} [MeasurableSpace Ω] (c : SourceData Ω)
  (r : ScaledRootIdx c.Θ c.Q)

/-- Equality of the extended root records implies equality of their
previous records, including stopped or unsuccessful attempts. -/
theorem root_record_tail_eq (l : List (EntryIdx c.Θ c.Q)) (x : EntryIdx c.Θ c.Q)
    {ω ω' : Ω}
    (hs : stageMap c.hκ c.h12p c.βA c.c₀ c.h c.s c.W c.ζ
      (schedSpecOf r.1 (x :: l)) ((entryList (x :: l)).length + 1) ω =
      stageMap c.hκ c.h12p c.βA c.c₀ c.h c.s c.W c.ζ
        (schedSpecOf r.1 (x :: l)) ((entryList (x :: l)).length + 1) ω') :
    stageMap c.hκ c.h12p c.βA c.c₀ c.h c.s c.W c.ζ
      (schedSpecOf r.1 l) ((entryList l).length + 1) ω =
      stageMap c.hκ c.h12p c.βA c.c₀ c.h c.s c.W c.ζ
        (schedSpecOf r.1 l) ((entryList l).length + 1) ω' := by
  have hs' : stageMap c.hκ c.h12p c.βA c.c₀ c.h c.s c.W c.ζ
      (schedSpec (rootPt r.1) (schedOf (rootEntry r.1) (entryList l) ++
        [((x.1 : ℝ), (x.2 : ℝ≥0))]))
      (schedOf (rootEntry r.1) (entryList l) ++ [((x.1 : ℝ), (x.2 : ℝ≥0))]).length ω =
      stageMap c.hκ c.h12p c.βA c.c₀ c.h c.s c.W c.ζ
        (schedSpec (rootPt r.1) (schedOf (rootEntry r.1) (entryList l) ++
          [((x.1 : ℝ), (x.2 : ℝ≥0))]))
        (schedOf (rootEntry r.1) (entryList l) ++
          [((x.1 : ℝ), (x.2 : ℝ≥0))]).length ω' := by
    rw [schedSpecOf, entryList_cons, schedOf_cons] at hs
    have hl : (entryList l).length + 1 + 1 =
        (schedOf (rootEntry r.1) (entryList l) ++
          [((x.1 : ℝ), (x.2 : ℝ≥0))]).length := by
      rw [List.length_append, List.length_singleton, length_schedOf]
    exact hl ▸ hs
  have ht := stageMap_eq_of_append_eq c.hκ c.h12p c.βA c.c₀ c.h c.s c.W c.ζ
    (rootPt r.1) (schedOf (rootEntry r.1) (entryList l))
    ((x.1 : ℝ), (x.2 : ℝ≥0)) hs'
  exact length_schedOf (rootEntry r.1) (entryList l) ▸ ht

/-- The literal unit-capacity assertion is constant on the extended
record fibres. Neither capacity function is assumed measurable. -/
theorem capacityUnit_fibre (l : List (EntryIdx c.Θ c.Q)) {ω ω' : Ω}
    (hs : stageMap c.hκ c.h12p c.βA c.c₀ c.h c.s c.W c.ζ
      (schedSpecOf r.1 l) ((entryList l).length + 1) ω =
      stageMap c.hκ c.h12p c.βA c.c₀ c.h c.s c.W c.ζ
        (schedSpecOf r.1 l) ((entryList l).length + 1) ω') :
    ω ∈ TestEvents.capacityUnit
      (capR c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s r) l ↔
    ω' ∈ TestEvents.capacityUnit
      (capR c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s r) l := by
  cases l with
  | nil => rfl
  | cons x l =>
    have hnew := capR_eq_of_stageMap_eq c.hκ c.h12p c.βA c.c₀ c.h c.b c.jumps
      c.s c.W c.ζ r (x :: l) hs
    have hold := capR_eq_of_stageMap_eq c.hκ c.h12p c.βA c.c₀ c.h c.b c.jumps
      c.s c.W c.ζ r l (root_record_tail_eq c r l x hs)
    simp only [TestEvents.capacityUnit, mem_ofPred_eq]
    rw [hnew, hold]

end InteractingSLE.Theorem14.GW2TipSystem.RootF27
