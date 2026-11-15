/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootF27Inner
import InteractingSLE.Spec.Supplement.GW2RootF27Fibre

/-!
# Observable unit events without global measurability of literal capacity

Packet PROVE-T14-GW2ROOT2. For every original source setup, root and
history, construct an event in the exact retained sigma algebra on which
the literal capacity increment is at least one, at every outcome. Every
measurable almost-sure geometric certificate for a unit is preserved.
Thus the unit-event bookkeeping does not require global measurability of
the exceptional branches of `capOf`. No geometry or comparison is assumed
to construct the events or prove these properties.
-/

set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootF27

open GW2Schedule GW2Tip Exist Staged StagedLaw Restart LQGMetric RootC24

variable {Ω : Type u} [mΩ : MeasurableSpace Ω] (c : SourceData Ω)
  (r : ScaledRootIdx c.Θ c.Q)

/-- A unit event in the literal retained root sigma algebra. The capacity
inequality is respected on every outcome, including exceptional samples. -/
def unitEvent (l : List (EntryIdx c.Θ c.Q)) : Set Ω :=
  recordCore (c.sigma r l) (stageSigma_le c.hβA.1 c.hh.1 c.hcf c.s _ _) c.P
    (TestEvents.capacityUnit
      (capR c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s r) l)

/-- The `hV` clause of the root test is proved for the constructed events. -/
theorem measurableSet_unitEvent (l : List (EntryIdx c.Θ c.Q)) :
    MeasurableSet[c.sigma r l] (unitEvent c r l) :=
  measurableSet_recordCore _ _ _ _

/-- The constructed event gives the actual capacity inequality everywhere,
which is stronger than the root test's restriction to alive outcomes. -/
theorem unitEvent_capR (l : List (EntryIdx c.Θ c.Q)) (x : EntryIdx c.Θ c.Q)
    {ω : Ω} (hω : ω ∈ unitEvent c r (x :: l)) :
    capR c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s r l ω + 1 ≤
      capR c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s r (x :: l) ω := by
  have h := recordCore_subset _ _ c.P
    (TestEvents.capacityUnit
      (capR c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s r) (x :: l)) hω
  exact h

variable [StandardBorelSpace Ω]

/-- Every ambient measurable almost-sure certificate for a literal unit
belongs almost surely to the same fixed observable unit event. No global
measurability or particular Borel version of either capacity is needed. -/
theorem ae_mem_unitEvent (l : List (EntryIdx c.Θ c.Q)) {E : Set Ω}
    (hE : MeasurableSet E)
    (hunit : ∀ᵐ ω ∂c.P, ω ∈ E → ω ∈ TestEvents.capacityUnit
      (capR c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s r) l) :
    ∀ᵐ ω ∂c.P, ω ∈ E → ω ∈ unitEvent c r l := by
  have hf : Measurable (stageMap c.hκ c.h12p c.βA c.c₀ c.h c.s c.W c.ζ
      (schedSpecOf r.1 l) ((entryList l).length + 1)) :=
    Measurable.of_comap_le (stageSigma_le c.hβA.1 c.hh.1 c.hcf c.s _ _)
  exact ae_mem_recordCore hf
    (fun ω ω' heq hω => (capacityUnit_fibre c r l heq).mp hω) hE hunit

/-- On a measurable event, a geometric unit implication is unchanged when
the literal unit event is replaced by its observable inner event. -/
theorem ae_unitEvent_iff_capacityUnit (l : List (EntryIdx c.Θ c.Q)) {E : Set Ω}
    (hE : MeasurableSet E)
    (hunit : ∀ᵐ ω ∂c.P, ω ∈ E → ω ∈ TestEvents.capacityUnit
      (capR c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s r) l) :
    ∀ᵐ ω ∂c.P, ω ∈ E → (ω ∈ unitEvent c r l ↔
      ω ∈ TestEvents.capacityUnit
        (capR c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s r) l) := by
  filter_upwards [ae_mem_unitEvent c r l hE hunit] with ω hω hωE
  exact iff_of_true (hω hωE) (recordCore_subset _ _ _ _ (hω hωE))

/-- All countably many successful-test unit certificates can use the
same preconstructed unit family simultaneously. The certificate is only
an almost-sure implication; the resulting unit inequality is pointwise. -/
theorem ae_tests_mem_unitEvent {A : Set Ω} (hA : MeasurableSet A)
    {E : Set Ω} (hE : MeasurableSet E) (l : List (EntryIdx c.Θ c.Q))
    (θ : c.Θ) (T : c.Q → Set Ω) (hT : ∀ q, MeasurableSet (T q))
    (hunit : ∀ᵐ ω ∂c.P, ω ∈ A → ω ∈ E → ∀ q, ω ∈ T q →
      capR c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s r l ω + 1 ≤
        capR c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h c.W c.ζ c.s r ((θ, q) :: l) ω) :
    ∀ᵐ ω ∂c.P, ω ∈ A → ω ∈ E → ∀ q, ω ∈ T q →
      ω ∈ unitEvent c r ((θ, q) :: l) := by
  have : Countable c.Q := c.hQc.to_subtype
  have hq : ∀ q, ∀ᵐ ω ∂c.P, ω ∈ A ∩ E ∩ T q →
      ω ∈ unitEvent c r ((θ, q) :: l) := by
    intro q
    apply ae_mem_unitEvent c r _ ((hA.inter hE).inter (hT q))
    filter_upwards [hunit] with ω hω hωmem
    exact hω hωmem.1.1 hωmem.1.2 q hωmem.2
  filter_upwards [ae_all_iff.mpr hq] with ω hω hωA hωE q hωT
  exact hω q ⟨⟨hωA, hωE⟩, hωT⟩

end InteractingSLE.Theorem14.GW2TipSystem.RootF27
