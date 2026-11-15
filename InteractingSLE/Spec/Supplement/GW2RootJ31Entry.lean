/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootJ31Sample

/-! # Borel physical entry for the restarted switched-capacity sample -/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2TipSystem.RootJ31

open Exist.StagedLaw Restart RootD25

/-- Pull the future sample's first crossing back to its own physical time.
Failure is assigned the actual physical buffer, rather than a fictitious entry. -/
def switchedEntry (a : ℝ≥0) (ε x : ℝ) (s v v₀ T F : ℝ≥0)
    (p : RecData × RecData) : ℝ≥0 :=
  open scoped Classical in
  if switchedSample a ε x s v v₀ T F p ∈ reachSet then
    invClock (fun t => (capacityIncrement a x s T t p : ℝ)) (F : ℝ≥0∞)
      (entryCapacity (switchedSample a ε x s v v₀ T F p)).toNNReal else F

/-- Random buffers, entry capacities and whole switched records are all permitted. -/
theorem measurable_switchedEntry_random {Ω : Type*} [MeasurableSpace Ω]
    {p : Ω → RecData × RecData} (hp : Measurable p)
    {F : Ω → ℝ≥0} (hF : Measurable F)
    (a : ℝ≥0) (ε x : ℝ) (s v v₀ T : ℝ≥0) :
    Measurable fun ω => switchedEntry a ε x s v v₀ T (F ω) (p ω) := by
  classical
  have hz := measurable_switchedSample_random hp hF a ε x s v v₀ T
  have hτ := (measurable_entryCapacity.comp hz).ennreal_toNNReal
  have hi : Measurable fun ω => invClock
      (fun t => (capacityIncrement a x s T t (p ω) : ℝ)) (F ω : ℝ≥0∞)
      (entryCapacity (switchedSample a ε x s v v₀ T (F ω) (p ω))).toNNReal := by
    unfold invClock
    refine Measurable.iSup fun q : ℚ => Measurable.ite ?_ measurable_const measurable_const
    exact (MeasurableSet.const _).inter
      ((measurableSet_le measurable_const (measurable_coe_nnreal_ennreal.comp hF)).inter
        (measurableSet_lt (NNReal.continuous_coe.measurable.comp
          (measurable_capacityIncrement_random hp measurable_const a x s T))
          (NNReal.continuous_coe.measurable.comp hτ)))
  exact Measurable.ite (hz measurableSet_reachSet) hi hF

theorem switchedEntry_eq_buffer_of_not_reach (a : ℝ≥0) (ε x : ℝ)
    (s v v₀ T F : ℝ≥0) (p : RecData × RecData)
    (hf : switchedSample a ε x s v v₀ T F p ∉ reachSet) :
    switchedEntry a ε x s v v₀ T F p = F := ite_eq_right hf

/-- The finite rational-supremum inverse cannot exceed its physical cap,
even when the supplied capacity reader is not an increasing clock. -/
theorem switchedEntry_le_buffer (a : ℝ≥0) (ε x : ℝ)
    (s v v₀ T F : ℝ≥0) (p : RecData × RecData) :
    switchedEntry a ε x s v v₀ T F p ≤ F := by
  classical
  unfold switchedEntry
  split_ifs
  · unfold invClock
    apply ciSup_le
    intro q
    split_ifs with hq
    · exact ENNReal.coe_le_coe.mp hq.2.1
    · exact zero_le
  · exact le_rfl

end InteractingSLE.Theorem14.GW2TipSystem.RootJ31
