/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootJ31Driver
import InteractingSLE.Spec.Supplement.GW2RootD25Passage

/-!
# Restarting the low-arc reader after a retained switched prefix

Packet PROVE-T14-GW2ROOT2. Root centering is at the capacity of the
initial root piece. Future sample time starts at the capacity of the
WHOLE retained prefix. The two capacities are deliberately distinct.
Every formula is a Borel readout on all records; generating-trace and
physical clock identifications are not asserted by these definitions.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2TipSystem.RootJ31

open Exist.StagedLaw Restart RootV7

/-- Normalized capacity gained during future own time t after physical time T. -/
def capacityIncrement (a : ℝ≥0) (x : ℝ) (s T t : ℝ≥0) (p : RecData × RecData) : ℝ≥0 :=
  a ^ 2 * (RootH29.forwardCapacity x s (T + t) p -
    RootH29.forwardCapacity x s T p).toNNReal

/-- The absolute driver in the initial joint chart, read at a future
capacity measured from the complete retained prefix. ε selects orientation. -/
def stageDriverRead (a : ℝ≥0) (ε x : ℝ) (s v v₀ T u : ℝ≥0)
    (p : RecData × RecData) : ℝ :=
  ε * (a : ℝ) * (capacityDriverRead x s v
      ((RootH29.forwardCapacity x s T p).toNNReal + u / a ^ 2) p -
    capacityDriverRead x s v (RootH29.forwardCapacity x s v₀ p).toNNReal p)

/-- The future sample is killed at the capacity actually assigned to F. -/
def switchedSample (a : ℝ≥0) (ε x : ℝ) (s v v₀ T F : ℝ≥0)
    (p : RecData × RecData) : DriverRecord :=
  (capacityIncrement a x s T F p, fun q =>
    if ((q : ℝ≥0) : ℝ≥0∞) < (capacityIncrement a x s T F p : ℝ≥0∞) then
      stageDriverRead a ε x s v v₀ T q p else 0)

variable {Ω : Type*} [MeasurableSpace Ω]
  {p : Ω → RecData × RecData} (hp : Measurable p)
  {u : Ω → ℝ≥0} (hu : Measurable u)

include hp hu

theorem measurable_capacityIncrement_random (a : ℝ≥0) (x : ℝ) (s T : ℝ≥0) :
    Measurable fun ω => capacityIncrement a x s T (u ω) (p ω) :=
  measurable_const.mul
    ((RootH29.measurable_forwardCapacity_random x s hp (measurable_const.add hu)).sub
      (RootH29.measurable_forwardCapacity_random x s hp measurable_const)).real_toNNReal

theorem measurable_stageDriverRead_random (a : ℝ≥0) (ε x : ℝ) (s v v₀ T : ℝ≥0) :
    Measurable fun ω => stageDriverRead a ε x s v v₀ T (u ω) (p ω) := by
  have hT := (RootH29.measurable_forwardCapacity_random x s hp
    (measurable_const : Measurable (fun _ : Ω => T))).real_toNNReal
  have h₀ := (RootH29.measurable_forwardCapacity_random x s hp
    (measurable_const : Measurable (fun _ : Ω => v₀))).real_toNNReal
  exact measurable_const.mul
    ((measurable_capacityDriverRead_random hp (hT.add (hu.div_const _)) x s v).sub
      (measurable_capacityDriverRead_random hp h₀ x s v))

/-- Random geometric killing times cause no measurability problem for the sample. -/
theorem measurable_switchedSample_random (a : ℝ≥0) (ε x : ℝ) (s v v₀ T : ℝ≥0) :
    Measurable fun ω => switchedSample a ε x s v v₀ T (u ω) (p ω) := by
  have hlife := measurable_coe_nnreal_ennreal.comp
    (measurable_capacityIncrement_random hp hu a x s T)
  exact hlife.prodMk (measurable_pi_iff.mpr fun q => Measurable.ite
    (measurableSet_lt measurable_const hlife)
    (measurable_stageDriverRead_random hp measurable_const a ε x s v v₀ T)
    measurable_const)

omit hp hu [MeasurableSpace Ω] in
/-- The live readings of the constructed sample are exact on every record. -/
theorem switchedSample_read (a : ℝ≥0) (ε x : ℝ) (s v v₀ T F : ℝ≥0)
    (p : RecData × RecData) {q : ℚ≥0}
    (hq : ((q : ℝ≥0) : ℝ≥0∞) < (switchedSample a ε x s v v₀ T F p).1) :
    (switchedSample a ε x s v v₀ T F p).2 q = stageDriverRead a ε x s v v₀ T q p :=
  ite_eq_left hq

omit hp hu [MeasurableSpace Ω] in
theorem capacityIncrement_zero (a : ℝ≥0) (x : ℝ) (s T : ℝ≥0)
    (p : RecData × RecData) : capacityIncrement a x s T 0 p = 0 := by
  simp only [capacityIncrement, add_zero, sub_self, Real.toNNReal_zero, mul_zero]

end InteractingSLE.Theorem14.GW2TipSystem.RootJ31
