/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootD25Sample
import InteractingSLE.Spec.Sec7.LocalExtNRef
import InteractingSLE.Spec.Sec5.Prop59StageUnit

/-!
# A measurable first crossing and reach event for the actual driver sample

Packet PROVE-T14-GW2ROOT2. The first crossing is read from rational live
sample values. The landed dense-time hitting theorem identifies it with
the original first passage on every continuous driver. The driver value
there is exactly two, as required by the open target band.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2TipSystem.RootD25

open RootV7

/-- First passage above two, read only from live rational driver observations. -/
def entryCapacity (z : DriverRecord) : ℝ≥0∞ :=
  ⨅ q : ℚ≥0, if ((q : ℝ≥0) : ℝ≥0∞) < z.1 ∧ 2 < z.2 q then
    ((q : ℝ≥0) : ℝ≥0∞) else ⊤

/-- The measurable crossing event on the common actual-sample carrier. -/
def reachSet : Set DriverRecord := {z | entryCapacity z < z.1}

theorem measurable_entryCapacity : Measurable entryCapacity := by
  refine Measurable.iInf fun q => Measurable.ite ?_ measurable_const measurable_const
  exact (measurableSet_lt measurable_const measurable_fst).inter
    (measurableSet_lt measurable_const ((measurable_pi_apply q).comp measurable_snd))

theorem measurableSet_reachSet : MeasurableSet reachSet :=
  measurableSet_lt measurable_entryCapacity measurable_fst

theorem entryCapacity_lt_iff (z : DriverRecord) (t : ℝ≥0∞) :
    entryCapacity z < t ↔ ∃ q : ℚ≥0,
      ((q : ℝ≥0) : ℝ≥0∞) < t ∧ ((q : ℝ≥0) : ℝ≥0∞) < z.1 ∧ 2 < z.2 q := by
  classical
  rw [entryCapacity, iInf_lt_iff]
  constructor
  · rintro ⟨q, hq⟩
    by_cases hg : ((q : ℝ≥0) : ℝ≥0∞) < z.1 ∧ 2 < z.2 q
    · rw [ite_eq_left hg] at hq
      exact ⟨q, hq, hg⟩
    · simp only [hg, ↓reduceIte, not_top_lt] at hq
  · rintro ⟨q, hqt, hqζ, hqY⟩
    refine ⟨q, ?_⟩
    rw [ite_eq_left ⟨hqζ, hqY⟩]
    exact hqt

/-- The Borel crossing time is the actual first passage of the continuous
driver read by the sample; the existing dense-time theorem supplies this identity. -/
theorem entryCapacity_eq_hitBelow {z : DriverRecord} {Y : ℝ≥0 → ℝ}
    (hc : ContinuousOn Y {t | (t : ℝ≥0∞) < z.1})
    (hread : ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < z.1 → z.2 q = Y q) :
    entryCapacity z = (Coupling.hitBelow (fun t => -(-2 + Y t)) z.1 0 : ℝ≥0∞) := by
  apply le_antisymm
  · refine ENNReal.le_of_forall_nnreal_lt fun t ht => ?_
    by_contra hnot
    have hhit := not_le.mp hnot
    obtain ⟨q, ⟨r, rfl⟩, hqt, hqζ, hqY⟩ :=
      (Coupling.hitBelow_lt_iff (continuousOn_const.add hc).neg
        LocalExt.dense_range_coe_nnrat t).mp hhit
    have hY : 2 < z.2 r := by
      rw [hread r hqζ]
      change -(-2 + Y r) < 0 at hqY
      linarith only [hqY]
    have hentry := (entryCapacity_lt_iff z t).mpr
      ⟨r, ENNReal.coe_lt_coe.mpr hqt, hqζ, hY⟩
    exact lt_asymm ht hentry
  · refine le_iInf fun q => ?_
    split_ifs with hg
    · have hY : -(-2 + Y q) < 0 := by rw [hread q hg.1] at hg; linarith only [hg.2]
      exact Coupling.hitBelow_le hg.1 hY
    · exact le_top

/-- On a successful finite crossing the actual driver is at the centre
of the target band; this reuses the proved first-passage level theorem. -/
theorem driver_eq_two_at_entry {z : DriverRecord} {Y : ℝ≥0 → ℝ}
    (hc : ContinuousOn Y {t | (t : ℝ≥0∞) < z.1}) (hzero : Y 0 = 0)
    (hread : ∀ q : ℚ≥0, ((q : ℝ≥0) : ℝ≥0∞) < z.1 → z.2 q = Y q)
    {t : ℝ≥0} (ht : entryCapacity z = (t : ℝ≥0∞)) : Y t = 2 := by
  have hhit : Coupling.hitBelow (fun u => -(-2 + Y u)) z.1 0 =
      (t : WithTop ℝ≥0) := (entryCapacity_eq_hitBelow hc hread).symm.trans ht
  have h := Sec5.Prop59Stage.eq_zero_of_hitBelow_eq hc hzero
    (show (-2 : ℝ) < 0 by norm_num) hhit
  linarith only [h]

end InteractingSLE.Theorem14.GW2TipSystem.RootD25
