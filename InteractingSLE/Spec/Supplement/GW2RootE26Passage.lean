/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootD25Passage

/-!
# A first crossing is detectable in the original clock

Packet PROVE-T14-GW2ROOT2. Reuse the dense-time first-passage theorem
and the intermediate value theorem for a continuous strictly increasing
clock. A capacity crossing before the clock of `q` is equivalent to a
crossing at a rational physical time before `q`.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2TipSystem.RootE26

open RootD25 RootV7

/-- Detection of a continuous driver's first crossing uses only rational
physical observations earlier than the query, through any finite clock. -/
theorem entryCapacity_lt_clock_iff {z : DriverRecord} {Y : ℝ≥0 → ℝ}
    (hY : ContinuousOn Y {t | (t : ℝ≥0∞) < z.1})
    (hread : ∀ r : ℚ≥0, ((r : ℝ≥0) : ℝ≥0∞) < z.1 → z.2 r = Y r)
    {c : ℝ≥0 → ℝ≥0} {v q : ℝ≥0} (h0 : c 0 = 0)
    (hm : StrictMonoOn c (Icc 0 v)) (hc : ContinuousOn c (Icc 0 v))
    (hlife : z.1 = (c v : ℝ≥0∞)) (hq : q ≤ v) :
    entryCapacity z < (c q : ℝ≥0∞) ↔
      ∃ r : ℚ≥0, (r : ℝ≥0) < q ∧ (r : ℝ≥0) < v ∧ 2 < Y (c r) := by
  have hcomp : ContinuousOn (fun t => Y (c t))
      {t : ℝ≥0 | (t : ℝ≥0∞) < (v : ℝ≥0∞)} := by
    apply hY.comp (hc.mono fun t ht => ⟨zero_le, (ENNReal.coe_lt_coe.mp ht).le⟩)
    intro t ht
    rw [hlife]
    exact ENNReal.coe_lt_coe.mpr
      (hm ⟨zero_le, (ENNReal.coe_lt_coe.mp ht).le⟩ ⟨zero_le, le_rfl⟩
        (ENNReal.coe_lt_coe.mp ht))
  have hdetect := Coupling.hitBelow_lt_iff (ε := 0)
    ((continuousOn_const (c := (-2 : ℝ))).add hcomp).neg
    LocalExt.dense_range_coe_nnrat q
  have hphysical : (Coupling.hitBelow (fun t => -(-2 + Y (c t)))
      (v : ℝ≥0∞) 0 < q) ↔
      ∃ r : ℚ≥0, (r : ℝ≥0) < q ∧ (r : ℝ≥0) < v ∧ 2 < Y (c r) := by
    constructor
    · intro h
      obtain ⟨t, ⟨r, rfl⟩, hrq, hrv, hYt⟩ := hdetect.mp h
      refine ⟨r, hrq, ENNReal.coe_lt_coe.mp hrv, ?_⟩
      change -(-2 + Y (c r)) < 0 at hYt
      linarith only [hYt]
    · rintro ⟨r, hrq, hrv, hYr⟩
      apply hdetect.mpr
      refine ⟨r, mem_range_self r, hrq, ENNReal.coe_lt_coe.mpr hrv, ?_⟩
      change -(-2 + Y (c r)) < 0
      linarith only [hYr]
  rw [← hphysical, entryCapacity_eq_hitBelow hY hread]
  constructor
  · intro h
    obtain ⟨u, _, huq, huζ, hYu⟩ :=
      (Coupling.hitBelow_lt_iff (continuousOn_const.add hY).neg dense_univ (c q)).mp h
    have hcq : ContinuousOn c (Icc 0 q) := hc.mono (Icc_subset_Icc_right hq)
    obtain ⟨r, hr, hcr⟩ := intermediate_value_Icc (zero_le : (0 : ℝ≥0) ≤ q) hcq
      (show u ∈ Icc (c 0) (c q) by rw [h0]; exact ⟨zero_le, huq.le⟩)
    have hrq : r < q := lt_of_le_of_ne hr.2 (fun heq => by
      rw [heq] at hcr
      exact huq.ne hcr.symm)
    have hval : -(-2 + Y (c r)) < 0 := by
      rw [hcr]
      exact hYu
    exact (Coupling.hitBelow_le (ENNReal.coe_lt_coe.mpr (hrq.trans_le hq)) hval).trans_lt
      (WithTop.coe_lt_coe.mpr hrq)
  · intro h
    obtain ⟨r, hrq, hrv, hYr⟩ := hphysical.mp h
    have hclock := hm ⟨zero_le, (hrq.trans_le hq).le⟩ ⟨zero_le, hq⟩ hrq
    have hrζ : (c r : ℝ≥0∞) < z.1 := by
      rw [hlife]
      exact ENNReal.coe_lt_coe.mpr (hm ⟨zero_le, hrv.le⟩ ⟨zero_le, le_rfl⟩ hrv)
    have hval : -(-2 + Y (c r)) < 0 := by linarith only [hYr]
    exact (Coupling.hitBelow_le hrζ hval).trans_lt (WithTop.coe_lt_coe.mpr hclock)

end InteractingSLE.Theorem14.GW2TipSystem.RootE26
