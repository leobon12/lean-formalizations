/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2JDetR3Chain

/-!
# The physical-capacity cutoff read from GW2 records

The cutoff is the first rational relative time at which the recovered physical
capacity exceeds the prescribed physical time. Its measurability holds on the
whole record space. Its exact value needs only the local inverse-clock law.
-/

set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2JDetR3

open Exist.StagedLaw Supp8.GB6

/-- Every time strictly below the supremum of an open continuous clock is
attained, uniquely when the clock is strictly increasing. -/
theorem existsUnique_time_of_lt_clockSup {a : ℝ≥0 → ℝ} {S : ℝ≥0∞}
    (ha0 : a 0 = 0) (hm : StrictMonoOn a {t | (t : ℝ≥0∞) < S})
    (hc : ContinuousOn a {t | (t : ℝ≥0∞) < S})
    {u : ℝ≥0} (hu : (u : ℝ≥0∞) <
      ⨆ (t : ℝ≥0) (_ : (t : ℝ≥0∞) < S), ((a t).toNNReal : ℝ≥0∞)) :
    ∃! t : ℝ≥0, (t : ℝ≥0∞) < S ∧ a t = u := by
  obtain ⟨T, hT⟩ := lt_iSup_iff.mp hu
  obtain ⟨hTS, huT⟩ := lt_iSup_iff.mp hT
  have haT : (u : ℝ) < a T := by
    have h := NNReal.coe_lt_coe.mpr (ENNReal.coe_lt_coe.mp huT)
    have hn : 0 ≤ a T := by
      have h0 : ((0 : ℝ≥0) : ℝ≥0∞) < S := lt_of_le_of_lt bot_le hTS
      have h := hm.monotoneOn h0 hTS (zero_le : (0 : ℝ≥0) ≤ T)
      rwa [ha0] at h
    simpa only [Real.coe_toNNReal _ hn] using h
  obtain ⟨t, ht, he⟩ := GaugeE.exists_clock_eq
    (hc.mono fun t ht => (ENNReal.coe_le_coe.mpr ht.2).trans_lt hTS) ha0 haT.le
  have htS : (t : ℝ≥0∞) < S := (ENNReal.coe_le_coe.mpr ht.2).trans_lt hTS
  refine ⟨t, ⟨htS, he⟩, ?_⟩
  intro t' ht'
  exact hm.injOn ht'.1 htS (ht'.2.trans he.symm)

open scoped Classical in
/-- The first relative time at which the inverse-hull capacity exceeds `t`. -/
def capacityCut (s t : ℝ≥0) (p : RecData × RecData) : ℝ≥0∞ :=
  ⨅ q : ℚ≥0, if (t : ℝ) < physicalCapacity s (q : ℝ≥0) p
    then ((q : ℝ≥0) : ℝ≥0∞) else ⊤

theorem measurable_capacityCut (s t : ℝ≥0) : Measurable (capacityCut s t) := by
  classical
  apply Measurable.iInf
  intro q
  exact Measurable.ite (measurableSet_lt measurable_const (measurable_physicalCapacity s q))
    measurable_const measurable_const

/-- A local inverse clock identifies the cutoff. Values beyond the buffer
cannot introduce an earlier threshold crossing. -/
theorem capacityCut_eq_of_local_inverse (s t : ℝ≥0) (p : RecData × RecData)
    {v b : ℝ≥0} (hvb : v < b)
    (hcap : ∀ q : ℝ≥0, q < b → ((t : ℝ) < physicalCapacity s q p ↔ v < q)) :
    capacityCut s t p = (v : ℝ≥0∞) := by
  classical
  apply le_antisymm
  · apply le_of_forall_gt
    intro B hvB
    obtain ⟨c, hvc, hcB⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hvB
    have hvc' : v < c := ENNReal.coe_lt_coe.mp hvc
    obtain ⟨q, hvq, hqb⟩ := exists_rat_btwn
      (show (v : ℝ) < min b c by exact_mod_cast lt_min hvb hvc')
    have hq0 : 0 ≤ q := by exact_mod_cast v.coe_nonneg.trans hvq.le
    let q' : ℚ≥0 := ⟨q, hq0⟩
    have hqb' : (q' : ℝ≥0) < b := by exact_mod_cast (lt_min_iff.mp hqb).1
    have hvq' : v < (q' : ℝ≥0) := by exact_mod_cast hvq
    have hcross := (hcap q' hqb').mpr hvq'
    have hle : capacityCut s t p ≤ ((q' : ℝ≥0) : ℝ≥0∞) := by
      exact (iInf_le _ q').trans_eq (ite_eq_left hcross)
    exact (hle.trans (ENNReal.coe_le_coe.mpr
      (show (q' : ℝ≥0) ≤ c by exact_mod_cast (lt_min_iff.mp hqb).2.le))).trans_lt hcB
  · apply le_iInf
    intro q
    split_ifs with hq
    · apply ENNReal.coe_le_coe.mpr
      by_contra h
      have hqv : (q : ℝ≥0) < v := not_le.mp h
      exact (not_lt_of_ge hqv.le) ((hcap q (hqv.trans hvb)).mp hq)
    · exact le_top

end InteractingSLE.Theorem14.GW2JDetR3
