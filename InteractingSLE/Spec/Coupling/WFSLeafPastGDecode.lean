/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafPastGNonzero
import InteractingSLE.Spec.ZhanGT4.A1CanonFactor

/-!
# Reading earlier lifetime tests from a later raw sample past

A nonzero sample after `r` certifies survival past `r`. Nonzero samples in
every live interval give the converse. The resulting event reader is Borel
for the raw sample sigma algebra, up to the already available null completion.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.WFS

open LawUnique Restart.FlowStopIdentG

/-- A raw past includes each state sample at or before its time. -/
theorem measurable_sample_rawPast {Ω : Type*} [MeasurableSpace Ω] {nL nR : ℕ}
    (Y : Ω → HistorySpace nL nR) {t : ℝ≥0} (p : ℕ × ℕ) (hp : dyadicTime p ≤ t) :
    Measurable[samplePastSigma Y t] fun ω => (Y ω).2 p := by
  have hm := (measurable_pi_apply p).comp
    (comap_measurable (fun ω => samplePast t (Y ω)))
  simpa only [samplePast, hp, ↓reduceIte, Function.comp_def] using hm

/-- The continuous-state reader at an earlier time is measurable for the raw past. -/
theorem measurable_histState_rawPast {Ω : Type*} [MeasurableSpace Ω] {nL nR : ℕ}
    (Y : Ω → HistorySpace nL nR) {r t : ℝ≥0} (hrt : r ≤ t) :
    Measurable[samplePastSigma Y t] fun ω => histState (Y ω) r := by
  let : MeasurableSpace Ω := samplePastSigma Y t
  exact (StronglyMeasurable.limUnder fun n =>
    (measurable_sample_rawPast Y (lowerDyadic r n)
      ((dyadicTime_lowerDyadic_le r n).trans hrt)).stronglyMeasurable).measurable

/-- Existence of a nonzero sample in `(r,t)` is an event of the raw past at `t`. -/
theorem measurableSet_nonzero_rawPast {Ω : Type*} [MeasurableSpace Ω] {nL nR : ℕ}
    (Y : Ω → HistorySpace nL nR) (r t : ℝ≥0) :
    MeasurableSet[samplePastSigma Y t]
      {ω | ∃ p, r < dyadicTime p ∧ dyadicTime p < t ∧ (Y ω).2 p ≠ 0} := by
  let : MeasurableSpace Ω := samplePastSigma Y t
  rw [ofPred_exists]
  apply MeasurableSet.iUnion
  intro p
  by_cases hc : r < dyadicTime p ∧ dyadicTime p < t
  · simpa only [hc.1, hc.2, true_and, Set.compl_ofPred] using
      (measurableSet_eq_fun (measurable_sample_rawPast Y p hc.2.le) measurable_const).compl
  · have he : {ω | r < dyadicTime p ∧ dyadicTime p < t ∧ (Y ω).2 p ≠ 0} = (∅ : Set Ω) := by
      ext ω
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false]
      exact fun h => hc ⟨h.1, h.2.1⟩
    rw [he]
    exact MeasurableSet.empty

/-- Earlier survival is exactly the existence of a later nonzero raw sample,
provided every strictly live interval has such a sample. -/
theorem lt_lifetime_iff_nonzero_rawPast {Ω : Type*} {nL nR : ℕ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞} {ω : Ω}
    (hn : ∀ a c : ℝ≥0, a < c → (c : ℝ≥0∞) < V ω →
      ∃ p, a < dyadicTime p ∧ dyadicTime p < c ∧ (killedHistory W VL VR V ω).2 p ≠ 0)
    {r t : ℝ≥0} (hrt : r < t) :
    (r : ℝ≥0∞) < V ω ↔ ∃ p, r < dyadicTime p ∧ dyadicTime p < t ∧
      (killedHistory W VL VR V ω).2 p ≠ 0 := by
  constructor
  · intro hrV
    obtain ⟨c, hrc, hc⟩ := ENNReal.lt_iff_exists_nnreal_btwn.1
      (lt_min hrV (ENNReal.coe_lt_coe.2 hrt))
    obtain ⟨p, hrp, hpc, hp0⟩ := hn r c (ENNReal.coe_lt_coe.1 hrc) (lt_min_iff.1 hc).1
    exact ⟨p, hrp, hpc.trans (ENNReal.coe_lt_coe.1 (lt_min_iff.1 hc).2), hp0⟩
  · rintro ⟨p, hrp, _, hp0⟩
    have hpV : (dyadicTime p : ℝ≥0∞) < V ω := by
      by_contra h
      exact hp0 (by simp only [killedHistory, h, ↓reduceIte])
    exact (ENNReal.coe_lt_coe.2 hrp).trans hpV

/-- Survival past an earlier time belongs to the completed later raw past. -/
theorem measurableSet_live_rawPast
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {nL nR : ℕ}
    {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {V : Ω → ℝ≥0∞}
    (hX : IsMeasurableKilledDriving W VL VR V)
    (hn : ∀ᵐ ω ∂P, ∀ a c : ℝ≥0, a < c → (c : ℝ≥0∞) < V ω →
      ∃ p, a < dyadicTime p ∧ dyadicTime p < c ∧ (killedHistory W VL VR V ω).2 p ≠ 0)
    {r t : ℝ≥0} (hrt : r < t) :
    MeasurableSet[samplePastSigma (killedHistory W VL VR V) t ⊔ nullSigma P] {ω | (r : ℝ≥0∞) < V ω} := by
  apply ZhanGT4.A1Canon.measurableSet_of_ae_eq_of_nullSets_le
    (sup_le (samplePastSigma_le (measurable_killedHistory hX) t)
      (MeasurableSpace.generateFrom_le fun _ hs => hs.1)) le_sup_right
    (measurableSet_lt measurable_const (Restart.Aux54.isStoppingTime_lifetime_driving (P := P) hX).measurable')
    ((le_sup_left : samplePastSigma (killedHistory W VL VR V) t ≤
      samplePastSigma (killedHistory W VL VR V) t ⊔ nullSigma P) _
      (measurableSet_nonzero_rawPast (killedHistory W VL VR V) r t))
  filter_upwards [hn] with ω hω
  exact propext (lt_lifetime_iff_nonzero_rawPast hω hrt)

end InteractingSLE.WFS
