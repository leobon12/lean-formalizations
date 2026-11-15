/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentGRule

/-!
# The own record's driving state up to the restart time: a countable continuity certificate

Packet PROVE-AUX61-R1CHART. R1's restart chart (`Aux61Restart.HasOriginalTargetRestartChart`) is read from the own
record stopped at the rational restart time `q`, a point of `HistorySpace nL nR` (the state at the dyadic times `≤ q`,
`0` after). The state read from the record (`histState`, the limit of the samples at the dyadic times below `t`) is
continuous on `[0, q]` as soon as the samples at the dyadic times `≤ q` are uniformly continuous; this is a countable
condition (`StateCert q`, a Borel set of records, `measurableSet_stateCert`). On it:

* `StateCert.tendsto`: the samples below `t ≤ q` converge to `histState γ t`;
* `StateCert.continuousOn`: `histState γ` is continuous on `[0, q]`;
* `frozenDrv q γ t = (histState γ (min t q)).1`, the driver read from the record and frozen at `q`, is continuous and
  starts at `0` (`StateCert.continuous_frozenDrv`, `StateCert.frozenDrv_zero`); it is measurable in the record
  (`measurable_frozenDrv`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology Metric
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Aux61R1C

open LawUnique Restart.FlowStopIdentG

variable {nL nR : ℕ}

/-- **The state certificate up to `q`**: the driver sample at the index `(0, 0)` is `0`, and the state samples at the
dyadic times `≤ q` are uniformly continuous in the dyadic time (a countable condition). -/
def StateCert (q : ℝ≥0) (γ : HistorySpace nL nR) : Prop :=
  (γ.2 (0, 0)).1 = 0 ∧ ∀ m : ℕ, ∃ k : ℕ, ∀ p p' : ℕ × ℕ, dyadicTime p ≤ q → dyadicTime p' ≤ q →
    dist (dyadicTime p) (dyadicTime p') < 1 / ((k : ℝ) + 1) → dist (γ.2 p) (γ.2 p') ≤ 1 / ((m : ℝ) + 1)

theorem measurableSet_stateCert (q : ℝ≥0) : MeasurableSet {γ : HistorySpace nL nR | StateCert q γ} := by
  have hev : ∀ p : ℕ × ℕ, Measurable fun γ : HistorySpace nL nR => γ.2 p :=
    fun p => (measurable_pi_apply p).comp measurable_snd
  refine MeasurableSet.inter (measurableSet_eq_fun (measurable_fst.comp (hev _)) measurable_const) ?_
  refine measurableSet_setOfPred.2 (Measurable.forall fun m => Measurable.exists fun k =>
    Measurable.forall fun p => Measurable.forall fun p' => ?_)
  refine Measurable.imp measurable_const (Measurable.imp measurable_const (Measurable.imp measurable_const ?_))
  exact measurableSet_setOfPred.1 (measurableSet_le ((hev p).dist (hev p')) measurable_const)

/-- The driver read from a record, frozen at `q`. -/
def frozenDrv (q : ℝ≥0) (γ : HistorySpace nL nR) (t : ℝ≥0) : ℝ := (histState γ (min t q)).1

theorem measurable_frozenDrv (q t : ℝ≥0) : Measurable fun γ : HistorySpace nL nR => frozenDrv q γ t :=
  measurable_fst.comp (measurable_histState _)

theorem measurable_frozenDrv_pi (q : ℝ≥0) : Measurable fun γ : HistorySpace nL nR => frozenDrv q γ :=
  measurable_pi_iff.2 (measurable_frozenDrv q)

theorem frozenDrv_of_le {q t : ℝ≥0} (ht : t ≤ q) (γ : HistorySpace nL nR) :
    frozenDrv q γ t = (histState γ t).1 := by
  rw [frozenDrv, min_eq_left ht]

variable {q : ℝ≥0} {γ : HistorySpace nL nR}

/-- On a certified record the samples below a time `t ≤ q` are Cauchy. -/
theorem StateCert.cauchySeq (hγ : StateCert q γ) {t : ℝ≥0} (ht : t ≤ q) :
    CauchySeq fun n => γ.2 (lowerDyadic t n) := by
  rw [Metric.cauchySeq_iff']
  intro ε hε
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  obtain ⟨k, hk⟩ := hγ.2 m
  obtain ⟨n₁, hn₁⟩ := Metric.cauchySeq_iff.1 (tendsto_dyadicTime_lowerDyadic t).cauchySeq
    (1 / ((k : ℝ) + 1)) (by positivity)
  have hle : ∀ n, dyadicTime (lowerDyadic t n) ≤ q := fun n => (dyadicTime_lowerDyadic_le t n).trans ht
  exact ⟨n₁, fun n hn => lt_of_le_of_lt (hk _ _ (hle n) (hle n₁) (hn₁ n hn n₁ le_rfl)) hm⟩

/-- On a certified record the samples below `t ≤ q` converge to the state read at `t`. -/
theorem StateCert.tendsto (hγ : StateCert q γ) {t : ℝ≥0} (ht : t ≤ q) :
    Tendsto (fun n => γ.2 (lowerDyadic t n)) atTop (𝓝 (histState γ t)) :=
  (hγ.cauchySeq ht).tendsto_limUnder

/-- **On a certified record the state read from it is continuous on `[0, q]`.** -/
theorem StateCert.continuousOn (hγ : StateCert q γ) : ContinuousOn (histState γ) (Iic q) := by
  rw [Metric.continuousOn_iff]
  intro t ht ε hε
  obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
  obtain ⟨k, hk⟩ := hγ.2 m
  refine ⟨1 / ((k : ℝ) + 1), by positivity, fun t' ht' hdist => ?_⟩
  have hle : ∀ u : ℝ≥0, u ≤ q → ∀ n, dyadicTime (lowerDyadic u n) ≤ q := fun u hu n =>
    (dyadicTime_lowerDyadic_le u n).trans hu
  have hd : ∀ᶠ n in atTop, dist (dyadicTime (lowerDyadic t' n)) (dyadicTime (lowerDyadic t n)) <
      1 / ((k : ℝ) + 1) :=
    ((tendsto_dyadicTime_lowerDyadic t').dist (tendsto_dyadicTime_lowerDyadic t)).eventually (gt_mem_nhds hdist)
  have hev : ∀ᶠ n in atTop, dist (γ.2 (lowerDyadic t' n)) (γ.2 (lowerDyadic t n)) ≤ 1 / ((m : ℝ) + 1) := by
    filter_upwards [hd] with n hn
    exact hk _ _ (hle t' ht' n) (hle t ht n) hn
  have hlim := le_of_tendsto ((hγ.tendsto ht').dist (hγ.tendsto ht)) hev
  exact lt_of_le_of_lt hlim hm

/-- **On a certified record the driver read at time `0` is `0`.** -/
theorem StateCert.state_zero (hγ : StateCert q γ) : (histState γ 0).1 = 0 := by
  have hconst : ∀ n, γ.2 (lowerDyadic 0 n) = γ.2 (0, 0) := by
    intro n
    have hl : lowerDyadic 0 n = (n, 0) := by simp [lowerDyadic]
    rw [hl]
    have ht : ∀ p : ℕ × ℕ, p.2 = 0 → dyadicTime p = 0 := fun p hp => by simp [dyadicTime, hp]
    refine eq_of_forall_dist_le fun ε hε => ?_
    obtain ⟨m, hm⟩ := exists_nat_one_div_lt hε
    obtain ⟨k, hk⟩ := hγ.2 m
    have h := hk (n, 0) (0, 0) (by rw [ht _ rfl]; exact zero_le) (by rw [ht _ rfl]; exact zero_le)
      (by rw [ht (n, 0) rfl, ht (0, 0) rfl, dist_self]; positivity)
    exact h.trans hm.le
  have h := hγ.tendsto (zero_le : (0 : ℝ≥0) ≤ q)
  simp only [hconst] at h
  rw [tendsto_nhds_unique h tendsto_const_nhds, hγ.1]

/-- **The frozen driver of a certified record is continuous.** -/
theorem StateCert.continuous_frozenDrv (hγ : StateCert q γ) : Continuous (frozenDrv q γ) :=
  (continuous_fst.comp_continuousOn hγ.continuousOn).comp_continuous (continuous_id.min continuous_const)
    fun t => min_le_right t q

/-- **The frozen driver of a certified record starts at `0`.** -/
theorem StateCert.frozenDrv_zero (hγ : StateCert q γ) : frozenDrv q γ 0 = 0 := by
  rw [frozenDrv_of_le (zero_le : (0 : ℝ≥0) ≤ q)]
  exact hγ.state_zero

end InteractingSLE.Sec5.Aux61R1C
