/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CrossCondStagedGlueStep
import InteractingSLE.Spec.Sec5.CrossCondStagedGlueCat
import InteractingSLE.Spec.Sec5.CrossCondStagedFinalPast
import InteractingSLE.Spec.Sec5.Prop513ScheduleTrace

/-!
# The pieces of an extreme-angle schedule: the joined driver, its trace, the state's chart and the join formula

Packet PROVE-STAGED5. For the staged history `E` of an extreme-angle schedule `s` (pieces `0, …, L − 1`, own times
`schedD s j`, start times `startN (schedD s) k`), the deterministic facts of `CrossCondStagedGlueCat` are instantiated:

* bookkeeping: `instrTime_schedule`, **`schedD_pos`** (every piece runs a positive own time), `startN_schedD`,
  **`exists_nnrat_startN`** (the start times are rational, as Lemma 6.2's restart needs);
* `pieceW`, `joinW`: the piece drivers and the joined driver (the back-nested concatenation through the last piece,
  which continues after its own time); `measurable_joinW`;
* **`ae_pieces_schedule`**: almost surely every piece lives forever and has a simple generating trace in `ℍ`
  (`Prop513Schedule.ae_schedule_goodPath`, R48-safe); hence **`ae_trace_joinW`**: the joined driver has a generating
  trace on `[0, ∞)`;
* on the good event (`IsGoodSched`): **`runChart_eq_succChart`**, **`succChart_succ_eq_iterChart`** (the state's chart
  is the iterated Loewner chart of the stopped pieces), **`runChart_inv_eq`** (its inverse on `ℍ` is the centred inverse
  Loewner map of the joined driver at the start time), **`frontier_runChart`** (its domain's frontier in `ℍ` lies on the
  joined trace before the start time) and **`join_runChart`** (the join formula: after the start of piece `k` the joined
  trace is the chart image of the piece's own trace).

R48: nothing here uses Theorem 1.2/1.3; the only named input is `AdmCode.Theorem12ParamCond44Statement`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (H chiC fwdMapInv)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Sec5.CrossCond.StagedGlue

open Exist.Staged Exist.StagedLaw Sec7.AdmCode Prop513TreeExtract Prop513Schedule
open Theorem14.GW2Schedule (schedTime schedDelta schedAngle schedDelta_ne_top isFlowProg_scheduleProgram AllSucc
  succChart succChart_congr run_gw2)
open Restart (BoundaryWord)
open Restart.StagedEntrance (frozenPath)
open Sec7.StripSideHeightProb (catPath catPath_of_le)
open InteractingSLE.Sec5.CrossCond.Staged (catN cumT catChartN iterChart cumT_succ cumT_zero continuous_catN
  catN_zero continuous_rpath_of rpath_zero_of_zero iterChart_agree iterChart_dom_eq succChart_loewner_eq_iterChart)
open InteractingSLE.Sec5.CrossCond.StagedFinal (startN startN_succ)

/-! ### Bookkeeping for a schedule -/

section Book

/-- The number of pieces of a schedule. -/
abbrev schedL (s : Schedule) : ℕ := (scheduleSpec s).2.2.length

/-- The own time of piece `j` of a schedule. -/
def schedD (s : Schedule) (j : ℕ) : ℝ≥0 := (schedDelta 0 (scheduleList s) j).toNNReal

theorem schedL_eq (s : Schedule) : schedL s = (scheduleList s).length := by
  simp only [schedL, scheduleSpec, Prop513Schedule.length_scheduleProgram]

theorem schedL_pos (s : Schedule) : 0 < schedL s := by
  rw [schedL_eq]
  exact List.length_pos_of_ne_nil fun h => s.2.1 (List.map_eq_nil_iff.1 h)

theorem instrTime_schedule (s : Schedule) {j : ℕ} (hj : j < schedL s) :
    instrTime (scheduleSpec s) j = (schedD s j : ℝ≥0∞) := by
  have h := isFlowProg_scheduleProgram 0 (scheduleList s) j
    (show j < (scheduleProgram 0 (scheduleList s)).length from hj)
  simp only [instrTime, scheduleSpec] at h ⊢
  rw [h, schedD, ENNReal.coe_toNNReal (schedDelta_ne_top _ _ _)]

theorem schedTime_lt (s : Schedule) {k : ℕ} (hk : k < (scheduleList s).length) :
    schedTime 0 (scheduleList s) k < ((scheduleList s).getD k (0, 0)).2 := by
  have hS := isSchedule_scheduleList s
  cases k with
  | zero =>
    change (0 : ℝ≥0) < _
    rw [List.getD_eq_getElem _ _ hk]
    obtain ⟨q, hq, he⟩ := (hS.1 _ (List.getElem_mem hk)).2
    rw [he]
    exact Real.toNNReal_pos.2 (by exact_mod_cast hq)
  | succ j =>
    change ((scheduleList s).getD j (0, 0)).2 < _
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ hk]
    exact List.pairwise_iff_getElem.1 hS.2 j (j + 1) (by omega) hk (by omega)

theorem schedD_eq (s : Schedule) (k : ℕ) :
    schedD s k = ((scheduleList s).getD k (0, 0)).2 - schedTime 0 (scheduleList s) k := by
  simp only [schedD, schedDelta, ENNReal.toNNReal_coe]

/-- **Every piece of a schedule runs a positive own time.** -/
theorem schedD_pos (s : Schedule) {k : ℕ} (hk : k < schedL s) : 0 < schedD s k := by
  rw [schedD_eq]
  exact tsub_pos_of_lt (schedTime_lt s (by rwa [schedL_eq] at hk))

/-- The start time of piece `k` is the `k`-th schedule time. -/
theorem startN_schedD (s : Schedule) : ∀ k ≤ (scheduleList s).length,
    startN (schedD s) k = schedTime 0 (scheduleList s) k
  | 0, _ => by simp only [startN, Finset.range_zero, Finset.sum_empty]; rfl
  | k + 1, hk => by
    rw [startN_succ, startN_schedD s k (by omega), schedD_eq,
      add_tsub_cancel_of_le (schedTime_lt s (by omega)).le]
    rfl

/-- **The start times of the pieces are rational.** -/
theorem exists_nnrat_startN (s : Schedule) : ∀ k ≤ schedL s, ∃ q : ℚ≥0, (q : ℝ≥0) = startN (schedD s) k
  | 0, _ => ⟨0, by simp only [NNRat.cast_zero, startN, Finset.range_zero, Finset.sum_empty]⟩
  | k + 1, hk => by
    rw [schedL_eq] at hk
    have hk' : k < (scheduleList s).length := by omega
    rw [startN_schedD s (k + 1) hk]
    change ∃ q : ℚ≥0, (q : ℝ≥0) = ((scheduleList s).getD k (0, 0)).2
    rw [List.getD_eq_getElem _ _ hk']
    obtain ⟨q, hq, he⟩ := ((isSchedule_scheduleList s).1 _ (List.getElem_mem hk')).2
    refine ⟨⟨q, hq.le⟩, ?_⟩
    rw [he]
    ext
    rw [Real.coe_toNNReal _ (by exact_mod_cast hq.le)]
    rfl

end Book

/-! ### The piece drivers and the joined driver -/

section Join

variable {Ω : Type*}

/-- The piece drivers of a schedule (`0` past the program). -/
def pieceW (s : Schedule) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω : Ω) (j : ℕ) : ℝ≥0 → ℝ :=
  if j < schedL s then (E j ω).1 else fun _ => 0

/-- **The joined driver of a schedule**: the back-nested concatenation of the piece drivers through the last piece
(which continues after its own time). -/
def joinW (s : Schedule) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω : Ω) : ℝ≥0 → ℝ :=
  catN (pieceW s E ω) (schedD s) (schedL s - 1)

theorem pieceW_of_lt (s : Schedule) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω : Ω) {j : ℕ} (hj : j < schedL s) :
    pieceW s E ω j = (E j ω).1 := by
  simp only [pieceW, hj, ↓reduceIte]

/-- A concatenation of measurable families of drivers is measurable. -/
theorem measurable_catN_family {α : Type*} [MeasurableSpace α] {f : α → ℕ → ℝ≥0 → ℝ}
    (hf : ∀ j, Measurable fun a => f a j) (T : ℕ → ℝ≥0) : ∀ k, Measurable fun a => catN (f a) T k
  | 0 => hf 0
  | k + 1 => (Sec7.StripDet.measurable_catPath (cumT T k)).comp
      ((measurable_catN_family hf T k).prodMk (hf (k + 1)))

theorem measurable_pieceW [MeasurableSpace Ω] (s : Schedule) {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ j, Measurable (E j)) (j : ℕ) :
    Measurable fun ω => pieceW s E ω j := by
  unfold pieceW
  split_ifs
  · exact measurable_fst.comp (hE j)
  · exact measurable_const

theorem measurable_joinW [MeasurableSpace Ω] (s : Schedule) {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞}
    (hE : ∀ j, Measurable (E j)) :
    Measurable (joinW s E) :=
  measurable_catN_family (measurable_pieceW s hE) _ _

end Join

/-! ### The good event -/

section Good

/-- **The good event of a schedule**: every piece lives forever, is continuous from `0` and has a simple generating
trace in `ℍ`. -/
def IsGoodSched (s : Schedule) {Ω : Type*} (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω : Ω) : Prop :=
  ∀ j < schedL s, (E j ω).2 = ⊤ ∧ Continuous (E j ω).1 ∧ (E j ω).1 0 = 0 ∧
    ∃ η : ℝ≥0 → ℂ, IsGeneratingTrace (E j ω).1 ⊤ η ∧ ∀ t, 0 < t → η t ∈ H

variable {Ω : Type*} {s : Schedule} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {ω : Ω}

theorem IsGoodSched.pieceW_cont (hg : IsGoodSched s E ω) :
    ∀ j, Continuous (pieceW s E ω j) ∧ pieceW s E ω j 0 = 0 := by
  intro j
  by_cases hj : j < schedL s
  · rw [pieceW_of_lt s E ω hj]
    exact ⟨(hg j hj).2.1, (hg j hj).2.2.1⟩
  · have e : StagedGlue.pieceW s E ω j = fun _ => 0 := by simp only [StagedGlue.pieceW, hj, ↓reduceIte]
    rw [e]
    exact ⟨continuous_const, rfl⟩

theorem IsGoodSched.continuous_joinW (hg : IsGoodSched s E ω) : Continuous (joinW s E ω) :=
  continuous_catN (fun j => (hg.pieceW_cont j).1) (fun j => (hg.pieceW_cont j).2) _

theorem IsGoodSched.joinW_zero (hg : IsGoodSched s E ω) : joinW s E ω 0 = 0 :=
  catN_zero (fun j => (hg.pieceW_cont j).2) _

/-- On the good event the joined driver has a generating trace on `[0, ∞)`. -/
theorem IsGoodSched.exists_trace_joinW (hg : IsGoodSched s E ω) :
    ∃ α : ℝ≥0 → ℂ, IsGeneratingTrace (joinW s E ω) ⊤ α :=
  exists_isGeneratingTrace_catN (fun j => (hg.pieceW_cont j).1) (fun j => (hg.pieceW_cont j).2) _ fun j hj => by
    have hjL : j < schedL s := by have := schedL_pos s; omega
    rw [pieceW_of_lt s E ω hjL]
    exact (hg j hjL).2.2.2

theorem IsGoodSched.allSucc (hg : IsGoodSched s E ω) (k : ℕ) (hk : k ≤ schedL s) :
    AllSucc (schedDelta 0 (scheduleList s)) (fun j => E j ω) k := fun j hj => by
  rw [(hg j (by omega)).1]
  exact lt_top_iff_ne_top.2 (schedDelta_ne_top _ _ _)

variable (h44 : Theorem12ParamCond44Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4)
  {Ω' : Type u} [MeasurableSpace Ω'] [StandardBorelSpace Ω'] {P : Measure Ω'} [IsProbabilityMeasure P]
  {h : Ω' → DistOn upperHalfPlaneOpens} {E' : ℕ → Ω' → (ℝ≥0 → ℝ) × ℝ≥0∞}

include h44 hκ hκ4 in
/-- **Almost surely the schedule's history is good** (R48-safe: `Prop513Schedule.ae_schedule_goodPath`). -/
theorem ae_isGoodSched (c₀ : BoundaryWord) (hc₀ : ExtremeHeights κ c₀)
    (hh : IsGFFWithBoundaryData P h c₀.fn c₀.jumps) (s : Schedule)
    (hE : IsStagedHistory κ c₀.fn c₀.jumps P h (scheduleSpec s) E') (hreg : ∀ j ω, IsRegularDriver (E' j ω)) :
    ∀ᵐ ω ∂P, IsGoodSched s E' ω := by
  filter_upwards [ae_schedule_goodPath h44 hκ hκ4 c₀ hc₀ hh s hE hreg] with ω hg j hj
  have hgood := hg j hj
  have htop := (Sec7.StripWall.mem_goodPathSet.1 hgood).1
  have hcont := Sec7.StripWall.continuous_of_isRegularDriver (hreg j ω) htop
  have hgood' : WangWu.ImgDrv.GoodPath (E' j ω).1 ⊤ := by
    simpa only [htop] using (Sec7.StripWall.mem_goodPathSet.1 hgood)
  obtain ⟨η, hη, -, hH, -⟩ := Sec7.StripWall.exists_simple_trace_of_goodPath hcont (hreg j ω).2.1 hgood'
  exact ⟨htop, hcont, (hreg j ω).2.1, η, hη, hH⟩

end Good

/-! ### The state's chart on the good event -/

section Chart

variable {κ : ℝ} {c₀ : BoundaryWord} {s : Schedule} {Ω : Type*} {E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} {ω : Ω}

/-- The stopped piece drivers (each piece read until its own time). -/
def stopW (s : Schedule) (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω : Ω) (j : ℕ) : ℝ≥0 → ℝ :=
  fun t => pieceW s E ω j (min t (schedD s j))

theorem IsGoodSched.stopW_cont (hg : IsGoodSched s E ω) :
    ∀ j, Continuous (stopW s E ω j) ∧ stopW s E ω j 0 = 0 := fun j =>
  ⟨(hg.pieceW_cont j).1.comp (continuous_id.min continuous_const), by
    simp only [StagedGlue.stopW, zero_le, min_eq_left]; exact (hg.pieceW_cont j).2⟩

theorem catN_stopW_eq (k : ℕ) {t : ℝ≥0} (ht : t ≤ cumT (schedD s) k) :
    catN (stopW s E ω) (schedD s) k t = catN (pieceW s E ω) (schedD s) k t :=
  catN_congr_cumT (fun j _ r hr => by simp only [stopW, min_eq_left hr]) t ht

/-- **On the good event the state's chart is the iterated Loewner chart of the stopped pieces.** -/
theorem IsGoodSched.runChart_eq_succChart (hg : IsGoodSched s E ω) {k : ℕ} (hk : k ≤ schedL s) :
    runChart κ c₀ s E k ω = succChart 0 (schedDelta 0 (scheduleList s)) (fun j => E j ω) k :=
  ((run_gw2 (κ := κ) (b := c₀.fn) (jumps := c₀.jumps) (spec := scheduleSpec s) rfl
    (isFlowProg_scheduleProgram 0 (scheduleList s)) (schedDelta_ne_top 0 (scheduleList s)) (fun j => E j ω) k
    hk).1 (hg.allSucc k hk)).2

theorem IsGoodSched.stopDrv_eq (hg : IsGoodSched s E ω) {j : ℕ} (hj : j < schedL s) :
    stopDrv (schedDelta 0 (scheduleList s) j) (E j ω) = Ito.rpath (stopW s E ω j) ∧
      stopTime (schedDelta 0 (scheduleList s) j) (E j ω) = (schedD s j : ℝ) := by
  have hΔ : schedDelta 0 (scheduleList s) j = (schedD s j : ℝ≥0∞) :=
    (ENNReal.coe_toNNReal (schedDelta_ne_top _ _ _)).symm
  have hζ := (hg j hj).1
  refine ⟨funext fun x => ?_, ?_⟩
  · change (E j ω).1 (min ((x.toNNReal : ℝ≥0) : ℝ≥0∞) (min (schedDelta 0 (scheduleList s) j) (E j ω).2)).toNNReal =
      pieceW s E ω j (min x.toNNReal (schedD s j))
    rw [hζ, hΔ, min_top_right, ← ENNReal.coe_min, ENNReal.toNNReal_coe, pieceW_of_lt s E ω hj]
  · change (((min (schedDelta 0 (scheduleList s) j) (E j ω).2).toNNReal : ℝ≥0) : ℝ) = _
    rw [hζ, hΔ, min_top_right, ENNReal.toNNReal_coe]

/-- **After `k + 1` pieces the state's chart is the iterated chart of the stopped pieces `0, …, k`.** -/
theorem IsGoodSched.succChart_succ_eq_iterChart (hg : IsGoodSched s E ω) {k : ℕ} (hk : k + 1 ≤ schedL s) :
    succChart 0 (schedDelta 0 (scheduleList s)) (fun j => E j ω) (k + 1) =
      iterChart 0 (stopW s E ω) (schedD s) k := by
  obtain ⟨h1, h2⟩ := hg.stopDrv_eq (j := k) (by omega)
  change (succChart 0 (schedDelta 0 (scheduleList s)) (fun j => E j ω) k).loewner
    (stopDrv (schedDelta 0 (scheduleList s) k) (E k ω)) (stopTime (schedDelta 0 (scheduleList s) k) (E k ω)) = _
  rw [h1, h2]
  exact succChart_loewner_eq_iterChart 0 _ (fun j => E j ω) (stopW s E ω) (schedD s) k fun j hj =>
    hg.stopDrv_eq (by omega)

/-- **The inverse of the state's chart before piece `k + 1` is the centred inverse Loewner map of the joined driver
at the start time** (on `ℍ`). -/
theorem IsGoodSched.runChart_inv_eq (hg : IsGoodSched s E ω) {k : ℕ} (hk : k + 1 ≤ schedL s) {y : ℂ} (hy : y ∈ H) :
    (runChart κ c₀ s E (k + 1) ω).2.1 y = fwdMapInv (Ito.rpath (catN (pieceW s E ω) (schedD s) k))
      (cumT (schedD s) k) y := by
  have hst := hg.stopW_cont
  have hpc := hg.pieceW_cont
  rw [hg.runChart_eq_succChart hk, hg.succChart_succ_eq_iterChart hk,
    (iterChart_agree 0 (fun j => (hst j).1) (fun j => (hst j).2) k).1 y hy, catChartN_inv_eq]
  refine LP.fwdMapInv_eq_of_eqOn_Icc (continuous_rpath_of (continuous_catN (fun j => (hst j).1)
    (fun j => (hst j).2) k)) (continuous_rpath_of (continuous_catN (fun j => (hpc j).1) (fun j => (hpc j).2) k))
    (rpath_zero_of_zero (catN_zero (fun j => (hst j).2) k)) (rpath_zero_of_zero (catN_zero (fun j => (hpc j).2) k))
    (cumT (schedD s) k).coe_nonneg (fun r hr => ?_) hy
  exact catN_stopW_eq k (Real.toNNReal_le_iff_le_coe.2 hr.2)

/-- **The frontier of the state's chart domain lies on the joined trace before the start time.** -/
theorem IsGoodSched.frontier_runChart (hg : IsGoodSched s E ω) {α : ℝ≥0 → ℂ}
    (hα : IsGeneratingTrace (joinW s E ω) ⊤ α) {k : ℕ} (hk : k ≤ schedL s) :
    ∀ z ∈ H, z ∈ closure ((runChart κ c₀ s E k ω).dom : Set ℂ) → z ∉ (runChart κ c₀ s E k ω).dom →
      z ∈ α '' Icc 0 (startN (schedD s) k) := by
  intro z hz hcl hnd
  rw [hg.runChart_eq_succChart hk] at hcl hnd
  cases k with
  | zero =>
    exfalso
    apply hnd
    change z ∈ (Chart.id.recenter 0).dom
    rw [Chart.recenter_zero]
    exact Restart.StagedEntrance.Strip.mem_dom_id hz
  | succ k =>
    have hst := hg.stopW_cont
    rw [hg.succChart_succ_eq_iterChart hk] at hcl hnd
    rw [iterChart_dom_eq 0 (fun j => (hst j).1) (fun j => (hst j).2) k] at hcl hnd
    refine frontier_catChartN (fun j => (hst j).1) (fun j => (hst j).2) k hg.continuous_joinW (fun t ht => ?_) hα
      z hz hcl hnd
    rw [catN_stopW_eq k ht]
    exact catN_of_le_cumT (by omega) ht

/-- **The join formula**: on the good event, for a generating trace `α` of the joined driver and the trace `β` of
piece `k` (in `ℍ` at positive times), `α(S_k + u) = c_k⁻¹(β(u))` for `0 < u ≤ schedD s k`, `c_k` the state's chart
before piece `k` and `S_k` its start time. -/
theorem IsGoodSched.join_runChart (hg : IsGoodSched s E ω) {α : ℝ≥0 → ℂ}
    (hα : IsGeneratingTrace (joinW s E ω) ⊤ α) {k : ℕ} (hk : k < schedL s) {β : ℝ≥0 → ℂ}
    (hβ : IsGeneratingTrace (E k ω).1 ⊤ β) (hH : ∀ u, 0 < u → β u ∈ H) {u : ℝ≥0} (hu : 0 < u)
    (huk : u ≤ schedD s k) :
    α (startN (schedD s) k + u) = (runChart κ c₀ s E k ω).2.1 (β u) := by
  have hpc := hg.pieceW_cont
  cases k with
  | zero =>
    rw [hg.runChart_eq_succChart hk.le]
    change α (startN (schedD s) 0 + u) = (Chart.id.recenter 0).2.1 (β u)
    rw [Chart.recenter_zero]
    simp only [startN, Finset.range_zero, Finset.sum_empty, zero_add]
    rw [← pieceW_of_lt s E ω hk] at hβ
    exact trace_catN_zero (fun j => (hpc j).1) (fun j => (hpc j).2) hα hβ huk
  | succ k =>
    rw [hg.runChart_inv_eq (k := k) hk.le (hH u hu)]
    rw [← pieceW_of_lt s E ω hk] at hβ
    exact trace_catN_add (fun j => (hpc j).1) (fun j => (hpc j).2) (by omega) hα hβ hH hu huk

end Chart

end InteractingSLE.Sec5.CrossCond.StagedGlue
