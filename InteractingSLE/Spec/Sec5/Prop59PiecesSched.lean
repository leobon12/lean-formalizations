/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop513ScheduleExtract
import InteractingSLE.Spec.Sec5.Prop59PiecesCand

/-!
# The schedules of the candidate pieces in Proposition 5.13's tree

Packet PROVE-PROP59-PIECES. Specification §5.2, proof of Proposition 5.9 (p. 146): "Every successful finite prefix
uses angles in `Θ` and original switching times in `Q`. Although the selected indices depend on the revealed history,
the set of all possible finite lists is countable." The candidate `(j, t)` of the alternating construction
(`Prop59PiecesCand`) is the flow line of PROVE-PROP513C's tree whose switches happen at the original times decoded
from the clock values `t` (`decode x = x/(1 − x)`; rational clock values give rational original times), with the
extreme angles alternating `+π/2, −π/2, …` (stage `j` heads left when `j` is even, PROVE-PROP59T2's `farGap`), and
which continues at its last angle.

* `stageFlag`, `ratVal`, `oTime`, `IsValid`, `lastO`: the angle flag of a stage (`true` is `+π/2`), the rational
  original time of a rational clock value, admissible lists (strictly increasing rational clock values in `(0, 1)`)
  and the original time of the last switch;
* `schedList`, **`mkSched`**: the schedule with the switches of `t` and the end time `v` of its last piece;
  `candSched` (end time `lastO + 1`, the candidate) and `mkSched j t u` for a rational `u > lastO` (its truncation at
  `u`, a node of the tree);
* `instr_lt_mkSched`, `instrAngle_mkSched`: two such schedules have the same instructions before the last piece and the
  same angle at it.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Prop59Pieces

open Prop513TreeExtract Prop513Schedule Exist.StagedLaw Exist.Staged

/-! ### Admissible lists -/

/-- The angle flag of stage `i` (`true` is `+π/2`: even stages head left). -/
def stageFlag (i : ℕ) : Bool := decide (Even i)

open scoped Classical in
/-- The rational value of a rational clock value (`0` otherwise). -/
def ratVal (x : ℝ≥0) : ℚ := if h : ∃ q : ℚ, (x : ℝ) = q then h.choose else 0

theorem ratVal_spec {x : ℝ≥0} (h : ∃ q : ℚ, (x : ℝ) = q) : ((ratVal x : ℚ) : ℝ) = x := by
  classical
  simp only [ratVal, h, ↓reduceDIte]
  exact h.choose_spec.symm

/-- The rational original time `x/(1 − x)` of a rational clock value. -/
def oTime (x : ℝ≥0) : ℚ := ratVal x / (1 - ratVal x)

theorem oTime_eq {x : ℝ≥0} (h : ∃ q : ℚ, (x : ℝ) = q) : ((oTime x : ℚ) : ℝ) = decode x := by
  rw [oTime, Rat.cast_div, Rat.cast_sub, Rat.cast_one, ratVal_spec h, decode]

theorem decode_strictMono {x y : ℝ≥0} (hy : y < 1) (hxy : x < y) : decode x < decode y := by
  have hy' : (y : ℝ) < 1 := by exact_mod_cast hy
  have hx' : (x : ℝ) < y := by exact_mod_cast hxy
  have hx0 : (0 : ℝ) ≤ x := x.coe_nonneg
  unfold decode
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

theorem decode_pos {x : ℝ≥0} (h0 : 0 < x) (h1 : x < 1) : 0 < decode x := by
  have h1' : (x : ℝ) < 1 := by exact_mod_cast h1
  exact div_pos (by exact_mod_cast h0) (by linarith)

/-- **An admissible list**: strictly increasing rational clock values in `(0, 1)`. -/
def IsValid (j : ℕ) (t : Fin j → ℝ≥0) : Prop :=
  StrictMono t ∧ ∀ i, 0 < t i ∧ t i < 1 ∧ ∃ q : ℚ, (t i : ℝ) = q

/-- The rational original time of the last switch (`0` for the empty list). -/
def lastO : (j : ℕ) → (Fin j → ℝ≥0) → ℚ
  | 0, _ => 0
  | j + 1, t => oTime (t (Fin.last j))

theorem lastO_eq {j : ℕ} {t : Fin j → ℝ≥0} (hv : IsValid j t) : ((lastO j t : ℚ) : ℝ) = qLast j t := by
  cases j with
  | zero => simp [lastO, qLast]
  | succ j => exact oTime_eq (hv.2 (Fin.last j)).2.2

theorem lastO_nonneg {j : ℕ} {t : Fin j → ℝ≥0} (hv : IsValid j t) : 0 ≤ lastO j t := by
  have h := lastO_eq hv
  cases j with
  | zero => exact le_rfl
  | succ j =>
    have : (0 : ℝ) ≤ (lastO (j + 1) t : ℝ) := by
      rw [h, qLast]; exact (decode_pos (hv.2 _).1 (hv.2 _).2.1).le
    exact_mod_cast this

theorem oTime_lt_oTime {j : ℕ} {t : Fin j → ℝ≥0} (hv : IsValid j t) {i i' : Fin j} (h : i < i') :
    oTime (t i) < oTime (t i') := by
  have h1 := oTime_eq (hv.2 i).2.2
  have h2 := oTime_eq (hv.2 i').2.2
  have : ((oTime (t i) : ℚ) : ℝ) < oTime (t i') := by
    rw [h1, h2]; exact decode_strictMono (hv.2 i').2.1 (hv.1 h)
  exact_mod_cast this

theorem oTime_le_lastO {j : ℕ} {t : Fin j → ℝ≥0} (hv : IsValid j t) (i : Fin j) : oTime (t i) ≤ lastO j t := by
  cases j with
  | zero => exact i.elim0
  | succ j =>
    rcases (Fin.le_last i).eq_or_lt with h | h
    · rw [h]; exact le_rfl
    · exact (oTime_lt_oTime hv h).le

theorem oTime_pos {j : ℕ} {t : Fin j → ℝ≥0} (hv : IsValid j t) (i : Fin j) : 0 < oTime (t i) := by
  have h := oTime_eq (hv.2 i).2.2
  have : (0 : ℝ) < (oTime (t i) : ℝ) := by rw [h]; exact decode_pos (hv.2 i).1 (hv.2 i).2.1
  exact_mod_cast this

/-- The parent of an admissible list is admissible. -/
theorem IsValid.init {j : ℕ} {t : Fin (j + 1) → ℝ≥0} (hv : IsValid (j + 1) t) : IsValid j (Fin.init t) :=
  ⟨fun _ _ h => hv.1 (Fin.castSucc_lt_castSucc_iff.2 h), fun _ => hv.2 _⟩

theorem qLast_init_le {j : ℕ} {t : Fin (j + 1) → ℝ≥0} (hv : IsValid (j + 1) t) :
    qLast j (Fin.init t) ≤ qLast (j + 1) t := by
  cases j with
  | zero => exact decode_nonneg (hv.2 _).2.1
  | succ j =>
    exact (decode_strictMono (hv.2 _).2.1 (hv.1 (Fin.castSucc_lt_last (Fin.last j)))).le

/-! ### The schedules -/

/-- The switch entries of a list: stage `i` ends at the original time of `t i`. -/
def entries (j : ℕ) (t : Fin j → ℝ≥0) : List (Bool × ℚ) := List.ofFn fun i : Fin j => (stageFlag i, oTime (t i))

/-- The schedule list with the switches of `t` and the end time `v` of the last piece. -/
def schedList (j : ℕ) (t : Fin j → ℝ≥0) (v : ℚ) : List (Bool × ℚ) := entries j t ++ [(stageFlag j, v)]

theorem isSchedule_schedList {j : ℕ} {t : Fin j → ℝ≥0} {v : ℚ} (hv : IsValid j t) (hlt : lastO j t < v) :
    schedList j t v ≠ [] ∧ (∀ p ∈ schedList j t v, 0 < p.2) ∧
      (schedList j t v).Pairwise (fun p r => p.2 < r.2) := by
  have hv0 : 0 < v := (lastO_nonneg hv).trans_lt hlt
  refine ⟨by simp [schedList], fun p hp => ?_, ?_⟩
  · rcases List.mem_append.1 hp with hp | hp
    · obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hp
      exact oTime_pos hv i
    · rw [List.mem_singleton.1 hp]; exact hv0
  · refine List.pairwise_append.2 ⟨List.pairwise_ofFn.2 fun i i' h => oTime_lt_oTime hv h,
      List.pairwise_singleton _ _, fun p hp r hr => ?_⟩
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hp
    rw [List.mem_singleton.1 hr]
    exact (oTime_le_lastO hv i).trans_lt hlt

open scoped Classical in
/-- **The schedule with the switches of `t` and last end time `v`** (the basic schedule if `t` is not admissible or
`v` is not after the last switch). -/
def mkSched (j : ℕ) (t : Fin j → ℝ≥0) (v : ℚ) : Schedule :=
  if h : IsValid j t ∧ lastO j t < v then ⟨schedList j t v, isSchedule_schedList h.1 h.2⟩ else basicSchedule

/-- **The candidate's schedule**: last piece ending one unit after the last switch (it is continued). -/
def candSched (j : ℕ) (t : Fin j → ℝ≥0) : Schedule := mkSched j t (lastO j t + 1)

theorem mkSched_val {j : ℕ} {t : Fin j → ℝ≥0} {v : ℚ} (hv : IsValid j t) (hlt : lastO j t < v) :
    (mkSched j t v).1 = schedList j t v := by
  classical
  simp only [mkSched, hv, hlt, and_self, ↓reduceDIte]

theorem terminal_mkSched {j : ℕ} {t : Fin j → ℝ≥0} {v : ℚ} (hv : IsValid j t) (hlt : lastO j t < v) :
    terminal (mkSched j t v) = (v : ℝ).toNNReal := by
  simp [terminal, terminalRat, mkSched_val hv hlt, schedList]

/-- The real-angle list of a schedule `mkSched`: the entries, then the last piece. -/
theorem scheduleList_mkSched {j : ℕ} {t : Fin j → ℝ≥0} {v : ℚ} (hv : IsValid j t) (hlt : lastO j t < v) :
    scheduleList (mkSched j t v) = (entries j t).map (fun p => (if p.1 then Real.pi / 2 else -(Real.pi / 2),
      (p.2 : ℝ).toNNReal)) ++ [(if stageFlag j then Real.pi / 2 else -(Real.pi / 2), (v : ℝ).toNNReal)] := by
  simp only [scheduleList, mkSched_val hv hlt, schedList, List.map_append, List.map_cons, List.map_nil]

theorem length_entries (j : ℕ) (t : Fin j → ℝ≥0) : (entries j t).length = j := List.length_ofFn

/-- **Two schedules `mkSched j t v`, `mkSched j t v'` have the same instructions before the last piece.** -/
theorem instr_lt_mkSched {j : ℕ} {t : Fin j → ℝ≥0} {v v' : ℚ} (hv : IsValid j t) (hlt : lastO j t < v)
    (hlt' : lastO j t < v') {k : ℕ} (hk : k < j) :
    (scheduleSpec (mkSched j t v)).2.2[k]? = (scheduleSpec (mkSched j t v')).2.2[k]? := by
  simp only [scheduleSpec, scheduleList_mkSched hv hlt, scheduleList_mkSched hv hlt', scheduleProgram_append]
  have hk' : k < (scheduleProgram 0 ((entries j t).map (fun p => (if p.1 then Real.pi / 2 else -(Real.pi / 2),
      (p.2 : ℝ).toNNReal)))).length := by
    rw [length_scheduleProgram, List.length_map, length_entries]; exact hk
  rw [List.getElem?_append_left hk', List.getElem?_append_left hk']

/-- **Two schedules `mkSched j t v`, `mkSched j t v'` have the same angle at the last piece.** -/
theorem instrAngle_mkSched {j : ℕ} {t : Fin j → ℝ≥0} {v v' : ℚ} (hv : IsValid j t) (hlt : lastO j t < v)
    (hlt' : lastO j t < v') :
    instrAngle (scheduleSpec (mkSched j t v)) j = instrAngle (scheduleSpec (mkSched j t v')) j := by
  have hlen : (scheduleProgram 0 ((entries j t).map (fun p => (if p.1 then Real.pi / 2 else -(Real.pi / 2),
      (p.2 : ℝ).toNNReal)))).length = j := by
    rw [length_scheduleProgram, List.length_map, length_entries]
  simp only [instrAngle, scheduleSpec, scheduleList_mkSched hv hlt, scheduleList_mkSched hv hlt',
    scheduleProgram_append]
  rw [List.getElem?_append_right hlen.le, List.getElem?_append_right hlen.le, hlen, Nat.sub_self]
  rfl

end InteractingSLE.Sec5.Prop59Pieces
