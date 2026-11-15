/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop59PiecesQPath

/-!
# The schedules of a node experiment: the node's prefix of switches, then the alternating angles

Packet PROVE-PROP59-NODETREE. Specification §5.2, proof of Proposition 5.13 (p. 151): "The extreme-angle version of
Proposition 5.9 gives `L_z = η'([0, T_z])`" — Proposition 5.9 run with the allowed stopped prefix `(η, σ)` of the node
`z` as its initial flow-line exploration (p. 143). The candidate paths of the node experiment follow the node's own
schedule (arbitrary extreme angles, PROVE-PROP59-NODES §5.1) and then the alternating construction, which starts at
the angle `+π/2` at the node's terminal time.

* `entriesF`, `schedListF`, **`mkSchedF`**, `candSchedF`: PROVE-PROP59-PIECES' schedules with an arbitrary sequence
  of angle flags `fl` (`true` is `+π/2`); the root experiment is the case `fl = stageFlag`;
* `enc q = q/(1 + q)`: the clock value of the rational original time `q` (`oTime_enc`);
* `nodeLen s`, `nodePre s`, **`nodeFlag s`**: the node prefix of a schedule `s` as `nodeLen s` switches (one at the end
  of each of its pieces, the last one at its terminal time), and the flags: those of `s`, then `stageFlag (k − m)`;
* `NodeValid s`: the admissible lists of the node tree (prefixes and extensions of `nodePre s`);
* **`isValid_nodePre`**, **`entriesF_nodePre`** (the node prefix is the schedule `s`), `lastO_nodePre`;
* **`isPrefix_mkSchedF`**, `terminal_le_mkSchedF`: every truncated extension is a descendant of `s`.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.Prop59NodeTree

open Prop513TreeExtract Prop513Schedule Exist.StagedLaw Exist.Staged Prop59Pieces

/-! ### Schedules with arbitrary angle flags -/

section Flags

variable (fl : ℕ → Bool)

/-- The switch entries of a list with the flags `fl`: piece `i` has angle flag `fl i` and ends at `oTime (t i)`. -/
def entriesF (j : ℕ) (t : Fin j → ℝ≥0) : List (Bool × ℚ) := List.ofFn fun i : Fin j => (fl i, oTime (t i))

/-- The schedule list with the switches of `t`, the flags `fl` and the end time `v` of the last piece. -/
def schedListF (j : ℕ) (t : Fin j → ℝ≥0) (v : ℚ) : List (Bool × ℚ) := entriesF fl j t ++ [(fl j, v)]

theorem length_entriesF (j : ℕ) (t : Fin j → ℝ≥0) : (entriesF fl j t).length = j := List.length_ofFn

theorem isSchedule_schedListF {j : ℕ} {t : Fin j → ℝ≥0} {v : ℚ} (hv : IsValid j t) (hlt : lastO j t < v) :
    schedListF fl j t v ≠ [] ∧ (∀ p ∈ schedListF fl j t v, 0 < p.2) ∧
      (schedListF fl j t v).Pairwise (fun p r => p.2 < r.2) := by
  have hv0 : 0 < v := (lastO_nonneg hv).trans_lt hlt
  refine ⟨by simp [schedListF], fun p hp => ?_, ?_⟩
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
/-- **The schedule with the switches of `t`, the flags `fl` and last end time `v`** (the basic schedule if `t` is
not admissible or `v` is not after the last switch). -/
def mkSchedF (j : ℕ) (t : Fin j → ℝ≥0) (v : ℚ) : Schedule :=
  if h : IsValid j t ∧ lastO j t < v then ⟨schedListF fl j t v, isSchedule_schedListF fl h.1 h.2⟩
  else basicSchedule

/-- **The candidate's schedule**: last piece ending one unit after the last switch (it is continued). -/
def candSchedF (j : ℕ) (t : Fin j → ℝ≥0) : Schedule := mkSchedF fl j t (lastO j t + 1)

variable {fl}

theorem mkSchedF_val {j : ℕ} {t : Fin j → ℝ≥0} {v : ℚ} (hv : IsValid j t) (hlt : lastO j t < v) :
    (mkSchedF fl j t v).1 = schedListF fl j t v := by
  classical
  simp only [mkSchedF, hv, hlt, and_self, ↓reduceDIte]

theorem terminal_mkSchedF {j : ℕ} {t : Fin j → ℝ≥0} {v : ℚ} (hv : IsValid j t) (hlt : lastO j t < v) :
    terminal (mkSchedF fl j t v) = (v : ℝ).toNNReal := by
  simp [terminal, terminalRat, mkSchedF_val hv hlt, schedListF]

/-- The real-angle list of a schedule `mkSchedF`: the entries, then the last piece. -/
theorem scheduleList_mkSchedF {j : ℕ} {t : Fin j → ℝ≥0} {v : ℚ} (hv : IsValid j t) (hlt : lastO j t < v) :
    scheduleList (mkSchedF fl j t v) = (entriesF fl j t).map gmap ++ [gmap (fl j, v)] := by
  simp only [scheduleList, mkSchedF_val hv hlt, schedListF, List.map_append, List.map_cons, List.map_nil]
  rfl

theorem entriesF_succ (j : ℕ) (t : Fin (j + 1) → ℝ≥0) :
    entriesF fl (j + 1) t = entriesF fl j (Fin.init t) ++ [(fl j, oTime (t (Fin.last j)))] := by
  simp only [entriesF, List.ofFn_succ', List.concat_eq_append, Fin.val_castSucc, Fin.val_last, Fin.init]

/-- **Two schedules `mkSchedF j t v`, `mkSchedF j t v'` have the same instructions before the last piece.** -/
theorem instr_lt_mkSchedF {j : ℕ} {t : Fin j → ℝ≥0} {v v' : ℚ} (hv : IsValid j t) (hlt : lastO j t < v)
    (hlt' : lastO j t < v') {k : ℕ} (hk : k < j) :
    (scheduleSpec (mkSchedF fl j t v)).2.2[k]? = (scheduleSpec (mkSchedF fl j t v')).2.2[k]? := by
  simp only [scheduleSpec, scheduleList_mkSchedF hv hlt, scheduleList_mkSchedF hv hlt', scheduleProgram_append]
  have hk' : k < (scheduleProgram 0 ((entriesF fl j t).map gmap)).length := by
    rw [length_scheduleProgram, List.length_map, length_entriesF]; exact hk
  rw [List.getElem?_append_left hk', List.getElem?_append_left hk']

/-- **Two schedules `mkSchedF j t v`, `mkSchedF j t v'` have the same angle at the last piece.** -/
theorem instrAngle_mkSchedF {j : ℕ} {t : Fin j → ℝ≥0} {v v' : ℚ} (hv : IsValid j t) (hlt : lastO j t < v)
    (hlt' : lastO j t < v') :
    instrAngle (scheduleSpec (mkSchedF fl j t v)) j = instrAngle (scheduleSpec (mkSchedF fl j t v')) j := by
  have hlen : (scheduleProgram 0 ((entriesF fl j t).map gmap)).length = j := by
    rw [length_scheduleProgram, List.length_map, length_entriesF]
  simp only [instrAngle, scheduleSpec, scheduleList_mkSchedF hv hlt, scheduleList_mkSchedF hv hlt',
    scheduleProgram_append]
  rw [List.getElem?_append_right hlen.le, List.getElem?_append_right hlen.le, hlen, Nat.sub_self]
  rfl

end Flags

/-! ### Clock values of rational original times -/

/-- **The clock value `q/(1 + q)`** of a rational original time `q`. -/
def enc (q : ℚ) : ℝ≥0 := ((q / (1 + q) : ℚ) : ℝ).toNNReal

theorem enc_coe {q : ℚ} (hq : 0 ≤ q) : ((enc q : ℝ≥0) : ℝ) = ((q / (1 + q) : ℚ) : ℝ) :=
  Real.coe_toNNReal _ (by exact_mod_cast div_nonneg hq (by linarith))

theorem oTime_enc {q : ℚ} (hq : 0 ≤ q) : oTime (enc q) = q := by
  have hr : ratVal (enc q) = q / (1 + q) := by
    have h := ratVal_spec (x := enc q) ⟨q / (1 + q), enc_coe hq⟩
    rw [enc_coe hq] at h
    exact_mod_cast h
  have h1 : (1 + q) ≠ 0 := by linarith
  rw [oTime, hr]
  field_simp
  ring

theorem enc_lt_one {q : ℚ} (hq : 0 ≤ q) : enc q < 1 := by
  rw [← NNReal.coe_lt_coe, enc_coe hq, NNReal.coe_one]
  have h : q / (1 + q) < 1 := (div_lt_one (by linarith)).2 (by linarith)
  exact_mod_cast h

theorem enc_pos {q : ℚ} (hq : 0 < q) : 0 < enc q := by
  rw [← NNReal.coe_lt_coe, enc_coe hq.le, NNReal.coe_zero]
  have h : 0 < q / (1 + q) := div_pos hq (by linarith)
  exact_mod_cast h

theorem enc_strictMono {q q' : ℚ} (hq : 0 ≤ q) (hqq : q < q') : enc q < enc q' := by
  rw [← NNReal.coe_lt_coe, enc_coe hq, enc_coe (hq.trans hqq.le)]
  have h : q / (1 + q) < q' / (1 + q') := by
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  exact_mod_cast h

/-- The original time of the last switch of a nonempty list. -/
theorem lastO_eq_get {j : ℕ} (t : Fin j → ℝ≥0) (hj : 0 < j) : lastO j t = oTime (t ⟨j - 1, by omega⟩) := by
  cases j with
  | zero => omega
  | succ j => rfl

/-! ### The node prefix of a schedule -/

section Node

variable (s : Schedule)

/-- The number of switches of the node prefix: one at the end of each piece of `s`. -/
def nodeLen : ℕ := s.1.length

/-- **The switching clock values of the node prefix**: the clock values of the end times of the pieces of `s`. -/
def nodePre : Fin (nodeLen s) → ℝ≥0 := fun i => enc (s.1.get i).2

/-- **The angle flags of the node tree**: the flags of the pieces of `s`, then the alternating flags of the node
experiment (`+π/2` first). -/
def nodeFlag (k : ℕ) : Bool := if h : k < s.1.length then (s.1.get ⟨k, h⟩).1 else stageFlag (k - s.1.length)

/-- **The admissible lists of the node tree**: admissible lists that are prefixes or extensions of the node
prefix. -/
def NodeValid (k : ℕ) (t : Fin k → ℝ≥0) : Prop :=
  IsValid k t ∧ ∀ (i : Fin k) (h : (i : ℕ) < nodeLen s), t i = nodePre s ⟨i, h⟩

variable {s}

theorem nodeLen_pos : 0 < nodeLen s := List.length_pos_iff.2 s.2.1

theorem nodeFlag_of_lt {k : ℕ} (hk : k < nodeLen s) : nodeFlag s k = (s.1.get ⟨k, hk⟩).1 := by
  simp only [nodeFlag, show k < s.1.length from hk, ↓reduceDIte]

theorem nodeFlag_add (j : ℕ) : nodeFlag s (nodeLen s + j) = stageFlag j := by
  simp only [nodeFlag, nodeLen, show ¬ s.1.length + j < s.1.length by omega, ↓reduceDIte, Nat.add_sub_cancel_left]

theorem time_pos (i : Fin (nodeLen s)) : 0 < (s.1.get i).2 := s.2.2.1 _ (List.get_mem _ _)

theorem time_lt {i i' : Fin (nodeLen s)} (h : i < i') : (s.1.get i).2 < (s.1.get i').2 :=
  List.pairwise_iff_get.1 s.2.2.2 i i' h

theorem oTime_nodePre (i : Fin (nodeLen s)) : oTime (nodePre s i) = (s.1.get i).2 := oTime_enc (time_pos i).le

/-- **The node prefix is admissible.** -/
theorem isValid_nodePre : IsValid (nodeLen s) (nodePre s) :=
  ⟨fun _ _ h => enc_strictMono (time_pos _).le (time_lt h), fun i =>
    ⟨enc_pos (time_pos i), enc_lt_one (time_pos i).le, _, enc_coe (time_pos i).le⟩⟩

theorem nodeValid_nodePre : NodeValid s (nodeLen s) (nodePre s) := ⟨isValid_nodePre, fun _ _ => rfl⟩

/-- **The entries of the node prefix are the schedule `s`.** -/
theorem entriesF_nodePre : entriesF (nodeFlag s) (nodeLen s) (nodePre s) = s.1 := by
  refine List.ext_getElem (by rw [length_entriesF]; rfl) fun k h₁ h₂ => ?_
  have hk : k < nodeLen s := h₂
  simp only [entriesF, List.getElem_ofFn]
  rw [nodeFlag_of_lt hk, oTime_nodePre]
  rfl

/-- **The last switch of the node prefix is the terminal time of `s`.** -/
theorem lastO_nodePre : lastO (nodeLen s) (nodePre s) = terminalRat s := by
  rw [lastO_eq_get _ nodeLen_pos, oTime_nodePre, terminalRat, List.getLast_eq_getElem]
  rfl

theorem NodeValid.isValid {k : ℕ} {t : Fin k → ℝ≥0} (h : NodeValid s k t) : IsValid k t := h.1

/-- The parent of a node-admissible list is node-admissible. -/
theorem NodeValid.init {k : ℕ} {t : Fin (k + 1) → ℝ≥0} (h : NodeValid s (k + 1) t) : NodeValid s k (Fin.init t) :=
  ⟨h.1.init, fun i hi => h.2 (Fin.castSucc i) hi⟩

/-- A node-admissible list of length at least the node prefix extends it, so its last switch is not earlier. -/
theorem NodeValid.lastO_le {k : ℕ} {t : Fin k → ℝ≥0} (h : NodeValid s k t) (hk : nodeLen s ≤ k) :
    terminalRat s ≤ lastO k t := by
  have hm := nodeLen_pos (s := s)
  have e := h.2 ⟨nodeLen s - 1, by omega⟩ (by simp only; omega)
  have h1 := oTime_le_lastO h.1 ⟨nodeLen s - 1, by omega⟩
  rw [e] at h1
  rw [← lastO_nodePre, lastO_eq_get _ nodeLen_pos]
  exact h1

/-- At most the node length, a node-admissible list is the node prefix up to its length. -/
theorem NodeValid.eq_nodePre {t : Fin (nodeLen s) → ℝ≥0} (h : NodeValid s (nodeLen s) t) : t = nodePre s :=
  funext fun i => h.2 i i.2

/-- **The entries of an extension begin with the schedule `s`.** -/
theorem isPrefix_entriesF {k : ℕ} {t : Fin k → ℝ≥0} (h : NodeValid s k t) (hk : nodeLen s ≤ k) :
    s.1.IsPrefix (entriesF (nodeFlag s) k t) := by
  rw [List.prefix_iff_eq_take]
  refine List.ext_getElem (by rw [List.length_take, length_entriesF]; exact (min_eq_left hk).symm) fun i h₁ h₂ => ?_
  have hi : i < nodeLen s := h₁
  rw [List.getElem_take]
  simp only [entriesF, List.getElem_ofFn]
  rw [h.2 ⟨i, by omega⟩ hi]
  have e := congrArg (fun l => l[i]?) (entriesF_nodePre (s := s))
  simp only [entriesF, List.getElem?_ofFn] at e
  rw [List.getElem?_eq_getElem h₁] at e
  simp only [hi, ↓reduceDIte, Option.some.injEq] at e
  exact e.symm

/-- **Every truncated extension is a descendant of `s`**: its list begins with `s`. -/
theorem isPrefix_mkSchedF {k : ℕ} {t : Fin k → ℝ≥0} {v : ℚ} (h : NodeValid s k t) (hk : nodeLen s ≤ k)
    (hlt : lastO k t < v) : s.1.IsPrefix (mkSchedF (nodeFlag s) k t v).1 := by
  rw [mkSchedF_val h.1 hlt, schedListF]
  exact (isPrefix_entriesF h hk).trans (List.prefix_append _ _)

theorem terminal_le_mkSchedF {k : ℕ} {t : Fin k → ℝ≥0} {v : ℚ} (h : NodeValid s k t) (hk : nodeLen s ≤ k)
    (hlt : lastO k t < v) : terminal s ≤ terminal (mkSchedF (nodeFlag s) k t v) := by
  rw [terminal_mkSchedF h.1 hlt, terminal]
  exact Real.toNNReal_le_toNNReal (by exact_mod_cast ((h.lastO_le hk).trans hlt.le))

/-- The descendant of `s` given by a truncated extension. -/
def descOf {k : ℕ} {t : Fin k → ℝ≥0} {v : ℚ} (h : NodeValid s k t) (hk : nodeLen s ≤ k) (hlt : lastO k t < v) :
    Descendant s :=
  ⟨mkSchedF (nodeFlag s) k t v, isPrefix_mkSchedF h hk hlt, terminal_le_mkSchedF h hk hlt⟩

end Node

end InteractingSLE.Sec5.Prop59NodeTree
