/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedDepthJoin
import InteractingSLE.Spec.Sec5.Prop59SchedHist

/-!
# The schedule family of a candidate (deterministic)

Packet PROVE-STAGED-S4 (§5.1 of `planning/handoffs/PROVE-STAGED-S3.md`). For PROVE-PROP59-PIECES' admissible list
`t` (depth `ℓ`) and a rational `v` after its last switch, the schedule `mkSched ℓ t v` has

* `ℓ + 1` pieces (`schedL_mkSched`), the same angles as the candidate's schedule (`schedAngle_mkSched`), first
  angle `π/2` (`schedAngle_mkSched_zero`);
* switch times `startT … (j + 1) = oTime (t j)` (`startT_schedD_mkSched`) and end of piece `ℓ` at `v`
  (`cumT_schedD_mkSched`);
* joined driver of its code drivers equal to the candidate's continued driver `qDrv ℓ t`, at every sample
  (`joinW_mkSched_eq_qDrv`): the glued objects built from `joinProc (mkSched ℓ t v) …` do not depend on `v`.

Deterministic; no probability. R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec5.CrossCond.StagedS4

open Exist.Staged Exist.StagedLaw Sec7.AdmCode Prop513TreeExtract Prop513Schedule StagedGlue StagedDepth
open Prop59Pieces
open Theorem14.GW2Schedule (schedTime schedDelta schedAngle)
open Sec7.StripSideHeightProb (catPath catPath_of_le)
open InteractingSLE.Sec5.CrossCond.Staged (catN cumT)
open StagedFinal (startN startT cumT_eq_startN coe_startN)

/-! ### Continued drivers only see the pieces up to the last and the times before it -/

section Continued

variable {Ω : Type*}

theorem continuedDriver_cons_of_ne_nil (E : ℕ → Ω → Driver) (j : ℕ) (a : ℝ≥0) (p : ℝ × ℝ≥0)
    {l : List (ℝ × ℝ≥0)} (hl : l ≠ []) (ω : Ω) :
    continuedDriver E j a (p :: l) ω = catPath (E j ω).1 (p.2 - a) (continuedDriver E (j + 1) p.2 l ω) := by
  cases l with
  | nil => exact absurd rfl hl
  | cons q l => rfl

/-- **A continued driver does not see the end time of its last piece**, nor the pieces after it. -/
theorem continuedDriver_append_congr {E E' : ℕ → Ω → Driver} (ω : Ω) :
    ∀ (A : List (ℝ × ℝ≥0)) (j : ℕ) (a : ℝ≥0) (x x' : ℝ × ℝ≥0),
      (∀ i, j ≤ i → i ≤ j + A.length → (E i ω).1 = (E' i ω).1) →
      continuedDriver E j a (A ++ [x]) ω = continuedDriver E' j a (A ++ [x']) ω
  | [], j, _, _, _, h => by
      funext t
      exact congrFun (h j le_rfl (by simp)) t
  | p :: A, j, a, x, x', h => by
      have hne : A ++ [x] ≠ [] := by simp
      have hne' : A ++ [x'] ≠ [] := by simp
      rw [List.cons_append, List.cons_append, continuedDriver_cons_of_ne_nil E j a p hne,
        continuedDriver_cons_of_ne_nil E' j a p hne' ω,
        continuedDriver_append_congr ω A (j + 1) p.2 x x' (fun i hi hi' => h i (by omega)
          (by simp only [List.length_cons] at hi' ⊢; omega)),
        h j le_rfl (by omega)]

end Continued

/-! ### The schedules `mkSched ℓ t v` -/

section Sched

variable {ℓ : ℕ} {t : Fin ℓ → ℝ≥0} {v v' : ℚ}

theorem length_scheduleList_mkSched (hv : IsValid ℓ t) (hlt : lastO ℓ t < v) :
    (scheduleList (mkSched ℓ t v)).length = ℓ + 1 := by
  rw [scheduleList_mkSched' hv hlt, List.length_append, List.length_map, length_entries, List.length_singleton]

theorem schedL_mkSched (hv : IsValid ℓ t) (hlt : lastO ℓ t < v) : schedL (mkSched ℓ t v) = ℓ + 1 := by
  rw [schedL_eq, length_scheduleList_mkSched hv hlt]

/-- The entries of the schedule list of `mkSched ℓ t v`: switch `j < ℓ` at `oTime (t j)`, the last at `v`. -/
theorem getD_scheduleList_mkSched_lt (hv : IsValid ℓ t) (hlt : lastO ℓ t < v) {j : ℕ} (hj : j < ℓ) :
    (scheduleList (mkSched ℓ t v)).getD j (0, 0) = gmap (stageFlag j, oTime (t ⟨j, hj⟩)) := by
  have hlen : ((entries ℓ t).map gmap).length = ℓ := by rw [List.length_map, length_entries]
  rw [scheduleList_mkSched' hv hlt, List.getD_eq_getElem _ _ (by simp [length_entries]; omega),
    List.getElem_append_left (by rw [hlen]; exact hj), List.getElem_map]
  simp [entries]

theorem getD_scheduleList_mkSched_last (hv : IsValid ℓ t) (hlt : lastO ℓ t < v) :
    (scheduleList (mkSched ℓ t v)).getD ℓ (0, 0) = gmap (stageFlag ℓ, v) := by
  have hlen : ((entries ℓ t).map gmap).length = ℓ := by rw [List.length_map, length_entries]
  rw [scheduleList_mkSched' hv hlt, List.getD_eq_getElem _ _ (by simp [length_entries]),
    List.getElem_append_right (by rw [hlen])]
  simp [hlen]

/-- **Two schedules `mkSched ℓ t v`, `mkSched ℓ t v'` have the same angles** (as functions of the index). -/
theorem schedAngle_mkSched (hv : IsValid ℓ t) (hlt : lastO ℓ t < v) (hlt' : lastO ℓ t < v') :
    schedAngle (scheduleList (mkSched ℓ t v)) = schedAngle (scheduleList (mkSched ℓ t v')) := by
  funext j
  simp only [schedAngle]
  rcases lt_trichotomy j ℓ with hj | rfl | hj
  · rw [getD_scheduleList_mkSched_lt hv hlt hj, getD_scheduleList_mkSched_lt hv hlt' hj]
  · rw [getD_scheduleList_mkSched_last hv hlt, getD_scheduleList_mkSched_last hv hlt']
    rfl
  · rw [List.getD_eq_default _ _ (by rw [length_scheduleList_mkSched hv hlt]; omega),
      List.getD_eq_default _ _ (by rw [length_scheduleList_mkSched hv hlt']; omega)]

/-- **The first angle of `mkSched ℓ t v` is `π/2`** (`stageFlag 0 = true`). -/
theorem schedAngle_mkSched_zero (hv : IsValid ℓ t) (hlt : lastO ℓ t < v) :
    schedAngle (scheduleList (mkSched ℓ t v)) 0 = Real.pi / 2 := by
  simp only [schedAngle]
  rcases Nat.eq_zero_or_pos ℓ with rfl | hℓ
  · rw [getD_scheduleList_mkSched_last hv hlt]
    simp [gmap, stageFlag]
  · rw [getD_scheduleList_mkSched_lt hv hlt hℓ]
    simp [gmap, stageFlag]

/-- **The switch times of `mkSched ℓ t v`**: piece `j + 1` starts at `oTime (t j)`. -/
theorem startN_schedD_mkSched (hv : IsValid ℓ t) (hlt : lastO ℓ t < v) {j : ℕ} (hj : j < ℓ) :
    startN (schedD (mkSched ℓ t v)) (j + 1) = ((oTime (t ⟨j, hj⟩) : ℚ) : ℝ).toNNReal := by
  rw [startN_schedD _ (j + 1) (by rw [length_scheduleList_mkSched hv hlt]; omega)]
  change ((scheduleList (mkSched ℓ t v)).getD j (0, 0)).2 = _
  rw [getD_scheduleList_mkSched_lt hv hlt hj]
  rfl

theorem startT_schedD_mkSched (hv : IsValid ℓ t) (hlt : lastO ℓ t < v) {j : ℕ} (hj : j < ℓ) :
    startT (fun i => (schedD (mkSched ℓ t v) i : ℝ)) (j + 1) = ((oTime (t ⟨j, hj⟩) : ℚ) : ℝ) := by
  rw [← coe_startN, startN_schedD_mkSched hv hlt hj, Real.coe_toNNReal _ (by exact_mod_cast (oTime_pos hv _).le)]

/-- **Piece `ℓ` of `mkSched ℓ t v` ends at `v`.** -/
theorem cumT_schedD_mkSched (hv : IsValid ℓ t) (hlt : lastO ℓ t < v) :
    cumT (schedD (mkSched ℓ t v)) ℓ = (v : ℝ).toNNReal := by
  rw [cumT_eq_startN, startN_schedD _ (ℓ + 1) (by rw [length_scheduleList_mkSched hv hlt])]
  change ((scheduleList (mkSched ℓ t v)).getD ℓ (0, 0)).2 = _
  rw [getD_scheduleList_mkSched_last hv hlt]
  rfl

theorem coe_cumT_schedD_mkSched (hv : IsValid ℓ t) (hlt : lastO ℓ t < v) :
    ((cumT (schedD (mkSched ℓ t v)) ℓ : ℝ≥0) : ℝ) = v := by
  rw [cumT_schedD_mkSched hv hlt, Real.coe_toNNReal _ (by exact_mod_cast ((lastO_nonneg hv).trans hlt.le))]

end Sched

/-! ### The joined driver of the code drivers is the candidate's continued driver -/

section Join

variable (h44 : Theorem12ParamCond44Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (c : Restart.BoundaryWord)
  {Ω : Type*} (F : Ω → LQGMetric.DistOn upperHalfPlaneOpens)

/-- Code drivers of two schedules `mkSched ℓ t v`, `mkSched ℓ t v'` agree on the pieces `0, …, ℓ`. -/
theorem codeFam_mkSched_eq {ℓ : ℕ} {t : Fin ℓ → ℝ≥0} {v v' : ℚ} (hv : IsValid ℓ t) (hlt : lastO ℓ t < v)
    (hlt' : lastO ℓ t < v') {i : ℕ} (hi : i ≤ ℓ) (ω : Ω) :
    codeFam h44 hκ hκ4 c F (mkSched ℓ t v) i ω = codeFam h44 hκ hκ4 c F (mkSched ℓ t v') i ω := by
  set A := (entries ℓ t).map gmap with hA
  have hlenA : A.length = ℓ := by rw [hA, List.length_map, length_entries]
  have hL : scheduleList (mkSched ℓ t v) = A ++ gmap (stageFlag ℓ, v) :: [] := scheduleList_mkSched' hv hlt
  have hL' : scheduleList (mkSched ℓ t v') = A ++ gmap (stageFlag ℓ, v') :: [] := scheduleList_mkSched' hv hlt'
  obtain ⟨hpre, hang⟩ := program_agree A [] [] (gmap (stageFlag ℓ, v)) (gmap (stageFlag ℓ, v')) rfl
  simp only [codeFam]
  refine codeDriver_eq_of_program h44 hκ hκ4 c (F ω) (fun i' hi' => ?_) ?_
  · simp only [scheduleSpec, hL, hL']
    exact hpre i' (by omega)
  · rcases (show i < A.length ∨ i = A.length by omega) with hi' | rfl
    · unfold instrAngle; simp only [scheduleSpec, hL, hL']; rw [hpre i hi']
    · simpa only [scheduleSpec, hL, hL'] using hang

/-- **The joined driver of `mkSched ℓ t v` (code drivers) is the candidate's continued driver**, at every sample. -/
theorem joinW_mkSched_eq_qDrv {ℓ : ℕ} {t : Fin ℓ → ℝ≥0} {v : ℚ} (hv : IsValid ℓ t) (hlt : lastO ℓ t < v)
    (ω : Ω) :
    joinW (mkSched ℓ t v) (codeFam h44 hκ hκ4 c F (mkSched ℓ t v)) ω = qDrv h44 hκ hκ4 c F ℓ t ω := by
  have hlt' : lastO ℓ t < lastO ℓ t + 1 := lt_add_one _
  rw [joinW_eq_continuedDriver _ _ ω fun k => (codeDriver_regular h44 hκ hκ4 c _ k (F ω)).2.1]
  unfold qDrv candSched
  rw [scheduleList_mkSched' hv hlt, scheduleList_mkSched' hv hlt']
  refine continuedDriver_append_congr ω _ 0 0 _ _ fun i _ hi => ?_
  rw [codeFam_mkSched_eq h44 hκ hκ4 c F hv hlt hlt' (by simpa [length_entries] using hi) ω]

theorem joinProc_mkSched_eq_qDrv {ℓ : ℕ} {t : Fin ℓ → ℝ≥0} {v : ℚ} (hv : IsValid ℓ t) (hlt : lastO ℓ t < v) :
    joinProc (mkSched ℓ t v) (Prop59Sched.schedDrivers h44 hκ hκ4 c (mkSched ℓ t v) F) =
      fun r ω => qDrv h44 hκ hκ4 c F ℓ t ω r := by
  funext r ω
  exact congrFun (joinW_mkSched_eq_qDrv h44 hκ hκ4 c F hv hlt ω) r

end Join

end InteractingSLE.Sec5.CrossCond.StagedS4
