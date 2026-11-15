/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.StagedS4Sched
import InteractingSLE.Spec.Sec5.Prop59NodeTreePath
import InteractingSLE.Spec.Sec5.Prop59NodeTreeWord

/-!
# The schedule family of a candidate with arbitrary angle flags (deterministic)

Packet PROVE-STAGED-NODECOMP. PROVE-STAGED-S4's `StagedS4Sched` for PROVE-PROP59-NODETREE's flag schedules
`mkSchedF fl ℓ t v` (piece `i` at angle `flagAngle (fl i)`): for an admissible list `t` of depth `ℓ` and a rational
`v` after its last switch,

* `ℓ + 1` pieces (`schedL_mkSchedF`), angles independent of `v` (`schedAngle_mkSchedF`), first angle
  `flagAngle (fl 0)` (`schedAngle_mkSchedF_zero`);
* switch times `startT … (j + 1) = oTime (t j)` (`startT_schedD_mkSchedF`), end of piece `ℓ` at `v`
  (`cumT_schedD_mkSchedF`);
* joined driver of its code drivers equal to the flag candidate's continued driver `qDrvF fl ℓ t`
  (`joinProc_mkSchedF_eq_qDrvF`).

Deterministic; no probability. R48: nothing here uses Theorem 1.2/1.3.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Sec5.CrossCond.StagedNComp

open Exist.Staged Exist.StagedLaw Sec7.AdmCode Prop513TreeExtract Prop513Schedule StagedGlue StagedDepth
open Prop59Pieces Prop59NodeTree StagedS4
open Theorem14.GW2Schedule (schedTime schedDelta schedAngle)
open InteractingSLE.Sec5.CrossCond.Staged (catN cumT)
open StagedFinal (startN startT cumT_eq_startN coe_startN)

/-! ### The schedules `mkSchedF fl ℓ t v` -/

section Sched

variable {fl : ℕ → Bool} {ℓ : ℕ} {t : Fin ℓ → ℝ≥0} {v v' : ℚ}

theorem gmap_fst (p : Bool × ℚ) : (gmap p).1 = flagAngle p.1 := rfl

theorem length_scheduleList_mkSchedF (hv : IsValid ℓ t) (hlt : lastO ℓ t < v) :
    (scheduleList (mkSchedF fl ℓ t v)).length = ℓ + 1 := by
  rw [scheduleList_mkSchedF hv hlt, List.length_append, List.length_map, length_entriesF, List.length_singleton]

theorem schedL_mkSchedF (hv : IsValid ℓ t) (hlt : lastO ℓ t < v) : schedL (mkSchedF fl ℓ t v) = ℓ + 1 := by
  rw [schedL_eq, length_scheduleList_mkSchedF hv hlt]

theorem getD_scheduleList_mkSchedF_lt (hv : IsValid ℓ t) (hlt : lastO ℓ t < v) {j : ℕ} (hj : j < ℓ) :
    (scheduleList (mkSchedF fl ℓ t v)).getD j (0, 0) = gmap (fl j, oTime (t ⟨j, hj⟩)) := by
  have hlen : ((entriesF fl ℓ t).map gmap).length = ℓ := by rw [List.length_map, length_entriesF]
  rw [scheduleList_mkSchedF hv hlt, List.getD_eq_getElem _ _ (by simp [length_entriesF]; omega),
    List.getElem_append_left (by rw [hlen]; exact hj), List.getElem_map]
  simp [entriesF]

theorem getD_scheduleList_mkSchedF_last (hv : IsValid ℓ t) (hlt : lastO ℓ t < v) :
    (scheduleList (mkSchedF fl ℓ t v)).getD ℓ (0, 0) = gmap (fl ℓ, v) := by
  have hlen : ((entriesF fl ℓ t).map gmap).length = ℓ := by rw [List.length_map, length_entriesF]
  rw [scheduleList_mkSchedF hv hlt, List.getD_eq_getElem _ _ (by simp [length_entriesF]),
    List.getElem_append_right (by rw [hlen])]
  simp [hlen]

/-- **Two schedules `mkSchedF fl ℓ t v`, `mkSchedF fl ℓ t v'` have the same angles.** -/
theorem schedAngle_mkSchedF (hv : IsValid ℓ t) (hlt : lastO ℓ t < v) (hlt' : lastO ℓ t < v') :
    schedAngle (scheduleList (mkSchedF fl ℓ t v)) = schedAngle (scheduleList (mkSchedF fl ℓ t v')) := by
  funext j
  simp only [schedAngle]
  rcases lt_trichotomy j ℓ with hj | rfl | hj
  · rw [getD_scheduleList_mkSchedF_lt hv hlt hj, getD_scheduleList_mkSchedF_lt hv hlt' hj]
  · rw [getD_scheduleList_mkSchedF_last hv hlt, getD_scheduleList_mkSchedF_last hv hlt']
    rfl
  · rw [List.getD_eq_default _ _ (by rw [length_scheduleList_mkSchedF hv hlt]; omega),
      List.getD_eq_default _ _ (by rw [length_scheduleList_mkSchedF hv hlt']; omega)]

/-- **The angle of piece `j ≤ ℓ` of `mkSchedF fl ℓ t v` is `flagAngle (fl j)`.** -/
theorem schedAngle_mkSchedF_of_le (hv : IsValid ℓ t) (hlt : lastO ℓ t < v) {j : ℕ} (hj : j ≤ ℓ) :
    schedAngle (scheduleList (mkSchedF fl ℓ t v)) j = flagAngle (fl j) := by
  simp only [schedAngle]
  rcases hj.lt_or_eq with hj | rfl
  · rw [getD_scheduleList_mkSchedF_lt hv hlt hj]; rfl
  · rw [getD_scheduleList_mkSchedF_last hv hlt]; rfl

/-- **The first angle of `mkSchedF fl ℓ t v` is `flagAngle (fl 0)`.** -/
theorem schedAngle_mkSchedF_zero (hv : IsValid ℓ t) (hlt : lastO ℓ t < v) :
    schedAngle (scheduleList (mkSchedF fl ℓ t v)) 0 = flagAngle (fl 0) :=
  schedAngle_mkSchedF_of_le hv hlt (Nat.zero_le _)

/-- **The switch times of `mkSchedF fl ℓ t v`**: piece `j + 1` starts at `oTime (t j)`. -/
theorem startN_schedD_mkSchedF (hv : IsValid ℓ t) (hlt : lastO ℓ t < v) {j : ℕ} (hj : j < ℓ) :
    startN (schedD (mkSchedF fl ℓ t v)) (j + 1) = ((oTime (t ⟨j, hj⟩) : ℚ) : ℝ).toNNReal := by
  rw [startN_schedD _ (j + 1) (by rw [length_scheduleList_mkSchedF hv hlt]; omega)]
  change ((scheduleList (mkSchedF fl ℓ t v)).getD j (0, 0)).2 = _
  rw [getD_scheduleList_mkSchedF_lt hv hlt hj]
  rfl

theorem startT_schedD_mkSchedF (hv : IsValid ℓ t) (hlt : lastO ℓ t < v) {j : ℕ} (hj : j < ℓ) :
    startT (fun i => (schedD (mkSchedF fl ℓ t v) i : ℝ)) (j + 1) = ((oTime (t ⟨j, hj⟩) : ℚ) : ℝ) := by
  rw [← coe_startN, startN_schedD_mkSchedF hv hlt hj,
    Real.coe_toNNReal _ (by exact_mod_cast (oTime_pos hv _).le)]

/-- **Piece `ℓ` of `mkSchedF fl ℓ t v` ends at `v`.** -/
theorem cumT_schedD_mkSchedF (hv : IsValid ℓ t) (hlt : lastO ℓ t < v) :
    cumT (schedD (mkSchedF fl ℓ t v)) ℓ = (v : ℝ).toNNReal := by
  rw [cumT_eq_startN, startN_schedD _ (ℓ + 1) (by rw [length_scheduleList_mkSchedF hv hlt])]
  change ((scheduleList (mkSchedF fl ℓ t v)).getD ℓ (0, 0)).2 = _
  rw [getD_scheduleList_mkSchedF_last hv hlt]
  rfl

theorem coe_cumT_schedD_mkSchedF (hv : IsValid ℓ t) (hlt : lastO ℓ t < v) :
    ((cumT (schedD (mkSchedF fl ℓ t v)) ℓ : ℝ≥0) : ℝ) = v := by
  rw [cumT_schedD_mkSchedF hv hlt, Real.coe_toNNReal _ (by exact_mod_cast ((lastO_nonneg hv).trans hlt.le))]

end Sched

/-! ### The joined driver of the code drivers is the flag candidate's continued driver -/

section Join

variable (h44 : Theorem12ParamCond44Statement.{u}) {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) (c : Restart.BoundaryWord)
  {Ω : Type*} (F : Ω → LQGMetric.DistOn upperHalfPlaneOpens) (fl : ℕ → Bool)

/-- Code drivers of two schedules `mkSchedF fl ℓ t v`, `mkSchedF fl ℓ t v'` agree on the pieces `0, …, ℓ`. -/
theorem codeFam_mkSchedF_eq {ℓ : ℕ} {t : Fin ℓ → ℝ≥0} {v v' : ℚ} (hv : IsValid ℓ t) (hlt : lastO ℓ t < v)
    (hlt' : lastO ℓ t < v') {i : ℕ} (hi : i ≤ ℓ) (ω : Ω) :
    codeFam h44 hκ hκ4 c F (mkSchedF fl ℓ t v) i ω = codeFam h44 hκ hκ4 c F (mkSchedF fl ℓ t v') i ω := by
  set A := (entriesF fl ℓ t).map gmap with hA
  have hlenA : A.length = ℓ := by rw [hA, List.length_map, length_entriesF]
  have hL : scheduleList (mkSchedF fl ℓ t v) = A ++ gmap (fl ℓ, v) :: [] := scheduleList_mkSchedF hv hlt
  have hL' : scheduleList (mkSchedF fl ℓ t v') = A ++ gmap (fl ℓ, v') :: [] := scheduleList_mkSchedF hv hlt'
  obtain ⟨hpre, hang⟩ := program_agree A [] [] (gmap (fl ℓ, v)) (gmap (fl ℓ, v')) rfl
  simp only [codeFam]
  refine codeDriver_eq_of_program h44 hκ hκ4 c (F ω) (fun i' hi' => ?_) ?_
  · simp only [scheduleSpec, hL, hL']
    exact hpre i' (by omega)
  · rcases (show i < A.length ∨ i = A.length by omega) with hi' | rfl
    · unfold instrAngle; simp only [scheduleSpec, hL, hL']; rw [hpre i hi']
    · simpa only [scheduleSpec, hL, hL'] using hang

/-- **The joined driver of `mkSchedF fl ℓ t v` (code drivers) is the flag candidate's continued driver.** -/
theorem joinW_mkSchedF_eq_qDrvF {ℓ : ℕ} {t : Fin ℓ → ℝ≥0} {v : ℚ} (hv : IsValid ℓ t) (hlt : lastO ℓ t < v)
    (ω : Ω) :
    joinW (mkSchedF fl ℓ t v) (codeFam h44 hκ hκ4 c F (mkSchedF fl ℓ t v)) ω = qDrvF h44 hκ hκ4 c F fl ℓ t ω := by
  have hlt' : lastO ℓ t < lastO ℓ t + 1 := lt_add_one _
  rw [joinW_eq_continuedDriver _ _ ω fun k => (codeDriver_regular h44 hκ hκ4 c _ k (F ω)).2.1]
  unfold qDrvF candSchedF
  rw [scheduleList_mkSchedF hv hlt, scheduleList_mkSchedF hv hlt']
  refine continuedDriver_append_congr ω _ 0 0 _ _ fun i _ hi => ?_
  rw [codeFam_mkSchedF_eq h44 hκ hκ4 c F fl hv hlt hlt' (by simpa [length_entriesF] using hi) ω]

theorem joinProc_mkSchedF_eq_qDrvF {ℓ : ℕ} {t : Fin ℓ → ℝ≥0} {v : ℚ} (hv : IsValid ℓ t) (hlt : lastO ℓ t < v) :
    joinProc (mkSchedF fl ℓ t v) (Prop59Sched.schedDrivers h44 hκ hκ4 c (mkSchedF fl ℓ t v) F) =
      fun r ω => qDrvF h44 hκ hκ4 c F fl ℓ t ω r := by
  funext r ω
  exact congrFun (joinW_mkSchedF_eq_qDrvF h44 hκ hκ4 c F fl hv hlt ω) r

end Join

end InteractingSLE.Sec5.CrossCond.StagedNComp
