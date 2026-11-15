/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2TfMarks

/-!
# The joined future driver up to `T + d` is the joined read of the program capped at `T + d`

Packet PROVE-GW2-RELDET (`GW2TcCurve.SchedPhysCurveStatement`, time-ordered case). The explored marks must contain the
explored path on `[0, q]`. On `oldSuccess` that path is read off the records of the program capped at `q`:

* `cappedProgram c r l a d`: the history program followed by the candidate run for own time `d`;
  `cappedRead`: its joined read of its records;
* `allSucc_capped_of_oldSuccess`: the history pieces of the capped program succeed when the history did;
* **`cappedRead_eq_joinDrv`**: GEOM2's re-nesting identity (`Gm.futureJoined_eq_joinDrv`) for the capped program;
* **`futureJoined_eq_cappedRead`**: on `oldSuccess`, with good records of both programs, the joined future driver and
  the capped joined read agree on `[0, T + d]`. The candidate's canonical driver does not depend on its own time
  (`RootH29.canonical_next_independent_time`). Both stopped drivers are `D (min u ζ)` for `u ≤ d ≤ cap`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.Gm

open Exist Staged StagedLaw Restart GW2Schedule GW2Tip RootC24 Sec5.Prop513TreeExtract Sec5.Prop513Schedule

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The history program followed by the candidate run for own time `d`. -/
def cappedProgram (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (d : ℝ≥0) : List (ℝ × ℝ≥0) :=
  RootJ31.historyProgram c r l ++ [((RootJ31.candidateAngle c r a : ℝ), RootJ31.historyTime c r l + d)]

/-- The joined read of the capped program's records. -/
def cappedRead (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (d : ℝ≥0)
    (ω : Ω) : ℝ≥0 → ℝ :=
  RootJ31.joinedRead (cappedProgram c r l a d)
    (RootJ31.programRecords c (rootPt r.1) (cappedProgram c r l a d) ω)

theorem length_cappedProgram (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (d : ℝ≥0) : (cappedProgram c r l a d).length = (RootJ31.historyProgram c r l).length + 1 := by
  simp only [cappedProgram, List.length_append, List.length_singleton]

theorem lastTime_cappedProgram (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))
    (a : ℕ) (d : ℝ≥0) : lastTime 0 (cappedProgram c r l a d) = RootJ31.historyTime c r l + d := by
  rw [lastTime_eq_getLast _ _ (by simp [cappedProgram])]
  simp only [cappedProgram, List.getLast_append, List.isEmpty_cons, Bool.false_eq_true, ↓reduceDIte,
    List.getLast_singleton]

/-- **The history pieces of the capped program succeed when the history did.** -/
theorem allSucc_capped_of_oldSuccess (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (d : ℝ≥0) (ω : Ω) (hold : RootJ31.oldSuccess c r l ω) :
    AllSucc (specDelta (schedSpec (rootPt r.1) (cappedProgram c r l a d)))
      (fun j => canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h
        (schedSpec (rootPt r.1) (cappedProgram c r l a d)) j ω)
      (RootJ31.historyProgram c r l).length := by
  intro j hj
  apply (RootCv.recOf_flag_eq_false_iff _ _).mp
  change (stopRec c.hκ c.h12p c.βA c.c₀ c.h
    (schedSpec (rootPt r.1) (cappedProgram c r l a d)) j ω).2.2 = false
  rw [cappedProgram, stopRec_schedSpec_append c.hκ c.h12p c.βA c.c₀ c.h _ _ hj ω]
  exact hold ⟨j, hj⟩

/-- **The re-nesting identity for the capped program.** -/
theorem cappedRead_eq_joinDrv (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (d : ℝ≥0) (ω : Ω)
    (hord : TimeOrdered 0 (RootJ31.historyProgram c r l)) (hold : RootJ31.oldSuccess c r l ω)
    (hgood : ∀ (j : ℕ) (hj : j < (cappedProgram c r l a d).length), LocalExt.IsDrvGood
      (recHist (RootJ31.programRecords c (rootPt r.1) (cappedProgram c r l a d) ω ⟨j, hj⟩)))
    {t : ℝ≥0} (ht : t ≤ RootJ31.historyTime c r l + d) :
    cappedRead c r l a d ω t =
      Swc.joinDrv (specDelta (schedSpec (rootPt r.1) (cappedProgram c r l a d)))
        (fun j => canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h
          (schedSpec (rootPt r.1) (cappedProgram c r l a d)) j ω)
        ((RootJ31.historyProgram c r l).length + 1) t := by
  set x := rootPt r.1
  set Lf := cappedProgram c r l a d with hLf
  set Δ := specDelta (schedSpec x Lf)
  set D := fun j => canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec x Lf) j ω
  have hlen : Lf.length = (RootJ31.historyProgram c r l).length + 1 := length_cappedProgram c r l a d
  have hTl : RootJ31.historyTime c r l = lastTime 0 (RootJ31.historyProgram c r l) :=
    schedTime_length_eq_lastTime _
  have hordf : TimeOrdered 0 Lf := timeOrdered_append hord (by
    change lastTime 0 (RootJ31.historyProgram c r l) ≤ RootJ31.historyTime c r l + d
    rw [← hTl]
    exact le_add_of_nonneg_right zero_le)
  have hs := allSucc_capped_of_oldSuccess c r l a d ω hold
  have hw : ∀ j < Lf.length, ∀ u : ℝ≥0,
      ((fun j (R : Fin Lf.length → RecData) => (RootJ31.recordDriver R j, (⊤ : ℝ≥0∞))) j
        (RootJ31.programRecords c x Lf ω)).1 u = stopDrv (Δ j) (D j) u := by
    intro j hj u
    have hrd : RootJ31.recordDriver (RootJ31.programRecords c x Lf ω) j =
        fun u : ℝ≥0 => rdrv (RootJ31.programRecords c x Lf ω ⟨j, hj⟩) u := by
      simp only [RootJ31.recordDriver, hj, ↓reduceDIte]
    change RootJ31.recordDriver (RootJ31.programRecords c x Lf ω) j u = _
    rw [hrd]
    have he : IsRegularDriver (D j) :=
      isRegularDriver_canonDrive c.hκ c.h12p c.βA c.c₀ x _ _ (c.h ω) j
    exact congrFun (recDrv_eq_stopDrv he (hgood j hj)) u
  have hT : ∀ k < Lf.length, Swc.joinTime Δ D k = schedTime 0 Lf k := fun k hk =>
    joinTime_eq_schedTime x hordf hk.le (hs.mono (by omega))
  have hlast : t ≤ lastTime 0 Lf := by rw [lastTime_cappedProgram]; exact ht
  have h := joinedDriver_eq_joinDrv (fun j (R : Fin Lf.length → RecData) =>
    (RootJ31.recordDriver R j, (⊤ : ℝ≥0∞))) (RootJ31.programRecords c x Lf ω) Lf hordf
    (fun j => RootJ31.recordDriver_zero _ j) hw hT hlast
  have hJ : Swc.joinDrv Δ D Lf.length = Swc.joinDrv Δ D ((RootJ31.historyProgram c r l).length + 1) :=
    congrArg (Swc.joinDrv Δ D) hlen
  exact h.trans (congrFun hJ t)

/-- **On `oldSuccess`, the joined future driver and the capped joined read agree up to `T + d`.** -/
theorem futureJoined_eq_cappedRead (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) {d : ℝ≥0} (hdcap : d ≤ RootJ31.candidateCap c r a) (ω : Ω)
    (hord : TimeOrdered 0 (RootJ31.historyProgram c r l)) (hold : RootJ31.oldSuccess c r l ω)
    (hgoodf : ∀ (j : ℕ) (hj : j < (RootJ31.futureProgram c r l a).length), LocalExt.IsDrvGood
      (recHist (RootJ31.programRecords c (rootPt r.1) (RootJ31.futureProgram c r l a) ω ⟨j, hj⟩)))
    (hgood : ∀ (j : ℕ) (hj : j < (cappedProgram c r l a d).length), LocalExt.IsDrvGood
      (recHist (RootJ31.programRecords c (rootPt r.1) (cappedProgram c r l a d) ω ⟨j, hj⟩)))
    {t : ℝ≥0} (ht : t ≤ RootJ31.historyTime c r l + d) :
    futureJoined c r l a ω t = cappedRead c r l a d ω t := by
  set x := rootPt r.1
  set θ : ℝ := (RootJ31.candidateAngle c r a : ℝ)
  set T := RootJ31.historyTime c r l with hT
  set Lh := RootJ31.historyProgram c r l with hLh
  set m := Lh.length with hm
  set L' := cappedProgram c r l a d with hL'
  set Δ' := specDelta (schedSpec x L')
  set D' := fun j => canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec x L') j ω
  set Δh := specDelta (schedSpec x Lh)
  set Dh := fun j => canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec x Lh) j ω
  set Lf := RootJ31.futureProgram c r l a with hLf
  set Δf := specDelta (schedSpec x Lf)
  set Df := fun j => canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec x Lf) j ω
  have hsh : AllSucc Δh Dh m := (RootJ31.oldSuccess_iff_allSucc c r l ω).mp hold
  have hΔ'h : ∀ j < m, Δ' j = Δh j := fun j hj => specDelta_schedSpec_append x _ hj
  have hD'h : ∀ j < m, D' j = Dh j := fun j hj =>
    RootC11.canonSpecFam_append c.hκ c.h12p c.βA c.c₀ c.h x _ hj ω
  have hΔfh : ∀ j < m, Δf j = Δh j := fun j hj => specDelta_schedSpec_append x _ hj
  have hDfh : ∀ j < m, Df j = Dh j := fun j hj =>
    RootC11.canonSpecFam_append c.hκ c.h12p c.βA c.c₀ c.h x _ hj ω
  have hJTh : Swc.joinTime Δh Dh m = (T : ℝ) := joinTime_eq_schedTime x hord le_rfl hsh
  have hJm' : Swc.joinTime Δ' D' m = (T : ℝ) := (joinTime_congr hΔ'h hD'h).trans hJTh
  have hJmf : Swc.joinTime Δf Df m = (T : ℝ) := (joinTime_congr hΔfh hDfh).trans hJTh
  have hJDm : Swc.joinDrv Δf Df m = Swc.joinDrv Δ' D' m :=
    (joinDrv_congr hΔfh hDfh).trans (joinDrv_congr hΔ'h hD'h).symm
  have hDm : Df m = D' m :=
    RootH29.canonical_next_independent_time c.hκ c.h12p c.βA c.c₀ c.h x θ Lh
      (T + RootJ31.candidateCap c r a) (T + d) ω
  have hΔfm : Δf m = (RootJ31.candidateCap c r a : ℝ≥0∞) := RootJ31.futureProgram_delta c r l a
  have hΔ'm : Δ' m = ((T + d - T : ℝ≥0) : ℝ≥0∞) := RootH29.specDelta_last x θ Lh (T + d)
  rw [add_tsub_cancel_left] at hΔ'm
  have hcap : t ≤ T + RootJ31.candidateCap c r a := ht.trans (add_le_add le_rfl hdcap)
  rw [futureJoined_eq_joinDrv c r l a ω hord hold hgoodf hcap, cappedRead_eq_joinDrv c r l a d ω hord hold hgood ht]
  change (if (t : ℝ) ≤ Swc.joinTime Δf Df m then Swc.joinDrv Δf Df m t else
      Swc.joinDrv Δf Df m (Swc.joinTime Δf Df m) +
        stopDrv (Δf m) (Df m) (t - Swc.joinTime Δf Df m)) =
    (if (t : ℝ) ≤ Swc.joinTime Δ' D' m then Swc.joinDrv Δ' D' m t else
      Swc.joinDrv Δ' D' m (Swc.joinTime Δ' D' m) +
        stopDrv (Δ' m) (D' m) (t - Swc.joinTime Δ' D' m))
  rw [hJmf, hJm', hJDm]
  by_cases htT : (t : ℝ) ≤ T
  · rw [ite_eq_left htT, ite_eq_left htT]
  · rw [ite_eq_right htT, ite_eq_right htT]
    congr 1
    -- both stopped drivers read the same driver at `min u ζ`
    have hu : ((((t : ℝ) - T).toNNReal : ℝ≥0) : ℝ≥0∞) ≤ (d : ℝ≥0∞) := by
      have h1 : (t : ℝ) - T ≤ d := by
        have := (NNReal.coe_le_coe.2 ht)
        push_cast at this
        linarith
      exact ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 h1)
    change (Df m).1 (min ((((t : ℝ) - T).toNNReal : ℝ≥0) : ℝ≥0∞) (min (Δf m) (Df m).2)).toNNReal =
      (D' m).1 (min ((((t : ℝ) - T).toNNReal : ℝ≥0) : ℝ≥0∞) (min (Δ' m) (D' m).2)).toNNReal
    rw [hDm, hΔfm, hΔ'm, ← min_assoc, ← min_assoc, min_eq_left hu,
      min_eq_left (hu.trans (ENNReal.coe_le_coe.2 hdcap))]

end InteractingSLE.Theorem14.GW2TipSystem.Gm
