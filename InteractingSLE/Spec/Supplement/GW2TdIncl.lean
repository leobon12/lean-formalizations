/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2TdRun
import InteractingSLE.Spec.Supplement.GW2GmPrefix

/-!
# The physical curve of the capped program lies in the joined trace, also after the candidate's death

Packet PROVE-GW2-RELDET (`GW2TcCurve.SchedPhysCurveStatement`). PROVE-GW2-GEOM2's `Gm.prefixSet_query_eq` identifies
the physical set of the program capped at `T + d` with the joined trace on `[0, T + d]` while the candidate is ALIVE
at its own time `d`. Here the candidate may have died before `d`. Then the physical set is the joined trace up to
`T + ζ`, which lies in the trace on `[0, T + d]`:

* **`prefixSet_capped_subset`**: on `oldSuccess` (all history pieces succeeded), with the joined future records good
  and the candidate's driver continuous up to its stop `min(d, ζ)` (Theorem 1.3's piece regularity), the physical
  set of `historyProgram ++ [(θ, T + d)]` lies in `x + γ '' [0, T + d]`, for every own time `d ≤ cap`.

The proof is GEOM2's with `Swc.physSet_eq_radialTips_pred` (`GW2TdRun`) in place of the all-success version and the
join time `T + min(d, ζ) ≤ T + d`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.Gm

open Exist Staged StagedLaw Restart GW2Schedule GW2Tip RootC24 Sec5.Prop513TreeExtract Sec5.Prop513Schedule

variable {Ω : Type u} [MeasurableSpace Ω]

/-- **The physical curve of the program capped at `T + d` lies in the joined trace on `[0, T + d]`.** -/
theorem prefixSet_capped_subset (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω)
    (hord : TimeOrdered 0 (RootJ31.historyProgram c r l)) (hold : RootJ31.oldSuccess c r l ω)
    (hgood : ∀ (j : ℕ) (hj : j < (RootJ31.futureProgram c r l a).length), LocalExt.IsDrvGood
      (recHist (RootJ31.programRecords c (rootPt r.1) (RootJ31.futureProgram c r l a) ω ⟨j, hj⟩)))
    {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace (futureJoined c r l a ω) ⊤ γ) {d : ℝ≥0}
    (hdcap : d ≤ RootJ31.candidateCap c r a)
    (hcm : ContinuousOn (canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec (rootPt r.1)
        (RootJ31.historyProgram c r l ++ [((RootJ31.candidateAngle c r a : ℝ), RootJ31.historyTime c r l + d)]))
        (RootJ31.historyProgram c r l).length ω).1
      {s | (s : ℝ≥0∞) ≤ min (specDelta (schedSpec (rootPt r.1)
        (RootJ31.historyProgram c r l ++ [((RootJ31.candidateAngle c r a : ℝ), RootJ31.historyTime c r l + d)]))
          (RootJ31.historyProgram c r l).length)
        (canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec (rootPt r.1)
          (RootJ31.historyProgram c r l ++ [((RootJ31.candidateAngle c r a : ℝ), RootJ31.historyTime c r l + d)]))
          (RootJ31.historyProgram c r l).length ω).2}) :
    prefixSet c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h (rootPt r.1)
        (RootJ31.historyProgram c r l ++ [((RootJ31.candidateAngle c r a : ℝ), RootJ31.historyTime c r l + d)]) ω ⊆
      (fun z => (rootPt r.1 : ℂ) + z) '' (γ '' Icc 0 (RootJ31.historyTime c r l + d)) := by
  set x := rootPt r.1
  set θ : ℝ := (RootJ31.candidateAngle c r a : ℝ)
  set T := RootJ31.historyTime c r l with hT
  set q := T + d with hq
  set Lh := RootJ31.historyProgram c r l with hLh
  set m := Lh.length with hm
  set L' := Lh ++ [(θ, q)] with hL'
  set Δ' := specDelta (schedSpec x L')
  set D' := fun j => canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec x L') j ω
  set Δh := specDelta (schedSpec x Lh)
  set Dh := fun j => canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec x Lh) j ω
  set Lf := RootJ31.futureProgram c r l a with hLf
  set Δf := specDelta (schedSpec x Lf)
  set Df := fun j => canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec x Lf) j ω
  have hsh : AllSucc Δh Dh m := (RootJ31.oldSuccess_iff_allSucc c r l ω).mp hold
  have hlen' : (schedSpec x L').2.2.length = m + 1 :=
    (GW2Schedule.length_scheduleProgram 0 L').trans
      (by rw [hL', List.length_append, List.length_singleton])
  have hΔ'h : ∀ j < m, Δ' j = Δh j := fun j hj => specDelta_schedSpec_append x _ hj
  have hD'h : ∀ j < m, D' j = Dh j := fun j hj =>
    RootC11.canonSpecFam_append c.hκ c.h12p c.βA c.c₀ c.h x _ hj ω
  have hΔfh : ∀ j < m, Δf j = Δh j := fun j hj => specDelta_schedSpec_append x _ hj
  have hDfh : ∀ j < m, Df j = Dh j := fun j hj =>
    RootC11.canonSpecFam_append c.hκ c.h12p c.βA c.c₀ c.h x _ hj ω
  have hs'm : AllSucc Δ' D' m := fun j hj => by rw [hΔ'h j hj, hD'h j hj]; exact hsh j hj
  have hc' : ∀ i < m + 1, Continuous (stopDrv (Δ' i) (D' i)) ∧ stopDrv (Δ' i) (D' i) 0 = 0 := by
    intro i hi
    rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
    · exact continuous_stopDrv_of_lt (isRegularDriver_canonDrive c.hκ c.h12p c.βA c.c₀ x _ _ (c.h ω) i)
        (hs'm i hi) (specDelta_ne_top _ i)
    · exact Swc.continuous_stopDrv_of_continuousOn
        (isRegularDriver_canonDrive c.hκ c.h12p c.βA c.c₀ x _ _ (c.h ω) _)
        (ne_top_of_le_ne_top (specDelta_ne_top _ _) (min_le_left _ _)) hcm
  have hphys : ExplState.physSet c.κ c.b c.jumps (schedSpec x L') D' =
      (fun z => (x : ℂ) + z) '' Swc.radialTips (Swc.joinDrv Δ' D' (m + 1)) 0
        (Swc.joinTime Δ' D' (m + 1)) := by
    have h := Swc.physSet_eq_radialTips_pred (κ := c.κ) (b := c.b) (jumps := c.jumps)
      (spec := schedSpec x L') (D := D') rfl (isFlowProg_spec x true L') (specDelta_ne_top _)
      (by rw [hlen']; omega) (by rw [hlen', Nat.add_sub_cancel]; exact hs'm) (by rw [hlen']; exact hc')
    rw [hlen'] at h
    exact h
  obtain ⟨hJ, hJ0⟩ := Swc.continuous_joinDrv hc'
  obtain ⟨hW, hW0⟩ := continuous_futureJoined c r l a ω
  -- the switching time after the history, for both programs
  have hJTh : Swc.joinTime Δh Dh m = (T : ℝ) := joinTime_eq_schedTime x hord le_rfl hsh
  have hJm' : Swc.joinTime Δ' D' m = (T : ℝ) := (joinTime_congr hΔ'h hD'h).trans hJTh
  have hJmf : Swc.joinTime Δf Df m = (T : ℝ) := (joinTime_congr hΔfh hDfh).trans hJTh
  have hJDm : Swc.joinDrv Δf Df m = Swc.joinDrv Δ' D' m :=
    (joinDrv_congr hΔfh hDfh).trans (joinDrv_congr hΔ'h hD'h).symm
  -- the last piece: same canonical driver; the capped stop is below the full one
  have hDm : Df m = D' m :=
    RootH29.canonical_next_independent_time c.hκ c.h12p c.βA c.c₀ c.h x θ Lh
      (T + RootJ31.candidateCap c r a) q ω
  have hΔfm : Δf m = (RootJ31.candidateCap c r a : ℝ≥0∞) := RootJ31.futureProgram_delta c r l a
  have hΔ'm : Δ' m = ((q - T : ℝ≥0) : ℝ≥0∞) := RootH29.specDelta_last x θ Lh q
  have hqT : q - T = d := add_tsub_cancel_left T d
  rw [hqT] at hΔ'm
  -- the join time of the capped program is at most `q`
  have hJ1 : Swc.joinTime Δ' D' (m + 1) = T + stopTime (Δ' m) (D' m) := by
    rw [Swc.joinTime_succ, hJm']
  have hstop : stopTime (Δ' m) (D' m) ≤ d := by
    unfold stopTime
    rw [hΔ'm]
    have h1 : ((min (d : ℝ≥0∞) (D' m).2).toNNReal : ℝ≥0) ≤ d := by
      simpa only [ENNReal.toNNReal_coe] using
        ENNReal.toNNReal_mono ENNReal.coe_ne_top (min_le_left (d : ℝ≥0∞) (D' m).2)
    exact_mod_cast h1
  have hJle : Swc.joinTime Δ' D' (m + 1) ≤ (q : ℝ) := by
    rw [hJ1, hq, NNReal.coe_add]
    linarith
  have hag : ∀ t : ℝ≥0, (t : ℝ) ≤ Swc.joinTime Δ' D' (m + 1) →
      futureJoined c r l a ω t = Swc.joinDrv Δ' D' (m + 1) t := by
    intro t ht
    have htq : t ≤ q := by exact_mod_cast ht.trans hJle
    have hcap : t ≤ T + RootJ31.candidateCap c r a := htq.trans (add_le_add le_rfl hdcap)
    have h1 : futureJoined c r l a ω t = Swc.joinDrv Δf Df (m + 1) t :=
      futureJoined_eq_joinDrv c r l a ω hord hold hgood hcap
    rw [h1]
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
      -- `t − T` is below the capped stop, hence below both stops
      have hle : ((((t : ℝ) - T).toNNReal : ℝ≥0) : ℝ≥0∞) ≤ min (Δ' m) (D' m).2 := by
        rw [hJ1] at ht
        have h2 : (t : ℝ) - T ≤ stopTime (Δ' m) (D' m) := by linarith
        have h3 : ((t : ℝ) - T).toNNReal ≤ (min (Δ' m) (D' m).2).toNNReal :=
          Real.toNNReal_le_iff_le_coe.2 h2
        have hne : min (Δ' m) (D' m).2 ≠ ⊤ := ne_top_of_le_ne_top (by rw [hΔ'm]; exact ENNReal.coe_ne_top)
          (min_le_left _ _)
        calc ((((t : ℝ) - T).toNNReal : ℝ≥0) : ℝ≥0∞) ≤ ((min (Δ' m) (D' m).2).toNNReal : ℝ≥0∞) :=
              ENNReal.coe_le_coe.2 h3
          _ = min (Δ' m) (D' m).2 := ENNReal.coe_toNNReal hne
      have hlef : ((((t : ℝ) - T).toNNReal : ℝ≥0) : ℝ≥0∞) ≤ min (Δf m) (Df m).2 := by
        rw [hΔfm, hDm]
        refine hle.trans (min_le_min ?_ le_rfl)
        rw [hΔ'm]
        exact ENNReal.coe_le_coe.2 hdcap
      rw [stopDrv_eq_of_le hlef, stopDrv_eq_of_le hle, hDm]
  change ExplState.physSet c.κ c.b c.jumps (schedSpec x L') D' ⊆ _
  rw [hphys, SwC.radialTips_eq_image hJ hJ0 hW hW0 hγ (Swc.joinTime_nonneg Δ' D' _) hag]
  refine image_mono (image_mono (Icc_subset_Icc le_rfl ?_))
  exact Real.toNNReal_le_iff_le_coe.2 hJle

end InteractingSLE.Theorem14.GW2TipSystem.Gm
