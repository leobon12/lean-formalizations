/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2GmNest
import InteractingSLE.Spec.Supplement.GW2GmJoin
import InteractingSLE.Spec.Supplement.GW2GmClock
import InteractingSLE.Spec.Supplement.GW2SwCTips
import InteractingSLE.Spec.Supplement.GW2RootC11Prefixes
import InteractingSLE.Spec.Supplement.GW2RootJ31Alive

/-!
# The switched physical prefixes of J31 are images of the joined trace

Packet PROVE-GW2-GEOM2 (steps R3–R4). At an alive history `l` of `RootJ31.constructionFamily` whose
future records are good (`GW2GmJoin`), the joined future driver `futureJoined` (J31's back-nested
reading) is PROVE-GW2-SWITCH's front-nested driver of the canonical pieces up to the last time
(`GW2GmNest`). With SWITCH's carrier (`Swc.physSet_eq_radialTips`, `SwC.radialTips_eq_image`), the
physical prefix of the history, and of its extension by a live query `(θ, q)`, is the root translate of
the joined trace on `[0, T]`, resp. `[0, q]`:

* `pairwise_lt_historyProgram_of_alive`, `timeOrdered_historyProgram_of_alive`: alive histories are
  strictly time-ordered;
* **`futureJoined_eq_joinDrv`**: the re-nesting identity for the future program;
* **`prefixSet_history_eq`**, **`prefixSet_query_eq`**: the two prefix identifications.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.Gm

open Exist Staged StagedLaw Restart GW2Schedule GW2Tip RootC24 Sec5.Prop513TreeExtract
  Sec5.Prop513Schedule

/-! ### Time order -/

/-- Every time of a time-ordered schedule is at most its last time. -/
theorem le_lastTime_of_mem {a : ℝ≥0} :
    ∀ {L : List (ℝ × ℝ≥0)}, TimeOrdered a L → ∀ p ∈ L, p.2 ≤ lastTime a L
  | [], _, p, hp => absurd hp List.not_mem_nil
  | q :: L, hL, p, hp => by
    change p.2 ≤ lastTime q.2 L
    rcases List.mem_cons.1 hp with rfl | hp
    · exact le_lastTime (timeOrdered_tail hL)
    · exact le_lastTime_of_mem (timeOrdered_tail hL) p hp

/-- Appending a later entry keeps a schedule time-ordered. -/
theorem timeOrdered_append {L : List (ℝ × ℝ≥0)} (hL : TimeOrdered 0 L) {y : ℝ × ℝ≥0}
    (hy : lastTime 0 L ≤ y.2) : TimeOrdered 0 (L ++ [y]) := by
  refine ⟨List.pairwise_append.2 ⟨hL.1, List.pairwise_singleton _ _, fun p hp q hq => ?_⟩,
    fun _ _ => zero_le⟩
  rw [List.mem_singleton.1 hq]
  exact (le_lastTime_of_mem hL p hp).trans hy

theorem timeOrdered_of_pairwise_lt {L : List (ℝ × ℝ≥0)}
    (h : L.Pairwise (fun p q => p.2 < q.2)) : TimeOrdered 0 L :=
  ⟨h.imp fun hpq => hpq.le, fun _ _ => zero_le⟩

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- **Alive histories are strictly time-ordered**: every passed test is after the history time. -/
theorem pairwise_lt_historyProgram_of_alive (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) :
    ∀ (l : List (EntryIdx c.Θ c.Q)) (ω : Ω),
      ω ∈ (RootJ31.experiment c r).data.alive ((RootJ31.construction c).G r) l →
      (RootJ31.historyProgram c r l).Pairwise (fun p q => p.2 < q.2)
  | [], _, _ => by
    simp only [RootJ31.historyProgram, entryList, List.map_nil, schedOf, List.reverse_nil,
      List.pairwise_singleton]
  | x :: l, ω, ha => by
    obtain ⟨hprev, htest⟩ := ha
    obtain ⟨a, htest⟩ := mem_iUnion.mp htest
    obtain ⟨hang, ht⟩ := mem_iUnion.mp htest
    have ih := pairwise_lt_historyProgram_of_alive c r l ω hprev
    have hT : RootJ31.historyTime c r l < (x.2 : ℝ≥0) :=
      NNReal.coe_lt_coe.mp ((RootJ31.sourceEntry_ge_historyTime c r l a ω).trans_lt ht.1)
    have hTl : RootJ31.historyTime c r l = lastTime 0 (RootJ31.historyProgram c r l) :=
      schedTime_length_eq_lastTime _
    rw [RootJ31.historyProgram_cons]
    refine List.pairwise_append.2 ⟨ih, List.pairwise_singleton _ _, fun p hp q hq => ?_⟩
    rw [List.mem_singleton.1 hq]
    exact ((le_lastTime_of_mem (timeOrdered_of_pairwise_lt ih) p hp).trans hTl.symm.le).trans_lt hT

theorem timeOrdered_historyProgram_of_alive (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (ω : Ω)
    (ha : ω ∈ (RootJ31.experiment c r).data.alive ((RootJ31.construction c).G r) l) :
    TimeOrdered 0 (RootJ31.historyProgram c r l) :=
  timeOrdered_of_pairwise_lt (pairwise_lt_historyProgram_of_alive c r l ω ha)

/-! ### The joined future driver is the front-nested driver -/

omit [StandardBorelSpace Ω] in
/-- **The re-nesting identity for J31's future program**: on a successful, time-ordered history with
good future records, the joined future driver is the front-nested driver of the canonical pieces of the
future program, up to its last time. -/
theorem futureJoined_eq_joinDrv (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω)
    (hord : TimeOrdered 0 (RootJ31.historyProgram c r l)) (hold : RootJ31.oldSuccess c r l ω)
    (hgood : ∀ (j : ℕ) (hj : j < (RootJ31.futureProgram c r l a).length), LocalExt.IsDrvGood
      (recHist (RootJ31.programRecords c (rootPt r.1) (RootJ31.futureProgram c r l a) ω ⟨j, hj⟩)))
    {t : ℝ≥0} (ht : t ≤ RootJ31.historyTime c r l + RootJ31.candidateCap c r a) :
    futureJoined c r l a ω t =
      Swc.joinDrv (specDelta (schedSpec (rootPt r.1) (RootJ31.futureProgram c r l a)))
        (fun j => canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h
          (schedSpec (rootPt r.1) (RootJ31.futureProgram c r l a)) j ω)
        ((RootJ31.historyProgram c r l).length + 1) t := by
  set x := rootPt r.1
  set Lf := RootJ31.futureProgram c r l a with hLf
  set Δ := specDelta (schedSpec x Lf)
  set D := fun j => canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec x Lf) j ω
  have hlen : Lf.length = (RootJ31.historyProgram c r l).length + 1 := by
    simp only [hLf, RootJ31.futureProgram, List.length_append, List.length_singleton]
  have hTl : RootJ31.historyTime c r l = lastTime 0 (RootJ31.historyProgram c r l) :=
    schedTime_length_eq_lastTime _
  have hordf : TimeOrdered 0 Lf := timeOrdered_append hord (by
    change lastTime 0 (RootJ31.historyProgram c r l) ≤ RootJ31.historyTime c r l + _
    rw [← hTl]
    exact le_add_of_nonneg_right zero_le)
  have hs := allSucc_future_of_oldSuccess c r l a ω hold
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
  have hlast : t ≤ lastTime 0 Lf := by rw [lastTime_futureProgram]; exact ht
  have h := joinedDriver_eq_joinDrv (fun j (R : Fin Lf.length → RecData) =>
    (RootJ31.recordDriver R j, (⊤ : ℝ≥0∞))) (RootJ31.programRecords c x Lf ω) Lf hordf
    (fun j => RootJ31.recordDriver_zero _ j) hw hT hlast
  have hJ : Swc.joinDrv Δ D Lf.length = Swc.joinDrv Δ D ((RootJ31.historyProgram c r l).length + 1) :=
    congrArg (Swc.joinDrv Δ D) hlen
  exact h.trans (congrFun hJ t)

/-! ### The physical prefixes -/

/-- A stopped driver before its stop is the driver. -/
theorem stopDrv_eq_of_le {t : ℝ≥0∞} {e : (ℝ≥0 → ℝ) × ℝ≥0∞} {u : ℝ}
    (hu : ((u.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ min t e.2) : stopDrv t e u = e.1 u.toNNReal := by
  change e.1 (min ((u.toNNReal : ℝ≥0) : ℝ≥0∞) (min t e.2)).toNNReal = _
  rw [min_eq_left hu, ENNReal.toNNReal_coe]

/-- The stopped driver of a piece that succeeds is continuous and starts at `0`. -/
theorem continuous_stopDrv_of_lt {t : ℝ≥0∞} {e : (ℝ≥0 → ℝ) × ℝ≥0∞} (he : IsRegularDriver e)
    (ht : t < e.2) (htop : t ≠ ⊤) : Continuous (stopDrv t e) ∧ stopDrv t e 0 = 0 := by
  have hg := isDrvGood_recOf_of_lt he (r := t.toNNReal) (by rwa [ENNReal.coe_toNNReal htop])
  rw [ENNReal.coe_toNNReal htop] at hg
  rw [← recDrv_eq_stopDrv he hg]
  exact ⟨continuous_recDrv _ _, recDrv_zero _ _⟩

omit [StandardBorelSpace Ω] in
/-- **The physical prefix of a successful history is the root translate of the joined trace on
`[0, T]`**, `T` the history time. -/
theorem prefixSet_history_eq (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω)
    (hord : TimeOrdered 0 (RootJ31.historyProgram c r l)) (hold : RootJ31.oldSuccess c r l ω)
    (hgood : ∀ (j : ℕ) (hj : j < (RootJ31.futureProgram c r l a).length), LocalExt.IsDrvGood
      (recHist (RootJ31.programRecords c (rootPt r.1) (RootJ31.futureProgram c r l a) ω ⟨j, hj⟩)))
    {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace (futureJoined c r l a ω) ⊤ γ) :
    prefixSet c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h (rootPt r.1) (RootJ31.historyProgram c r l) ω =
      (fun z => (rootPt r.1 : ℂ) + z) '' (γ '' Icc 0 (RootJ31.historyTime c r l)) := by
  set x := rootPt r.1
  set Lh := RootJ31.historyProgram c r l with hLh
  set m := Lh.length with hm
  set Δh := specDelta (schedSpec x Lh)
  set Dh := fun j => canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec x Lh) j ω
  set Lf := RootJ31.futureProgram c r l a with hLf
  have hsh : AllSucc Δh Dh m := (RootJ31.oldSuccess_iff_allSucc c r l ω).mp hold
  have hlenh : (schedSpec x Lh).2.2.length = m := GW2Schedule.length_scheduleProgram 0 Lh
  have hc : ∀ i < m, Continuous (stopDrv (Δh i) (Dh i)) ∧ stopDrv (Δh i) (Dh i) 0 = 0 :=
    fun i hi => continuous_stopDrv_of_lt
      (isRegularDriver_canonDrive c.hκ c.h12p c.βA c.c₀ x _ _ (c.h ω) i) (hsh i hi)
      (specDelta_ne_top _ i)
  have hphys : ExplState.physSet c.κ c.b c.jumps (schedSpec x Lh) Dh =
      (fun z => (x : ℂ) + z) '' Swc.radialTips (Swc.joinDrv Δh Dh m) 0 (Swc.joinTime Δh Dh m) := by
    have h := Swc.physSet_eq_radialTips (κ := c.κ) (b := c.b) (jumps := c.jumps)
      (spec := schedSpec x Lh) (D := Dh) rfl (isFlowProg_spec x true Lh) (specDelta_ne_top _)
      (by rw [hlenh]; exact hsh) (by rw [hlenh]; exact hc)
    rw [hlenh] at h
    exact h
  have hJT : Swc.joinTime Δh Dh m = (RootJ31.historyTime c r l : ℝ) :=
    joinTime_eq_schedTime x hord le_rfl hsh
  obtain ⟨hJ, hJ0⟩ := Swc.continuous_joinDrv hc
  obtain ⟨hW, hW0⟩ := continuous_futureJoined c r l a ω
  -- the future program's first `m` pieces are the history's
  have hΔ : ∀ j < m, specDelta (schedSpec x Lf) j = Δh j := fun j hj =>
    specDelta_schedSpec_append x _ hj
  have hD : ∀ j < m, canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec x Lf) j ω = Dh j :=
    fun j hj => RootC11.canonSpecFam_append c.hκ c.h12p c.βA c.c₀ c.h x _ hj ω
  have hJTf : Swc.joinTime (specDelta (schedSpec x Lf))
      (fun j => canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec x Lf) j ω) m =
      (RootJ31.historyTime c r l : ℝ) := (joinTime_congr hΔ hD).trans hJT
  have hag : ∀ t : ℝ≥0, (t : ℝ) ≤ Swc.joinTime Δh Dh m →
      futureJoined c r l a ω t = Swc.joinDrv Δh Dh m t := by
    intro t ht
    have htT : t ≤ RootJ31.historyTime c r l := by rw [hJT] at ht; exact_mod_cast ht
    have h1 : futureJoined c r l a ω t =
        Swc.joinDrv (specDelta (schedSpec x Lf))
          (fun j => canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec x Lf) j ω) (m + 1) t :=
      futureJoined_eq_joinDrv c r l a ω hord hold hgood
        (htT.trans (le_add_of_nonneg_right zero_le))
    have hmem : (t : ℝ) ∈ Icc 0 (Swc.joinTime (specDelta (schedSpec x Lf))
        (fun j => canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec x Lf) j ω) m) :=
      ⟨NNReal.coe_nonneg t, by rw [hJTf]; exact_mod_cast htT⟩
    rw [h1, Swc.joinDrv_eqOn m hmem, joinDrv_congr hΔ hD]
  change ExplState.physSet c.κ c.b c.jumps (schedSpec x Lh) Dh = _
  rw [hphys, SwC.radialTips_eq_image hJ hJ0 hW hW0 hγ (Swc.joinTime_nonneg Δh Dh m) hag,
    hJT, Real.toNNReal_coe]

omit [StandardBorelSpace Ω] in
/-- **The physical prefix of a successful history extended by a live query `(θ, q)` is the root
translate of the joined trace on `[0, q]`.** -/
theorem prefixSet_query_eq (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω)
    (hord : TimeOrdered 0 (RootJ31.historyProgram c r l)) (hold : RootJ31.oldSuccess c r l ω)
    (hgood : ∀ (j : ℕ) (hj : j < (RootJ31.futureProgram c r l a).length), LocalExt.IsDrvGood
      (recHist (RootJ31.programRecords c (rootPt r.1) (RootJ31.futureProgram c r l a) ω ⟨j, hj⟩)))
    {γ : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace (futureJoined c r l a ω) ⊤ γ) {q : ℝ≥0}
    (hTq : RootJ31.historyTime c r l < q)
    (hqcap : q ≤ RootJ31.historyTime c r l + RootJ31.candidateCap c r a)
    (hlive : specDelta (schedSpec (rootPt r.1) (RootJ31.historyProgram c r l ++
        [((RootJ31.candidateAngle c r a : ℝ), q)])) (RootJ31.historyProgram c r l).length <
      (canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec (rootPt r.1) (RootJ31.historyProgram c r l ++
        [((RootJ31.candidateAngle c r a : ℝ), q)])) (RootJ31.historyProgram c r l).length ω).2) :
    prefixSet c.hκ c.h12p c.βA c.b c.jumps c.c₀ c.h (rootPt r.1)
        (RootJ31.historyProgram c r l ++ [((RootJ31.candidateAngle c r a : ℝ), q)]) ω =
      (fun z => (rootPt r.1 : ℂ) + z) '' (γ '' Icc 0 q) := by
  set x := rootPt r.1
  set θ : ℝ := (RootJ31.candidateAngle c r a : ℝ)
  set T := RootJ31.historyTime c r l with hT
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
  have hs' : AllSucc Δ' D' (m + 1) := by
    intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · rw [hΔ'h j hj, hD'h j hj]; exact hsh j hj
    · exact hlive
  have hc' : ∀ i < m + 1, Continuous (stopDrv (Δ' i) (D' i)) ∧ stopDrv (Δ' i) (D' i) 0 = 0 :=
    fun i hi => continuous_stopDrv_of_lt
      (isRegularDriver_canonDrive c.hκ c.h12p c.βA c.c₀ x _ _ (c.h ω) i) (hs' i hi)
      (specDelta_ne_top _ i)
  have hphys : ExplState.physSet c.κ c.b c.jumps (schedSpec x L') D' =
      (fun z => (x : ℂ) + z) '' Swc.radialTips (Swc.joinDrv Δ' D' (m + 1)) 0
        (Swc.joinTime Δ' D' (m + 1)) := by
    have h := Swc.physSet_eq_radialTips (κ := c.κ) (b := c.b) (jumps := c.jumps)
      (spec := schedSpec x L') (D := D') rfl (isFlowProg_spec x true L') (specDelta_ne_top _)
      (by rw [hlen']; exact hs') (by rw [hlen']; exact hc')
    rw [hlen'] at h
    exact h
  have hTl : T = lastTime 0 Lh := schedTime_length_eq_lastTime _
  have hord' : TimeOrdered 0 L' := timeOrdered_append hord (by
    change lastTime 0 Lh ≤ q
    rw [← hTl]
    exact hTq.le)
  have hmL : m < L'.length := by
    rw [hL', List.length_append, List.length_singleton]; omega
  have hJT' : Swc.joinTime Δ' D' (m + 1) = (q : ℝ) := by
    have hget : L'[m] = (θ, q) := by simp [hL', hm]
    rw [joinTime_eq_schedTime x hord' hmL hs', schedTime_succ_eq_getElem hmL, hget]
  obtain ⟨hJ, hJ0⟩ := Swc.continuous_joinDrv hc'
  obtain ⟨hW, hW0⟩ := continuous_futureJoined c r l a ω
  -- the switching time after the history, for all three programs
  have hJTh : Swc.joinTime Δh Dh m = (T : ℝ) := joinTime_eq_schedTime x hord le_rfl hsh
  have hJm' : Swc.joinTime Δ' D' m = (T : ℝ) := (joinTime_congr hΔ'h hD'h).trans hJTh
  have hJmf : Swc.joinTime Δf Df m = (T : ℝ) := (joinTime_congr hΔfh hDfh).trans hJTh
  have hJDm : Swc.joinDrv Δf Df m = Swc.joinDrv Δ' D' m :=
    (joinDrv_congr hΔfh hDfh).trans (joinDrv_congr hΔ'h hD'h).symm
  -- the last piece: same canonical driver, both stops beyond `q - T`
  have hDm : Df m = D' m :=
    RootH29.canonical_next_independent_time c.hκ c.h12p c.βA c.c₀ c.h x θ Lh
      (T + RootJ31.candidateCap c r a) q ω
  have hΔfm : Δf m = (RootJ31.candidateCap c r a : ℝ≥0∞) := RootJ31.futureProgram_delta c r l a
  have hΔ'm : Δ' m = ((q - T : ℝ≥0) : ℝ≥0∞) := RootH29.specDelta_last x θ Lh q
  have hqT : (q - T : ℝ≥0) ≤ RootJ31.candidateCap c r a := by
    rw [tsub_le_iff_left]; exact hqcap
  have hlast : ∀ u : ℝ, ((u.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ ((q - T : ℝ≥0) : ℝ≥0∞) →
      stopDrv (Δf m) (Df m) u = stopDrv (Δ' m) (D' m) u := by
    intro u hu
    have hζ : ((q - T : ℝ≥0) : ℝ≥0∞) < (D' m).2 := by rw [← hΔ'm]; exact hlive
    rw [stopDrv_eq_of_le (e := Df m) (by
        rw [hΔfm, hDm]
        exact le_min (hu.trans (ENNReal.coe_le_coe.2 hqT)) (hu.trans hζ.le)),
      stopDrv_eq_of_le (e := D' m) (by rw [hΔ'm]; exact le_min hu (hu.trans hζ.le)), hDm]
  have hag : ∀ t : ℝ≥0, (t : ℝ) ≤ Swc.joinTime Δ' D' (m + 1) →
      futureJoined c r l a ω t = Swc.joinDrv Δ' D' (m + 1) t := by
    intro t ht
    rw [hJT'] at ht
    have htq : t ≤ q := by exact_mod_cast ht
    have h1 : futureJoined c r l a ω t = Swc.joinDrv Δf Df (m + 1) t :=
      futureJoined_eq_joinDrv c r l a ω hord hold hgood (htq.trans hqcap)
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
    · rw [ite_eq_right htT, ite_eq_right htT, hlast]
      have hle : (t : ℝ) - T ≤ ((q - T : ℝ≥0) : ℝ) := by
        rw [NNReal.coe_sub hTq.le]; linarith
      exact ENNReal.coe_le_coe.2 (Real.toNNReal_le_iff_le_coe.2 hle)
  change ExplState.physSet c.κ c.b c.jumps (schedSpec x L') D' = _
  rw [hphys, SwC.radialTips_eq_image hJ hJ0 hW hW0 hγ (Swc.joinTime_nonneg Δ' D' _) hag,
    hJT', Real.toNNReal_coe]

end InteractingSLE.Theorem14.GW2TipSystem.Gm
