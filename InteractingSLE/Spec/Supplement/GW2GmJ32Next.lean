/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2GmCross
import InteractingSLE.Spec.Supplement.GW2SdePrefix

/-!
# The candidate's future driver is the next history's driver on the query window

Packet PROVE-GW2-GEOM2 (round 4), reader consistency for J32. For a history `l`, a candidate `a` and a query time
`q ≥ T` (`T` the history time), the next history `(θ_a, q) :: l` has the program `history ++ [(θ_a, q)]`, whose
joined driver (`RootJ31.joinedRead`) is what its retained record pair reads (`measurable_historyPair_sigma`).

* **`futureJoined_eq_nextJoined`** (deterministic): on a successful, time-ordered history with good records of both
  programs, the candidate's joined future driver equals the next history's joined driver on
  `[0, min (T + cap) q]`. Unlike `futureJoined_eq_joinDrv_query`, the query piece need not survive to `q`: both
  last pieces are the same canonical piece, stopped at `cap` and at `q − T`.
* **`ae_futureJoined_eq_nextJoined`**: almost surely this holds for every history, candidate and query (records of
  launched pieces are a.s. good, `ae_launched_rdrv_trace`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.Gm

open Exist Staged StagedLaw Restart GW2Schedule GW2Tip RootC24 Sec5.Prop513TreeExtract
  Sec5.Prop513Schedule

variable {Ω : Type u} [MeasurableSpace Ω]

omit [MeasurableSpace Ω] in
/-- A stopped driver read before both stops does not see the stop. -/
theorem stopDrv_eq_of_le_both {t t' : ℝ≥0∞} {e : (ℝ≥0 → ℝ) × ℝ≥0∞} {u : ℝ}
    (ht : ((u.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ t) (ht' : ((u.toNNReal : ℝ≥0) : ℝ≥0∞) ≤ t') :
    stopDrv t e u = stopDrv t' e u := by
  change e.1 (min ((u.toNNReal : ℝ≥0) : ℝ≥0∞) (min t e.2)).toNNReal =
    e.1 (min ((u.toNNReal : ℝ≥0) : ℝ≥0∞) (min t' e.2)).toNNReal
  rw [← min_assoc, min_eq_left ht, ← min_assoc, min_eq_left ht']

/-- **The candidate's future driver is the next history's driver on the query window** (deterministic). -/
theorem futureJoined_eq_nextJoined (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω)
    (hord : TimeOrdered 0 (RootJ31.historyProgram c r l)) (hold : RootJ31.oldSuccess c r l ω)
    (hgood : ∀ (j : ℕ) (hj : j < (RootJ31.futureProgram c r l a).length), LocalExt.IsDrvGood
      (recHist (RootJ31.programRecords c (rootPt r.1) (RootJ31.futureProgram c r l a) ω ⟨j, hj⟩)))
    {q : ℝ≥0} (hTq : RootJ31.historyTime c r l ≤ q)
    (hgood' : ∀ (j : ℕ) (hj : j < (RootJ31.historyProgram c r l ++
        [((RootJ31.candidateAngle c r a : ℝ), q)]).length), LocalExt.IsDrvGood
      (recHist (RootJ31.programRecords c (rootPt r.1) (RootJ31.historyProgram c r l ++
        [((RootJ31.candidateAngle c r a : ℝ), q)]) ω ⟨j, hj⟩))) :
    ∀ t : ℝ≥0, t ≤ RootJ31.historyTime c r l + RootJ31.candidateCap c r a → t ≤ q →
      futureJoined c r l a ω t =
        RootJ31.joinedRead (RootJ31.historyProgram c r l ++ [((RootJ31.candidateAngle c r a : ℝ), q)])
          (RootJ31.programRecords c (rootPt r.1) (RootJ31.historyProgram c r l ++
            [((RootJ31.candidateAngle c r a : ℝ), q)]) ω) t := by
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
  have hΔ'h : ∀ j < m, Δ' j = Δh j := fun j hj => specDelta_schedSpec_append x _ hj
  have hD'h : ∀ j < m, D' j = Dh j := fun j hj =>
    RootC11.canonSpecFam_append c.hκ c.h12p c.βA c.c₀ c.h x _ hj ω
  have hΔfh : ∀ j < m, Δf j = Δh j := fun j hj => specDelta_schedSpec_append x _ hj
  have hDfh : ∀ j < m, Df j = Dh j := fun j hj =>
    RootC11.canonSpecFam_append c.hκ c.h12p c.βA c.c₀ c.h x _ hj ω
  have hs' : AllSucc Δ' D' m := by
    intro j hj
    rw [hΔ'h j hj, hD'h j hj]
    exact hsh j hj
  have hTl : T = lastTime 0 Lh := schedTime_length_eq_lastTime _
  have hord' : TimeOrdered 0 L' := timeOrdered_append hord (by
    change lastTime 0 Lh ≤ q
    rw [← hTl]
    exact hTq)
  have hlen' : L'.length = m + 1 := by
    rw [hL', List.length_append, List.length_singleton]
  -- the next history's joined driver is front-nested
  have hw' : ∀ j < L'.length, ∀ u : ℝ≥0,
      ((fun j (R : Fin L'.length → RecData) => (RootJ31.recordDriver R j, (⊤ : ℝ≥0∞))) j
        (RootJ31.programRecords c x L' ω)).1 u = stopDrv (Δ' j) (D' j) u := by
    intro j hj u
    have hrd : RootJ31.recordDriver (RootJ31.programRecords c x L' ω) j =
        fun u : ℝ≥0 => rdrv (RootJ31.programRecords c x L' ω ⟨j, hj⟩) u := by
      simp only [RootJ31.recordDriver, hj, ↓reduceDIte]
    change RootJ31.recordDriver (RootJ31.programRecords c x L' ω) j u = _
    rw [hrd]
    have he : IsRegularDriver (D' j) :=
      isRegularDriver_canonDrive c.hκ c.h12p c.βA c.c₀ x _ _ (c.h ω) j
    exact congrFun (recDrv_eq_stopDrv he (hgood' j hj)) u
  have hT' : ∀ k < L'.length, Swc.joinTime Δ' D' k = schedTime 0 L' k := fun k hk =>
    joinTime_eq_schedTime x hord' hk.le (hs'.mono (by omega))
  have hlast' : lastTime 0 L' = q := by
    rw [hL', lastTime_eq_getLast _ _ (by simp)]
    simp only [List.getLast_append, List.isEmpty_cons, Bool.false_eq_true, ↓reduceDIte,
      List.getLast_singleton]
  -- the switching time after the history and the common prefix
  have hJTh : Swc.joinTime Δh Dh m = (T : ℝ) := joinTime_eq_schedTime x hord le_rfl hsh
  have hJm' : Swc.joinTime Δ' D' m = (T : ℝ) := (joinTime_congr hΔ'h hD'h).trans hJTh
  have hJmf : Swc.joinTime Δf Df m = (T : ℝ) := (joinTime_congr hΔfh hDfh).trans hJTh
  have hJDm : Swc.joinDrv Δf Df m = Swc.joinDrv Δ' D' m :=
    (joinDrv_congr hΔfh hDfh).trans (joinDrv_congr hΔ'h hD'h).symm
  -- the last piece: the same canonical driver, stopped at `cap` and at `q − T`
  have hDm : Df m = D' m :=
    RootH29.canonical_next_independent_time c.hκ c.h12p c.βA c.c₀ c.h x θ Lh
      (T + RootJ31.candidateCap c r a) q ω
  have hΔfm : Δf m = (RootJ31.candidateCap c r a : ℝ≥0∞) := RootJ31.futureProgram_delta c r l a
  have hΔ'm : Δ' m = ((q - T : ℝ≥0) : ℝ≥0∞) := RootH29.specDelta_last x θ Lh q
  intro t htcap htq
  have h1 : futureJoined c r l a ω t = Swc.joinDrv Δf Df (m + 1) t :=
    futureJoined_eq_joinDrv c r l a ω hord hold hgood htcap
  have h2 : RootJ31.joinedRead L' (RootJ31.programRecords c x L' ω) t =
      Swc.joinDrv Δ' D' (m + 1) t := by
    have h := joinedDriver_eq_joinDrv (fun j (R : Fin L'.length → RecData) =>
      (RootJ31.recordDriver R j, (⊤ : ℝ≥0∞))) (RootJ31.programRecords c x L' ω) L' hord'
      (fun j => RootJ31.recordDriver_zero _ j) hw' hT' (le_of_le_of_eq htq hlast'.symm)
    exact h.trans (congrFun (congrArg (Swc.joinDrv Δ' D') hlen') t)
  rw [h1, h2]
  change (if (t : ℝ) ≤ Swc.joinTime Δf Df m then Swc.joinDrv Δf Df m t else
      Swc.joinDrv Δf Df m (Swc.joinTime Δf Df m) +
        stopDrv (Δf m) (Df m) (t - Swc.joinTime Δf Df m)) =
    (if (t : ℝ) ≤ Swc.joinTime Δ' D' m then Swc.joinDrv Δ' D' m t else
      Swc.joinDrv Δ' D' m (Swc.joinTime Δ' D' m) +
        stopDrv (Δ' m) (D' m) (t - Swc.joinTime Δ' D' m))
  rw [hJmf, hJm', hJDm]
  by_cases htT : (t : ℝ) ≤ T
  · rw [ite_eq_left htT, ite_eq_left htT]
  · rw [ite_eq_right htT, ite_eq_right htT, hDm]
    have hTt : T ≤ t := by exact_mod_cast (not_le.1 htT).le
    have hu : ((t : ℝ) - T).toNNReal = t - T := by
      rw [← NNReal.coe_sub hTt, Real.toNNReal_coe]
    congr 1
    refine stopDrv_eq_of_le_both ?_ ?_
    · rw [hu, hΔfm]
      exact ENNReal.coe_le_coe.2 (tsub_le_iff_left.2 htcap)
    · rw [hu, hΔ'm]
      exact ENNReal.coe_le_coe.2 (tsub_le_tsub_right htq T)

variable [StandardBorelSpace Ω] in
/-- **Reader consistency for J32, the drivers**: almost surely, for every successful time-ordered history `l`,
candidate `a` and query `q ≥ T`, the candidate's joined future driver equals the joined driver of the next
history `(θ_a, q) :: l` on `[0, min (T + cap) q]`. -/
theorem ae_futureJoined_eq_nextJoined (h13 : Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) :
    ∀ᵐ ω ∂c.P, ∀ (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (q : c.Q),
      RootJ31.oldSuccess c r l ω → TimeOrdered 0 (RootJ31.historyProgram c r l) →
      RootJ31.historyTime c r l ≤ (q : ℝ≥0) →
      ∀ t : ℝ≥0, t ≤ RootJ31.historyTime c r l + RootJ31.candidateCap c r a → t ≤ (q : ℝ≥0) →
        futureJoined c r l a ω t =
          RootJ31.joinedRead (RootJ31.historyProgram c r ((RootJ31.candidateAngle c r a, q) :: l))
            (RootJ31.programRecords c (rootPt r.1)
              (RootJ31.historyProgram c r ((RootJ31.candidateAngle c r a, q) :: l)) ω) t := by
  have : Countable c.Θ := c.hΘc.to_subtype
  have : Countable c.Q := c.hQc.to_subtype
  have hnext : ∀ᵐ ω ∂c.P, ∀ (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (q : c.Q),
      ∀ k < (RootJ31.historyProgram c r l ++ [((RootJ31.candidateAngle c r a : ℝ), (q : ℝ≥0))]).length,
        AllSucc (specDelta (schedSpec (rootPt r.1) (RootJ31.historyProgram c r l ++
            [((RootJ31.candidateAngle c r a : ℝ), (q : ℝ≥0))])))
          (fun j => canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec (rootPt r.1)
            (RootJ31.historyProgram c r l ++ [((RootJ31.candidateAngle c r a : ℝ), (q : ℝ≥0))])) j ω) k →
        LocalExt.IsDrvGood (recHist (stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpec (rootPt r.1)
          (RootJ31.historyProgram c r l ++ [((RootJ31.candidateAngle c r a : ℝ), (q : ℝ≥0))])) k ω)) := by
    rw [ae_all_iff]; intro l
    rw [ae_all_iff]; intro a
    rw [ae_all_iff]; intro q
    filter_upwards [ae_launched_rdrv_trace h13 c (rootPt r.1)
      (RootJ31.historyProgram c r l ++ [((RootJ31.candidateAngle c r a : ℝ), (q : ℝ≥0))])]
      with ω hω k hk hs
    exact (hω k hk hs).1
  filter_upwards [ae_futureJoined_trace h13 c r, hnext] with ω hjoin hnext l a q hold hord hTq
  obtain ⟨hgood, -⟩ := hjoin l a hold
  set x := rootPt r.1
  set Lh := RootJ31.historyProgram c r l with hLh
  set L' := Lh ++ [((RootJ31.candidateAngle c r a : ℝ), (q : ℝ≥0))] with hL'
  have hsh := (RootJ31.oldSuccess_iff_allSucc c r l ω).mp hold
  set Δ' := specDelta (schedSpec x L')
  set D' := fun j => canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec x L') j ω
  have hΔ'h : ∀ j < Lh.length, Δ' j = specDelta (schedSpec x Lh) j := fun j hj =>
    specDelta_schedSpec_append x _ hj
  have hD'h : ∀ j < Lh.length, D' j =
      canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec x Lh) j ω := fun j hj =>
    RootC11.canonSpecFam_append c.hκ c.h12p c.βA c.c₀ c.h x _ hj ω
  have hs' : AllSucc Δ' D' Lh.length := by
    intro j hj
    rw [hΔ'h j hj, hD'h j hj]
    exact hsh j hj
  have hgood' : ∀ (j : ℕ) (hj : j < L'.length), LocalExt.IsDrvGood
      (recHist (RootJ31.programRecords c x L' ω ⟨j, hj⟩)) := by
    intro j hj
    have hjm : j ≤ Lh.length := by
      rw [hL', List.length_append, List.length_singleton] at hj
      omega
    exact hnext l a q j hj (hs'.mono hjm)
  intro t htcap htq
  rw [RootJ31.historyProgram_cons]
  exact futureJoined_eq_nextJoined c r l a ω hord hold hgood hTq hgood' t htcap htq

/-! ### Without time order -/

omit [MeasurableSpace Ω] in
/-- **Two programs differing only in their last time** have the same joined driver while the last pieces agree:
the common prefix is glued identically, and the last pieces start at the same joined time. -/
theorem joinedDriver_append_last_eq {Ω' : Type*} (E F : ℕ → Ω' → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω : Ω') :
    ∀ (Lh : List (ℝ × ℝ≥0)) (j : ℕ) (a : ℝ≥0) (p₁ p₂ : ℝ × ℝ≥0) (d : ℝ≥0),
      (∀ i, j ≤ i → i < j + Lh.length → E i ω = F i ω) →
      (∀ u ≤ d, (E (j + Lh.length) ω).1 u = (F (j + Lh.length) ω).1 u) →
      d ≤ p₁.2 - lastTime a Lh → d ≤ p₂.2 - lastTime a Lh →
      ∀ t ≤ (lastTime a Lh - a) + d,
        joinedDriver E j a (Lh ++ [p₁]) ω t = joinedDriver F j a (Lh ++ [p₂]) ω t
  | [], j, a, p₁, p₂, d, _, hlast, h1, h2, t, ht => by
    change Sec7.StripSideHeightProb.catPath (E j ω).1 (p₁.2 - a)
        (joinedDriver E (j + 1) p₁.2 [] ω) t =
      Sec7.StripSideHeightProb.catPath (F j ω).1 (p₂.2 - a) (joinedDriver F (j + 1) p₂.2 [] ω) t
    have ht' : t ≤ d := by simpa only [lastTime, tsub_self, zero_add] using ht
    have h1' : d ≤ p₁.2 - a := h1
    have h2' : d ≤ p₂.2 - a := h2
    rw [Sec7.StripSideHeightProb.catPath_of_le (ht'.trans h1'),
      Sec7.StripSideHeightProb.catPath_of_le (ht'.trans h2')]
    simpa only [List.length_nil, add_zero] using hlast t ht'
  | p :: Lh, j, a, p₁, p₂, d, hpre, hlast, h1, h2, t, ht => by
    change Sec7.StripSideHeightProb.catPath (E j ω).1 (p.2 - a)
        (joinedDriver E (j + 1) p.2 (Lh ++ [p₁]) ω) t =
      Sec7.StripSideHeightProb.catPath (F j ω).1 (p.2 - a)
        (joinedDriver F (j + 1) p.2 (Lh ++ [p₂]) ω) t
    rw [hpre j le_rfl (by simp only [List.length_cons]; omega)]
    unfold Sec7.StripSideHeightProb.catPath
    split_ifs with htp
    · rfl
    · congr 1
      have hidx : j + (p :: Lh).length = j + 1 + Lh.length := by
        simp only [List.length_cons]; omega
      rw [hidx] at hlast
      refine joinedDriver_append_last_eq E F ω Lh (j + 1) p.2 p₁ p₂ d
        (fun i hi1 hi2 => hpre i (by omega) (by simp only [List.length_cons]; omega)) hlast h1 h2
        (t - (p.2 - a)) ?_
      have ht' : t ≤ (lastTime p.2 Lh - a) + d := ht
      rw [tsub_le_iff_right]
      calc t ≤ (lastTime p.2 Lh - a) + d := ht'
        _ ≤ (lastTime p.2 Lh - p.2 + (p.2 - a)) + d := by
          gcongr
          exact tsub_le_tsub_add_tsub
        _ = lastTime p.2 Lh - p.2 + d + (p.2 - a) := by ring

omit [MeasurableSpace Ω] in
/-- **Joined record drivers of two programs differing only in their last time** agree up to the last history
time plus any `d` on which the last records' drivers agree (and which both last pieces cover). -/
theorem joinedRead_append_last_eq (Lh : List (ℝ × ℝ≥0)) (p₁ p₂ : ℝ × ℝ≥0)
    (R₁ : Fin (Lh ++ [p₁]).length → RecData) (R₂ : Fin (Lh ++ [p₂]).length → RecData)
    (hpre : ∀ (i : ℕ) (h1 : i < (Lh ++ [p₁]).length) (h2 : i < (Lh ++ [p₂]).length),
      i < Lh.length → R₁ ⟨i, h1⟩ = R₂ ⟨i, h2⟩) {d : ℝ≥0}
    (hlast : ∀ u ≤ d, RootJ31.recordDriver R₁ Lh.length u = RootJ31.recordDriver R₂ Lh.length u)
    (h1 : d ≤ p₁.2 - lastTime 0 Lh) (h2 : d ≤ p₂.2 - lastTime 0 Lh) :
    ∀ t ≤ lastTime 0 Lh + d,
      RootJ31.joinedRead (Lh ++ [p₁]) R₁ t = RootJ31.joinedRead (Lh ++ [p₂]) R₂ t := by
  intro t ht
  unfold RootJ31.joinedRead
  rw [GW2Sde.joinedDriver_eq_const _ R₁, GW2Sde.joinedDriver_eq_const _ R₂]
  refine joinedDriver_append_last_eq _ _ () Lh 0 0 p₁ p₂ d (fun i _ hi => ?_) ?_ h1 h2 t
    (by simpa only [tsub_zero] using ht)
  · have hi1 : i < (Lh ++ [p₁]).length := by rw [List.length_append]; omega
    have hi2 : i < (Lh ++ [p₂]).length := by rw [List.length_append]; omega
    have hiL : i < Lh.length := by omega
    simp only [RootJ31.recordDriver, hi1, hi2, ↓reduceDIte, hpre i hi1 hi2 hiL]
  · intro u hu
    simpa only [zero_add] using congrArg (fun y => y) (hlast u hu)

variable [StandardBorelSpace Ω] in
/-- **Reader consistency for J32, the drivers, for every history**: almost surely, for every successful history
`l` (time-ordered or not), candidate `a` and query `q`, the candidate's joined future driver equals the joined
driver of the next history `(θ_a, q) :: l` on `[0, T + min cap (q − T)]`. -/
theorem ae_futureJoined_eq_nextJoined' (h13 : Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) :
    ∀ᵐ ω ∂c.P, ∀ (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (q : c.Q), RootJ31.oldSuccess c r l ω →
      ∀ t : ℝ≥0, t ≤ RootJ31.historyTime c r l +
          min (RootJ31.candidateCap c r a) ((q : ℝ≥0) - RootJ31.historyTime c r l) →
        futureJoined c r l a ω t =
          RootJ31.joinedRead (RootJ31.historyProgram c r ((RootJ31.candidateAngle c r a, q) :: l))
            (RootJ31.programRecords c (rootPt r.1)
              (RootJ31.historyProgram c r ((RootJ31.candidateAngle c r a, q) :: l)) ω) t := by
  have : Countable c.Θ := c.hΘc.to_subtype
  have : Countable c.Q := c.hQc.to_subtype
  have hnext : ∀ᵐ ω ∂c.P, ∀ (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (q : c.Q),
      ∀ k < (RootJ31.historyProgram c r l ++ [((RootJ31.candidateAngle c r a : ℝ), (q : ℝ≥0))]).length,
        AllSucc (specDelta (schedSpec (rootPt r.1) (RootJ31.historyProgram c r l ++
            [((RootJ31.candidateAngle c r a : ℝ), (q : ℝ≥0))])))
          (fun j => canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec (rootPt r.1)
            (RootJ31.historyProgram c r l ++ [((RootJ31.candidateAngle c r a : ℝ), (q : ℝ≥0))])) j ω) k →
        LocalExt.IsDrvGood (recHist (stopRec c.hκ c.h12p c.βA c.c₀ c.h (schedSpec (rootPt r.1)
          (RootJ31.historyProgram c r l ++ [((RootJ31.candidateAngle c r a : ℝ), (q : ℝ≥0))])) k ω)) := by
    rw [ae_all_iff]; intro l
    rw [ae_all_iff]; intro a
    rw [ae_all_iff]; intro q
    filter_upwards [ae_launched_rdrv_trace h13 c (rootPt r.1)
      (RootJ31.historyProgram c r l ++ [((RootJ31.candidateAngle c r a : ℝ), (q : ℝ≥0))])]
      with ω hω k hk hs
    exact (hω k hk hs).1
  filter_upwards [ae_futureJoined_trace h13 c r, hnext] with ω hjoin hnext l a q hold
  obtain ⟨hgood, -⟩ := hjoin l a hold
  set x := rootPt r.1
  set θ : ℝ := (RootJ31.candidateAngle c r a : ℝ)
  set T := RootJ31.historyTime c r l with hT
  set Lh := RootJ31.historyProgram c r l with hLh
  set m := Lh.length with hm
  set L' := Lh ++ [(θ, (q : ℝ≥0))] with hL'
  set Lf := RootJ31.futureProgram c r l a with hLf
  set Δ' := specDelta (schedSpec x L')
  set D' := fun j => canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec x L') j ω
  set Δf := specDelta (schedSpec x Lf)
  set Df := fun j => canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec x Lf) j ω
  have hsh := (RootJ31.oldSuccess_iff_allSucc c r l ω).mp hold
  have hΔ'h : ∀ j < m, Δ' j = specDelta (schedSpec x Lh) j := fun j hj =>
    specDelta_schedSpec_append x _ hj
  have hD'h : ∀ j < m, D' j = canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec x Lh) j ω :=
    fun j hj => RootC11.canonSpecFam_append c.hκ c.h12p c.βA c.c₀ c.h x _ hj ω
  have hs' : AllSucc Δ' D' m := by
    intro j hj
    rw [hΔ'h j hj, hD'h j hj]
    exact hsh j hj
  have hmL' : m < L'.length := by rw [hL', List.length_append, List.length_singleton]; omega
  have hmLf : m < Lf.length := by
    rw [hLf, RootJ31.futureProgram, List.length_append, List.length_singleton]
    exact Nat.lt_succ_self _
  have hgood'm : LocalExt.IsDrvGood (recHist (RootJ31.programRecords c x L' ω ⟨m, hmL'⟩)) :=
    hnext l a q m hmL' hs'
  -- the last records: the same canonical piece stopped at `cap` and at `q − T`
  have hDm : Df m = D' m :=
    RootH29.canonical_next_independent_time c.hκ c.h12p c.βA c.c₀ c.h x θ Lh
      (T + RootJ31.candidateCap c r a) q ω
  have hΔfm : Δf m = (RootJ31.candidateCap c r a : ℝ≥0∞) := RootJ31.futureProgram_delta c r l a
  have hΔ'm : Δ' m = (((q : ℝ≥0) - T : ℝ≥0) : ℝ≥0∞) := RootH29.specDelta_last x θ Lh q
  have hTl : T = lastTime 0 Lh := schedTime_length_eq_lastTime _
  have hlast : ∀ u ≤ min (RootJ31.candidateCap c r a) ((q : ℝ≥0) - T),
      RootJ31.recordDriver (RootJ31.programRecords c x Lf ω) m u =
        RootJ31.recordDriver (RootJ31.programRecords c x L' ω) m u := by
    intro u hu
    simp only [RootJ31.recordDriver, hmLf, hmL', ↓reduceDIte]
    have hef : IsRegularDriver (Df m) :=
      isRegularDriver_canonDrive c.hκ c.h12p c.βA c.c₀ x _ _ (c.h ω) m
    have he' : IsRegularDriver (D' m) :=
      isRegularDriver_canonDrive c.hκ c.h12p c.βA c.c₀ x _ _ (c.h ω) m
    have h1 := congrFun (recDrv_eq_stopDrv hef (hgood m hmLf)) u
    have h2 := congrFun (recDrv_eq_stopDrv he' hgood'm) u
    change rdrv (RootJ31.programRecords c x Lf ω ⟨m, hmLf⟩) u = stopDrv (Δf m) (Df m) u at h1
    change rdrv (RootJ31.programRecords c x L' ω ⟨m, hmL'⟩) u = stopDrv (Δ' m) (D' m) u at h2
    rw [h1, h2, hDm]
    refine stopDrv_eq_of_le_both ?_ ?_
    · rw [Real.toNNReal_coe, hΔfm]
      exact ENNReal.coe_le_coe.2 (hu.trans (min_le_left _ _))
    · rw [Real.toNNReal_coe, hΔ'm]
      exact ENNReal.coe_le_coe.2 (hu.trans (min_le_right _ _))
  intro t ht
  rw [RootJ31.historyProgram_cons]
  change RootJ31.joinedRead Lf (RootJ31.programRecords c x Lf ω) t =
    RootJ31.joinedRead L' (RootJ31.programRecords c x L' ω) t
  refine joinedRead_append_last_eq Lh _ _ _ _ (fun i h1 h2 hi => ?_) hlast ?_ ?_ t
    (by rw [← hTl]; exact ht)
  · exact (stopRec_schedSpec_append c.hκ c.h12p c.βA c.c₀ c.h x _ hi ω).trans
      (stopRec_schedSpec_append c.hκ c.h12p c.βA c.c₀ c.h x _ hi ω).symm
  · change _ ≤ (T + RootJ31.candidateCap c r a) - lastTime 0 Lh
    rw [← hTl, add_tsub_cancel_left]
    exact min_le_left _ _
  · change _ ≤ (q : ℝ≥0) - lastTime 0 Lh
    rw [← hTl]
    exact min_le_right _ _

end InteractingSLE.Theorem14.GW2TipSystem.Gm
