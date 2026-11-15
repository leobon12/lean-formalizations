/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2GmPrefix
import InteractingSLE.Spec.Supplement.GW1PieceChart

/-!
# Re-nesting on the history and query windows; traces on a common prefix

Packet PROVE-GW2-GEOM2 (ruling R111, cross-program identity). Standalone forms of the driver identities inside
`prefixSet_history_eq` / `prefixSet_query_eq`, and uniqueness of generating traces on a common driver prefix:

* **`futureJoined_eq_joinDrv_hist`**: on `[0, T]` the joined future driver is the front-nested driver of the history;
* **`futureJoined_eq_joinDrv_query`**: on `[0, q]` it is the front-nested driver of the history extended by the live
  query `(θ, q)` (the next history);
* **`trace_eq_of_driver_eqOn`**: two drivers agreeing on `[0, q]` have the same generating trace there.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal
open QuantumZipper (H fwdMapInv)

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.Gm

open Exist Staged StagedLaw Restart GW2Schedule GW2Tip RootC24 Sec5.Prop513TreeExtract
  Sec5.Prop513Schedule

/-- **Generating traces of drivers agreeing on `[0, q]` agree there.** -/
theorem trace_eq_of_driver_eqOn {J J' : ℝ≥0 → ℝ} (hJ : Continuous J) (hJ0 : J 0 = 0)
    (hJ' : Continuous J') (hJ'0 : J' 0 = 0) {γ γ' : ℝ≥0 → ℂ} (hγ : IsGeneratingTrace J ⊤ γ)
    (hγ' : IsGeneratingTrace J' ⊤ γ') {q : ℝ≥0} (h : ∀ t ≤ q, J t = J' t) :
    ∀ t ≤ q, γ t = γ' t := by
  intro t ht
  have h1 := hγ.tendsto_fwdMapInv_tip hJ.continuousOn hJ0
    (show ((t : ℝ≥0) : ℝ≥0∞) < ⊤ from ENNReal.coe_lt_top)
  have h2 := hγ'.tendsto_fwdMapInv_tip hJ'.continuousOn hJ'0
    (show ((t : ℝ≥0) : ℝ≥0∞) < ⊤ from ENNReal.coe_lt_top)
  have hF : ∀ z ∈ H, fwdMapInv (fun s : ℝ => J s.toNNReal) t z =
      fwdMapInv (fun s : ℝ => J' s.toNNReal) t z := fun z hz =>
    LP.fwdMapInv_eq_of_eqOn_Icc (hJ.comp continuous_real_toNNReal)
      (hJ'.comp continuous_real_toNNReal) (by simp [hJ0]) (by simp [hJ'0]) t.2
      (fun r hr => h _ ((Real.toNNReal_le_iff_le_coe.2 hr.2).trans ht)) hz
  have : (𝓝[H] (0 : ℂ)).NeBot :=
    GW1P.neBot_nhdsWithin_H (by change (0 : ℝ) ≤ (0 : ℂ).im; simp)
  exact tendsto_nhds_unique h1 (h2.congr' (eventually_nhdsWithin_of_forall fun z hz => (hF z hz).symm))

variable {Ω : Type u} [MeasurableSpace Ω]

/-- **The joined future driver on the history window** is the front-nested driver of the history. -/
theorem futureJoined_eq_joinDrv_hist (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω)
    (hord : TimeOrdered 0 (RootJ31.historyProgram c r l)) (hold : RootJ31.oldSuccess c r l ω)
    (hgood : ∀ (j : ℕ) (hj : j < (RootJ31.futureProgram c r l a).length), LocalExt.IsDrvGood
      (recHist (RootJ31.programRecords c (rootPt r.1) (RootJ31.futureProgram c r l a) ω ⟨j, hj⟩))) :
    ∀ t : ℝ≥0, t ≤ RootJ31.historyTime c r l →
      futureJoined c r l a ω t =
        Swc.joinDrv (specDelta (schedSpec (rootPt r.1) (RootJ31.historyProgram c r l)))
          (fun j => canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h
            (schedSpec (rootPt r.1) (RootJ31.historyProgram c r l)) j ω)
          (RootJ31.historyProgram c r l).length t := by
  set x := rootPt r.1
  set Lh := RootJ31.historyProgram c r l with hLh
  set m := Lh.length with hm
  set Δh := specDelta (schedSpec x Lh)
  set Dh := fun j => canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec x Lh) j ω
  set Lf := RootJ31.futureProgram c r l a with hLf
  have hsh : AllSucc Δh Dh m := (RootJ31.oldSuccess_iff_allSucc c r l ω).mp hold
  have hJT : Swc.joinTime Δh Dh m = (RootJ31.historyTime c r l : ℝ) :=
    joinTime_eq_schedTime x hord le_rfl hsh
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
  intro t ht
  exact hag t (by rw [hJT]; exact_mod_cast ht)

/-- **The joined future driver on the query window** is the front-nested driver of the next history
(the history extended by the live query `(θ, q)`). -/
theorem futureJoined_eq_joinDrv_query (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω)
    (hord : TimeOrdered 0 (RootJ31.historyProgram c r l)) (hold : RootJ31.oldSuccess c r l ω)
    (hgood : ∀ (j : ℕ) (hj : j < (RootJ31.futureProgram c r l a).length), LocalExt.IsDrvGood
      (recHist (RootJ31.programRecords c (rootPt r.1) (RootJ31.futureProgram c r l a) ω ⟨j, hj⟩)))
    {q : ℝ≥0} (hTq : RootJ31.historyTime c r l < q)
    (hqcap : q ≤ RootJ31.historyTime c r l + RootJ31.candidateCap c r a)
    (hlive : specDelta (schedSpec (rootPt r.1) (RootJ31.historyProgram c r l ++
        [((RootJ31.candidateAngle c r a : ℝ), q)])) (RootJ31.historyProgram c r l).length <
      (canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec (rootPt r.1) (RootJ31.historyProgram c r l ++
        [((RootJ31.candidateAngle c r a : ℝ), q)])) (RootJ31.historyProgram c r l).length ω).2) :
    ∀ t : ℝ≥0, t ≤ q →
      futureJoined c r l a ω t =
        Swc.joinDrv (specDelta (schedSpec (rootPt r.1) (RootJ31.historyProgram c r l ++
            [((RootJ31.candidateAngle c r a : ℝ), q)])))
          (fun j => canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec (rootPt r.1)
            (RootJ31.historyProgram c r l ++ [((RootJ31.candidateAngle c r a : ℝ), q)])) j ω)
          ((RootJ31.historyProgram c r l).length + 1) t := by
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
  have hs' : AllSucc Δ' D' (m + 1) := by
    intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · rw [hΔ'h j hj, hD'h j hj]; exact hsh j hj
    · exact hlive
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
  intro t ht
  exact hag t (by rw [hJT']; exact_mod_cast ht)

end InteractingSLE.Theorem14.GW2TipSystem.Gm
