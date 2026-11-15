/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2PsmJoin
import InteractingSLE.Spec.Supplement.GW2TrCap
import InteractingSLE.Spec.Supplement.GW2GmPrefix
import InteractingSLE.Spec.Supplement.GW2GmNest
import InteractingSLE.Spec.Supplement.GW2OlmChain
import InteractingSLE.Spec.Supplement.GW2GmJ32Cross

/-!
# GW2's open lines: the explored driver of a history and of its prefix with a same-angle candidate

Packet PROVE-GW2-STAGEMEAN, R121 round (deterministic; the union side of the Claim(k) step):

* `historyProgram_cons`: the history of `e :: l'` is the history of `l'` followed by `e`;
* **`futureJoined_cons_eq`**: the explored driver of `(r, e :: l', a)` and of the prefix `(r, l', a')`, whose candidate
  has the angle of `e` and a cap reaching past `e`'s end, agree up to the end of `e` (on the history's success):
  the canonical drives agree before `e`, and at `e` they are the same drive (`canonDrive_congr_angle`), only the stop
  differs (`joinDrv_succ_eqOn_of_le`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set
open scoped NNReal ENNReal

namespace InteractingSLE.Theorem14.GW2Psm

open Exist Staged StagedLaw GW2Schedule GW2Tip GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31
  Sec5.Prop513Schedule GW2TipSystem.Swc

variable {Ω : Type*} [MeasurableSpace Ω]

theorem historyProgram_cons (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (e : EntryIdx c.Θ c.Q)
    (l' : List (EntryIdx c.Θ c.Q)) :
    historyProgram c r (e :: l') = historyProgram c r l' ++ [((e.1 : ℝ), (e.2 : ℝ≥0))] := by
  unfold historyProgram
  rw [entryList_cons]
  exact schedOf_cons _ _ _

/-- **The explored driver of a history and of its prefix with a same-angle candidate.** -/
theorem futureJoined_cons_eq (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (e : EntryIdx c.Θ c.Q)
    (l' : List (EntryIdx c.Θ c.Q)) (a a' : ℕ) (ω : Ω)
    (hord : (historyProgram c r (e :: l')).Pairwise (fun p q => p.2 < q.2))
    (hord' : (historyProgram c r l').Pairwise (fun p q => p.2 < q.2))
    (hold : oldSuccess c r (e :: l') ω) (hold' : oldSuccess c r l' ω)
    (hgood : ∀ (j : ℕ) (hj : j < (futureProgram c r (e :: l') a).length), LocalExt.IsDrvGood
      (recHist (programRecords c (rootPt r.1) (futureProgram c r (e :: l') a) ω ⟨j, hj⟩)))
    (hgood' : ∀ (j : ℕ) (hj : j < (futureProgram c r l' a').length), LocalExt.IsDrvGood
      (recHist (programRecords c (rootPt r.1) (futureProgram c r l' a') ω ⟨j, hj⟩)))
    (hθ : candidateAngle c r a' = (e.1 : ℝ))
    (hcap : historyTime c r (e :: l') ≤ historyTime c r l' + candidateCap c r a') :
    ∀ t ≤ historyTime c r (e :: l'), Gm.futureJoined c r (e :: l') a ω t = Gm.futureJoined c r l' a' ω t := by
  intro t ht
  have hH := historyProgram_cons c r e l'
  have hlenH : (historyProgram c r (e :: l')).length = (historyProgram c r l').length + 1 := by
    rw [hH, List.length_append, List.length_singleton]
  -- the first pieces agree
  have hΔj : ∀ j < (historyProgram c r l').length,
      specDelta (schedSpec (rootPt r.1) (futureProgram c r (e :: l') a)) j =
        specDelta (schedSpec (rootPt r.1) (futureProgram c r l' a')) j := by
    intro j hj
    have hj' : j < (historyProgram c r (e :: l')).length := by rw [hlenH]; omega
    unfold futureProgram
    rw [specDelta_schedSpec_append _ _ hj', specDelta_schedSpec_append _ _ hj, hH,
      specDelta_schedSpec_append _ _ hj]
  have hθj : ∀ j < (historyProgram c r l').length,
      specAngle (schedSpec (rootPt r.1) (futureProgram c r (e :: l') a)) j =
        specAngle (schedSpec (rootPt r.1) (futureProgram c r l' a')) j := by
    intro j hj
    have hj' : j < (historyProgram c r (e :: l')).length := by rw [hlenH]; omega
    unfold futureProgram
    rw [specAngle_schedSpec_append _ _ hj', specAngle_schedSpec_append _ _ hj, hH,
      specAngle_schedSpec_append _ _ hj]
  have hθm : specAngle (schedSpec (rootPt r.1) (futureProgram c r (e :: l') a)) (historyProgram c r l').length =
      specAngle (schedSpec (rootPt r.1) (futureProgram c r l' a')) (historyProgram c r l').length := by
    have hj' : (historyProgram c r l').length < (historyProgram c r (e :: l')).length := by rw [hlenH]; omega
    unfold futureProgram
    rw [specAngle_schedSpec_append _ _ hj', hH, RootH29.specAngle_last, RootH29.specAngle_last, hθ]
  have hDall : ∀ j ≤ (historyProgram c r l').length,
      canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec (rootPt r.1) (futureProgram c r (e :: l') a)) j ω =
        canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec (rootPt r.1) (futureProgram c r l' a')) j ω := by
    intro j hj
    exact GW2Rd.canonDrive_congr_angle c.hκ c.h12p c.βA c.c₀ (rootPt r.1) (c.h ω)
      (fun i hi => (lt_or_eq_of_le (hi.trans hj)).elim (hθj i) (fun h => h ▸ hθm))
      (fun i hi => hΔj i (lt_of_lt_of_le hi hj))
  have hTe : historyTime c r (e :: l') = (e.2 : ℝ≥0) := by
    obtain ⟨θe, qe⟩ := e
    exact Gm.historyTime_cons c r l' θe qe
  have hle : specDelta (schedSpec (rootPt r.1) (futureProgram c r (e :: l') a)) (historyProgram c r l').length ≤
      specDelta (schedSpec (rootPt r.1) (futureProgram c r l' a')) (historyProgram c r l').length := by
    have hj' : (historyProgram c r l').length < (historyProgram c r (e :: l')).length := by rw [hlenH]; omega
    rw [GW2Rd.specDelta_future_last c r l' a']
    unfold futureProgram
    rw [specDelta_schedSpec_append _ _ hj', hH, RootH29.specDelta_last]
    refine ENNReal.coe_le_coe.2 (tsub_le_iff_left.2 ?_)
    have h1 : schedTime 0 (historyProgram c r l') (historyProgram c r l').length = historyTime c r l' := rfl
    rw [h1, ← hTe]
    exact hcap
  -- the joined drivers
  have h1 := Gm.futureJoined_eq_joinDrv c r (e :: l') a ω (Gm.timeOrdered_of_pairwise_lt hord) hold hgood
    (ht.trans le_self_add)
  have h2 := Gm.futureJoined_eq_joinDrv c r l' a' ω (Gm.timeOrdered_of_pairwise_lt hord') hold' hgood'
    (ht.trans hcap)
  rw [h1, h2, hlenH]
  set Δ := specDelta (schedSpec (rootPt r.1) (futureProgram c r (e :: l') a)) with hΔ
  set D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun j =>
    canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h (schedSpec (rootPt r.1) (futureProgram c r (e :: l') a)) j ω with hD
  have hTO : TimeOrdered 0 (futureProgram c r (e :: l') a) :=
    Gm.timeOrdered_of_pairwise_lt (GW2Olm.pairwise_lt_futureProgram c r (e :: l') a hord)
  have hlenF : (futureProgram c r (e :: l') a).length = (historyProgram c r l').length + 2 := by
    rw [futureProgram, List.length_append, List.length_singleton, hlenH]
  have hs : AllSucc Δ D ((historyProgram c r l').length + 1) := by
    have := Gm.allSucc_future_of_oldSuccess c r (e :: l') a ω hold
    rw [hlenH] at this
    exact this
  have hjT : joinTime Δ D ((historyProgram c r l').length + 1) = (historyTime c r (e :: l') : ℝ) := by
    rw [Gm.joinTime_eq_schedTime (rootPt r.1) hTO (by omega) hs]
    have : schedTime 0 (futureProgram c r (e :: l') a) ((historyProgram c r l').length + 1) =
        historyTime c r (e :: l') := by
      rw [← hlenH]
      unfold futureProgram historyTime
      exact (schedTime_append 0 _ le_rfl)
    rw [this]
  have htT : (t : ℝ) ∈ Icc (0 : ℝ) (joinTime Δ D ((historyProgram c r l').length + 1)) :=
    ⟨t.coe_nonneg, by rw [hjT]; exact_mod_cast ht⟩
  rw [joinDrv_eqOn (Δ := Δ) (D := D) ((historyProgram c r l').length + 1) htT]
  exact joinDrv_succ_eqOn_of_le hΔj (fun j hj => hDall j hj.le) (hDall _ le_rfl) hle htT

end InteractingSLE.Theorem14.GW2Psm
