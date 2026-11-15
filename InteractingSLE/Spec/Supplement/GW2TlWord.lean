/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2TlCoord
import InteractingSLE.Spec.Supplement.GW2GmPrefix
import InteractingSLE.Spec.Supplement.GW2GmNest
import InteractingSLE.Spec.Supplement.GW2SwcCarrier
import InteractingSLE.Spec.Supplement.GW2SdePrefix

/-!
# N4 item 1 in launch coordinates, part 5: the launch word and the candidate read off the explored driver

Packet PROVE-GW2-RELDET (decision D20). On the success of the history (time-ordered, good records), the explored
driver `schedW` is the joined driver of the canonical pieces. Its pieces are the stopped records of the history and
the candidate's own driver:

* `pastRecOf c r l a w`: the history's stopped records read off a driver path `w` (only `w` on `[0, T]` is read);
  `launchWordOf c r l a w`: the canonical word of the launch (`pastWord` of these records); measurable
  (`measurable_launchWordOf`) and decided by `w` up to `T` (`launchWordOf_congr`);
* **`launchWordOf_schedW`**: on the history's success, the word read off the explored driver is the canonical word of
  the candidate's launch (`GW2Schedule.canonWord`);
* **`shiftNN_schedW`**: on the history's success, the explored driver after `T` is the candidate's own driver before
  its cap and its lifetime.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Rd

open GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 GW2TipSystem.Swc GW2Schedule GW2Tip Exist Exist.Staged
  Exist.StagedLaw Sec5.Prop513Schedule
open Restart (BoundaryWord)

section Word

variable {Ω : Type u} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
  (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)

/-- The start time of instruction `i` of the future program. -/
abbrev pieceStart (i : ℕ) : ℝ≥0 := schedTime 0 (futureProgram c r l a) i

/-- The own time of instruction `i` of the future program. -/
abbrev pieceLen (i : ℕ) : ℝ≥0 := (specDelta (GW2Olm.futSpec c r l a) i).toNNReal

/-- **The history's stopped records read off a driver path** (only the path on `[0, T]` is read). -/
def pastRecOf (w : ℝ≥0 → ℝ) : PastData (GW2Olm.curIdx c r l) := fun i =>
  ((fun q : ℚ => w (min (historyTime c r l) (pieceStart c r l a i + min (q : ℝ).toNNReal (pieceLen c r l a i))) -
      w (min (historyTime c r l) (pieceStart c r l a i))),
    specDelta (GW2Olm.futSpec c r l a) i, false)

/-- **The launch word read off a driver path.** -/
def launchWordOf (w : ℝ≥0 → ℝ) : BoundaryWord :=
  pastWord c.βA c.c₀ (rootPt r.1) (specAngle (GW2Olm.futSpec c r l a)) (GW2Olm.curIdx c r l)
    (pastRecOf c r l a w)

theorem measurable_pastRecOf : Measurable (pastRecOf c r l a) := by
  refine measurable_pi_iff.2 fun i => Measurable.prodMk ?_ measurable_const
  exact measurable_pi_iff.2 fun q => (measurable_pi_apply _).sub (measurable_pi_apply _)

theorem measurable_launchWordOf : Measurable (launchWordOf c r l a) :=
  (measurable_pastWord c.βA c.c₀ (rootPt r.1) _ c.hβA.1 _).comp (measurable_pastRecOf c r l a)

/-- **The launch word only reads the path up to the history time.** -/
theorem launchWordOf_congr {w w' : ℝ≥0 → ℝ} (h : ∀ u ≤ historyTime c r l, w u = w' u) :
    launchWordOf c r l a w = launchWordOf c r l a w' := by
  unfold launchWordOf pastRecOf
  congr 1
  funext i
  simp only [h _ (min_le_left _ _)]

end Word

/-! ### On the history's success -/

section Success

variable {Ω : Type u} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
  (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)

/-- The future program is time-ordered when the history is. -/
theorem timeOrdered_futureProgram (hord : TimeOrdered 0 (historyProgram c r l)) :
    TimeOrdered 0 (futureProgram c r l a) := by
  have hTl : historyTime c r l = lastTime 0 (historyProgram c r l) := Gm.schedTime_length_eq_lastTime _
  refine Gm.timeOrdered_append hord ?_
  change lastTime 0 (historyProgram c r l) ≤ historyTime c r l + _
  rw [← hTl]
  exact le_add_of_nonneg_right zero_le

theorem schedTime_curIdx : schedTime 0 (futureProgram c r l a) (GW2Olm.curIdx c r l) = historyTime c r l := by
  have h2 : schedTime 0 (futureProgram c r l a) (GW2Olm.curIdx c r l) =
      schedTime 0 (historyProgram c r l) (historyProgram c r l).length := schedTime_append 0 _ le_rfl
  rw [h2]
  rfl

variable {c r l a} {ω : Ω}

/-- The pieces of the joined explored driver: on the history's success, the explored driver after the start of
instruction `i ≤ k` is that piece's stopped driver, up to its stop. -/
theorem schedW_piece (hord : TimeOrdered 0 (historyProgram c r l)) (hold : oldSuccess c r l ω)
    (hgood : ∀ (j : ℕ) (hj : j < (futureProgram c r l a).length), LocalExt.IsDrvGood
      (recHist (programRecords c (rootPt r.1) (futureProgram c r l a) ω ⟨j, hj⟩)))
    {i : ℕ} (hi : i ≤ GW2Olm.curIdx c r l) {v : ℝ≥0}
    (hv : (v : ℝ) ≤ stopTime (specDelta (GW2Olm.futSpec c r l a) i) (GW2Olm.futFam c r l a i ω))
    (hJ : Swc.joinTime (specDelta (GW2Olm.futSpec c r l a)) (fun j => GW2Olm.futFam c r l a j ω) i =
      pieceStart c r l a i)
    (hend : pieceStart c r l a i + v ≤ historyTime c r l + candidateCap c r a) :
    schedW c r l a (pieceStart c r l a i + v) ω - schedW c r l a (pieceStart c r l a i) ω =
      stopDrv (specDelta (GW2Olm.futSpec c r l a) i) (GW2Olm.futFam c r l a i ω) v := by
  set Δ := specDelta (GW2Olm.futSpec c r l a) with hΔ
  set D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun j => GW2Olm.futFam c r l a j ω with hD
  set k := GW2Olm.curIdx c r l with hk
  have hreg : IsRegularDriver (D i) :=
    isRegularDriver_canonFam c.hκ c.h12p c.βA c.c₀ _ _ _ c.h i ω
  have hS0 : stopDrv (Δ i) (D i) 0 = 0 := by
    rw [Gm.stopDrv_eq_of_le (by simp only [Real.toNNReal_zero, ENNReal.coe_zero]; exact zero_le)]
    simp only [Real.toNNReal_zero]
    exact hreg.2.1
  have hjoin : ∀ t : ℝ≥0, t ≤ historyTime c r l + candidateCap c r a →
      schedW c r l a t ω = joinDrv Δ D (k + 1) t := by
    intro t ht
    rw [congrFun (schedW_of_oldSuccess c r l a hold) t]
    exact Gm.futureJoined_eq_joinDrv c r l a ω hord hold hgood ht
  have hstart : pieceStart c r l a i ≤ historyTime c r l + candidateCap c r a := le_self_add.trans hend
  rw [hjoin _ hend, hjoin _ hstart]
  have hsucc : joinTime Δ D (i + 1) = joinTime Δ D i + stopTime (Δ i) (D i) := joinTime_succ Δ D i
  have hmem1 : ((pieceStart c r l a i + v : ℝ≥0) : ℝ) ∈ Icc 0 (joinTime Δ D (i + 1)) := by
    refine ⟨by positivity, ?_⟩
    rw [hsucc, hJ, NNReal.coe_add]
    linarith
  have hmem0 : ((pieceStart c r l a i : ℝ≥0) : ℝ) ∈ Icc 0 (joinTime Δ D (i + 1)) := by
    refine ⟨by positivity, ?_⟩
    rw [hsucc, hJ]
    linarith [stopTime_nonneg (Δ i) (D i)]
  rw [joinDrv_eqOn_of_le (Nat.succ_le_succ hi) hmem1, joinDrv_eqOn_of_le (Nat.succ_le_succ hi) hmem0]
  have h3 := shiftDrive_joinDrv_eqOn (Δ := Δ) (D := D) hS0 ⟨v.coe_nonneg, hv⟩
  simp only [QuantumZipper.RS.shiftDrive, hJ] at h3
  rw [NNReal.coe_add]
  exact h3

/-- **The candidate's own driver**: on the history's success, the explored driver after the history time is the
candidate's driver before its cap and its lifetime. -/
theorem shiftNN_schedW (hord : TimeOrdered 0 (historyProgram c r l)) (hold : oldSuccess c r l ω)
    (hgood : ∀ (j : ℕ) (hj : j < (futureProgram c r l a).length), LocalExt.IsDrvGood
      (recHist (programRecords c (rootPt r.1) (futureProgram c r l a) ω ⟨j, hj⟩)))
    {σ : ℝ≥0} (hσ : (σ : ℝ≥0∞) ≤ min (candidateCap c r a : ℝ≥0∞)
      (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).2) :
    Sec7.shiftNN (fun t => schedW c r l a t ω) (historyTime c r l) σ =
      (GW2Olm.futFam c r l a (GW2Olm.curIdx c r l) ω).1 σ := by
  set Δ := specDelta (GW2Olm.futSpec c r l a) with hΔ
  set D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun j => GW2Olm.futFam c r l a j ω with hD
  set k := GW2Olm.curIdx c r l with hk
  have hΔk : Δ k = (candidateCap c r a : ℝ≥0∞) := futureProgram_delta c r l a
  have hs : AllSucc Δ D k := Gm.allSucc_future_of_oldSuccess c r l a ω hold
  have hlen : k ≤ (futureProgram c r l a).length := by
    simp only [hk, GW2Olm.curIdx, futureProgram, List.length_append, List.length_singleton]; omega
  have hJ : joinTime Δ D k = pieceStart c r l a k :=
    Gm.joinTime_eq_schedTime (rootPt r.1) (timeOrdered_futureProgram c r l a hord) hlen hs
  have hmin : min (Δ k) (D k).2 ≠ ⊤ := ne_top_of_le_ne_top (specDelta_ne_top _ k) (min_le_left _ _)
  have hσ' : (σ : ℝ≥0∞) ≤ min (Δ k) (D k).2 := by rw [hΔk]; exact hσ
  have hv : (σ : ℝ) ≤ stopTime (Δ k) (D k) := by
    have h1 : σ ≤ (min (Δ k) (D k).2).toNNReal := by
      rw [← ENNReal.coe_le_coe, ENNReal.coe_toNNReal hmin]; exact hσ'
    exact_mod_cast h1
  have hσcap : σ ≤ candidateCap c r a := by
    have := hσ.trans (min_le_left _ _)
    exact_mod_cast this
  have hT : pieceStart c r l a k = historyTime c r l := schedTime_curIdx c r l a
  have h := schedW_piece hord hold hgood le_rfl hv hJ (by rw [hT]; exact add_le_add_right hσcap _)
  rw [hT] at h
  simp only [Sec7.shiftNN]
  rw [h, Gm.stopDrv_eq_of_le (by rw [Real.toNNReal_coe]; exact hσ'), Real.toNNReal_coe]

/-- **The launch word read off the explored driver is the canonical word of the launch** (on the history's
success). -/
theorem launchWordOf_schedW (hord : TimeOrdered 0 (historyProgram c r l)) (hold : oldSuccess c r l ω)
    (hgood : ∀ (j : ℕ) (hj : j < (futureProgram c r l a).length), LocalExt.IsDrvGood
      (recHist (programRecords c (rootPt r.1) (futureProgram c r l a) ω ⟨j, hj⟩))) :
    launchWordOf c r l a (fun t => schedW c r l a t ω) =
      canonWord c.hκ c.h12p c.βA c.c₀ (specAngle (GW2Olm.futSpec c r l a)) (specDelta (GW2Olm.futSpec c r l a))
        c.κ c.b c.jumps (GW2Olm.futSpec c r l a) c.h (GW2Olm.curIdx c r l) ω := by
  set Δ := specDelta (GW2Olm.futSpec c r l a) with hΔ
  set D : ℕ → (ℝ≥0 → ℝ) × ℝ≥0∞ := fun j => GW2Olm.futFam c r l a j ω with hD
  set k := GW2Olm.curIdx c r l with hk
  have hs : AllSucc Δ D k := Gm.allSucc_future_of_oldSuccess c r l a ω hold
  have hlenL : (futureProgram c r l a).length = k + 1 := by
    simp only [hk, GW2Olm.curIdx, futureProgram, List.length_append, List.length_singleton]
  have hlen : k ≤ (GW2Olm.futSpec c r l a).2.2.length := by
    rw [GW2Schedule.length_scheduleProgram, hlenL]; omega
  unfold launchWordOf canonWord
  congr 1
  rw [pastMap_of_allSucc (κ := c.κ) (b := c.b) (jumps := c.jumps) rfl (isFlowProg_spec (rootPt r.1) true _)
    (specDelta_ne_top _) (GW2Olm.futFam c r l a) hlen hs]
  funext i
  have hi : (i : ℕ) < k := i.2
  have hlt : Δ i < (D i).2 := hs i hi
  have hne : Δ i ≠ ⊤ := specDelta_ne_top _ i
  have hmin : min (Δ i) (D i).2 = Δ i := min_eq_left hlt.le
  have hJi : joinTime Δ D i = pieceStart c r l a i :=
    Gm.joinTime_eq_schedTime (rootPt r.1) (timeOrdered_futureProgram c r l a hord)
      (by rw [hlenL]; omega) (hs.mono hi.le)
  have hstop : stopTime (Δ i) (D i) = (pieceLen c r l a i : ℝ) := by
    simp only [stopTime, hmin]
    rfl
  -- the piece ends before the history time
  have hJk : joinTime Δ D k = (historyTime c r l : ℝ) := by
    have h := Gm.joinTime_eq_schedTime (rootPt r.1) (timeOrdered_futureProgram c r l a hord) (k := k)
      (by rw [hlenL]; omega) hs
    rw [schedTime_curIdx] at h
    exact h
  have hend : pieceStart c r l a i + pieceLen c r l a i ≤ historyTime c r l := by
    have h1 : joinTime Δ D (i + 1) ≤ joinTime Δ D k := joinTime_mono (Nat.succ_le_of_lt hi)
    rw [joinTime_succ, hJi, hstop, hJk] at h1
    exact_mod_cast h1
  unfold pastRecOf recOf readRec retOf
  refine Prod.ext (funext fun q => ?_) (Prod.ext ?_ ?_)
  · have hvl : min (q : ℝ).toNNReal (pieceLen c r l a i) ≤ pieceLen c r l a i := min_le_right _ _
    have h1 : pieceStart c r l a i + min (q : ℝ).toNNReal (pieceLen c r l a i) ≤ historyTime c r l :=
      (add_le_add_right hvl _).trans hend
    have h2 : pieceStart c r l a i ≤ historyTime c r l := le_self_add.trans h1
    dsimp only
    rw [min_eq_right h1, min_eq_right h2]
    have hv : ((min (q : ℝ).toNNReal (pieceLen c r l a i) : ℝ≥0) : ℝ) ≤ stopTime (Δ i) (D i) := by
      rw [hstop]; exact_mod_cast hvl
    rw [schedW_piece hord hold hgood (le_of_lt hi) hv hJi (h1.trans le_self_add)]
    have hvle : (((min (q : ℝ).toNNReal (pieceLen c r l a i) : ℝ≥0) : ℝ).toNNReal : ℝ≥0∞) ≤
        min (Δ i) (D i).2 := by
      rw [Real.toNNReal_coe, hmin, ← ENNReal.coe_toNNReal hne]
      exact ENNReal.coe_le_coe.2 hvl
    rw [Gm.stopDrv_eq_of_le hvle, Real.toNNReal_coe]
    rw [hmin, ← ENNReal.coe_toNNReal hne, ← ENNReal.coe_min, ENNReal.toNNReal_coe]
  · exact hmin.symm
  · have hn : ¬ (GW2Olm.futFam c r l a i ω).2 ≤ specDelta (GW2Olm.futSpec c r l a) i := not_le.2 hlt
    exact (decide_eq_false hn).symm

end Success

end InteractingSLE.Theorem14.GW2Rd
