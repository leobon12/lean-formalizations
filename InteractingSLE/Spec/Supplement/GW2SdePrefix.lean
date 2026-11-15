/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2SdeNeeds
import InteractingSLE.Spec.Supplement.GW2Root2Cap
import InteractingSLE.Spec.Sec5.Prop513SchedulePrefix
import InteractingSLE.Spec.Supplement.GW2RootJ31Program
import InteractingSLE.Spec.Supplement.GW2RootJ31Joined

/-!
# GW2's retained stopped SDE: part (II) for ROOT2's joined explored driver

Packet PROVE-GW2-SDE (round 2). The target `StageInst.Good.prefix_retained` (part (II): the relative prefix record is
`c.sigma r l`-measurable up to null sets) was reduced by `StageInst.prefix_retained_of_path` to the explored driver on
`[0, T]` being so. Here it is PROVED when the explored driver is ROOT2's joined driver of a candidate's future program
(`RootJ31.joinedRead (futureProgram c r l a) (programRecords …)`) on `[0, lastTime 0 (historyProgram c r l)]`:

* `joinedDriver_append_eq`: appending pieces does not change a joined driver before the last switch time of the
  original program, for ANY (not necessarily time-ordered) program (`Prop513Schedule.joinedDriver_prefix` without its
  ordering hypothesis);
* `joinedRead_append_eq`: the same for ROOT2's record-indexed `joinedRead`;
* **`joinedRead_future_eq_history`**: before the last history time the future program's joined driver is the history
  program's (the history records do not change when a switch is appended: `stopRec_schedSpec_append`);
* **`measurable_joinedRead_history_sigma`**: the history program's joined driver is `c.sigma r l`-measurable;
* **`comap_joinedRead_future_le_sigma`**, **`StageInst.prefix_retained_of_joined`**: part (II) for an instance whose
  explored driver is the joined future driver up to its stage start `T ≤ lastTime 0 (historyProgram c r l)`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter MeasureTheory Topology
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2Sde

open Exist.StagedLaw GW2TipSystem GW2TipSystem.RootC24 GW2TipSystem.RootJ31 Sec5.Prop513TreeExtract
  Sec5.Prop513Schedule Sec7.StripSideHeightProb GW2Schedule Supp8.GB6 Supp8.GB6.HullId Supp8.RelSafe GW2Rd

/-- **Appending pieces leaves a joined driver unchanged before the last switch time** (any program). -/
theorem joinedDriver_append_eq {Ω : Type*} {E F : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞} (ω : Ω)
    (hF : ∀ k, (F k ω).1 0 = 0) (j : ℕ) (a : ℝ≥0) (l tail : List (ℝ × ℝ≥0))
    (he : ∀ i, j ≤ i → i < j + l.length → E i ω = F i ω) {t : ℝ≥0} (ht : t ≤ lastTime a l - a) :
    joinedDriver E j a l ω t = joinedDriver F j a (l ++ tail) ω t := by
  induction l generalizing j a t with
  | nil =>
    have ht0 : t = 0 := by simpa only [lastTime, tsub_self, nonpos_iff_eq_zero] using ht
    rw [ht0]
    exact (joinedDriver_zero F ω hF j a tail).symm
  | cons p l ih =>
    change catPath (E j ω).1 (p.2 - a) (joinedDriver E (j + 1) p.2 l ω) t =
      catPath (F j ω).1 (p.2 - a) (joinedDriver F (j + 1) p.2 (l ++ tail) ω) t
    rw [he j le_rfl (by simp only [List.length_cons]; omega)]
    by_cases htp : t ≤ p.2 - a
    · simp only [catPath, htp, ↓reduceIte]
    · simp only [catPath, htp, ↓reduceIte]
      congr 1
      refine ih (j + 1) p.2 (fun i hji hi => he i (by omega) (by simp only [List.length_cons]; omega)) ?_
      have ht' : t ≤ lastTime p.2 l - a := ht
      exact tsub_le_iff_right.2 (ht'.trans tsub_le_tsub_add_tsub)

/-- A joined driver evaluated at a fixed sample is the joined driver of the frozen family. -/
theorem joinedDriver_eq_const {Ω : Type*} (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω : Ω) (j : ℕ) (a : ℝ≥0)
    (l : List (ℝ × ℝ≥0)) : joinedDriver E j a l ω = joinedDriver (fun k (_ : Unit) => E k ω) j a l () := by
  induction l generalizing j a with
  | nil => rfl
  | cons p l ih =>
    funext t
    change catPath (E j ω).1 (p.2 - a) (joinedDriver E (j + 1) p.2 l ω) t =
      catPath (E j ω).1 (p.2 - a) (joinedDriver (fun k (_ : Unit) => E k ω) (j + 1) p.2 l ()) t
    rw [ih]

/-- **ROOT2's joined read is unchanged by appending pieces** before the last switch time, when the earlier records
agree. -/
theorem joinedRead_append_eq (L tail : List (ℝ × ℝ≥0)) (Rh : Fin L.length → RecData)
    (Rf : Fin (L ++ tail).length → RecData)
    (hR : ∀ (i : ℕ) (hi : i < L.length) (hi' : i < (L ++ tail).length), Rh ⟨i, hi⟩ = Rf ⟨i, hi'⟩)
    {t : ℝ≥0} (ht : t ≤ lastTime 0 L) : joinedRead L Rh t = joinedRead (L ++ tail) Rf t := by
  unfold joinedRead
  rw [joinedDriver_eq_const _ Rh, joinedDriver_eq_const _ Rf]
  refine joinedDriver_append_eq () (fun k => recordDriver_zero Rf k) 0 0 L tail (fun i _ hi => ?_)
    (by simpa only [tsub_zero] using ht)
  have hi' : i < (L ++ tail).length := by rw [List.length_append]; omega
  have hiL : i < L.length := by omega
  simp only [recordDriver, hiL, hi', ↓reduceDIte, hR i hiL hi']

variable {Ω : Type u} [MeasurableSpace Ω]

/-- **Before the last history time, the future program's joined driver is the history program's.** -/
theorem joinedRead_future_eq_history (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q))
    (a : ℕ) (ω : Ω) {t : ℝ≥0} (ht : t ≤ lastTime 0 (historyProgram c r l)) :
    joinedRead (futureProgram c r l a) (programRecords c (rootPt r.1) (futureProgram c r l a) ω) t =
      joinedRead (historyProgram c r l) (programRecords c (rootPt r.1) (historyProgram c r l) ω) t := by
  unfold futureProgram
  refine (joinedRead_append_eq _ _ _ _ (fun i hi hi' => ?_) ht).symm
  exact (stopRec_schedSpec_append c.hκ c.h12p c.βA c.c₀ c.h (rootPt r.1) _ hi ω).symm

/-- **The history program's joined driver is `c.sigma r l`-measurable.** -/
theorem measurable_joinedRead_history_sigma (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (t : ℝ≥0) :
    Measurable[c.sigma r l] fun ω =>
      joinedRead (historyProgram c r l) (programRecords c (rootPt r.1) (historyProgram c r l) ω) t := by
  have hlen : (historyProgram c r l).length = (entryList l).length + 1 := by
    simp only [historyProgram, schedOf, List.length_cons, List.length_reverse]
  have hsig : c.sigma r l = stageSigma c.hκ c.h12p c.βA c.c₀ c.h c.s c.W c.ζ
      (schedSpec (rootPt r.1) (historyProgram c r l)) (historyProgram c r l).length := by
    rw [hlen]
    rfl
  rw [hsig]
  exact ((measurable_pi_apply t).comp (measurable_joinedRead (historyProgram c r l))).comp
    (measurable_snd.comp (comap_measurable _))

/-- **The future program's joined driver before the last history time is `c.sigma r l`-measurable.** -/
theorem comap_joinedRead_future_le_sigma (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) {t : ℝ≥0} (ht : t ≤ lastTime 0 (historyProgram c r l)) :
    MeasurableSpace.comap (fun ω =>
      joinedRead (futureProgram c r l a) (programRecords c (rootPt r.1) (futureProgram c r l a) ω) t)
        inferInstance ≤ c.sigma r l := by
  have e : (fun ω =>
      joinedRead (futureProgram c r l a) (programRecords c (rootPt r.1) (futureProgram c r l a) ω) t) =
      fun ω => joinedRead (historyProgram c r l) (programRecords c (rootPt r.1) (historyProgram c r l) ω) t :=
    funext fun ω => joinedRead_future_eq_history c r l a ω ht
  rw [e]
  exact (measurable_joinedRead_history_sigma c r l t).comap_le

/-- **Part (II) for an instance exploring the joined future driver** up to its stage start
`T ≤ lastTime 0 (historyProgram c r l)` (`StageInst.prefix_retained_of_path` with
`comap_joinedRead_future_le_sigma`). -/
theorem StageInst.prefix_retained_of_joined {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q}
    {l : List (EntryIdx c.Θ c.Q)} (I : StageInst Ω) (a : ℕ)
    (hGT : ∀ ω ∈ I.GT, PhysGood c.s I.W c.W c.ζ I.γ c.α ω) (hWm : ∀ t, Measurable (I.W t))
    (hGTm : MeasurableSet I.GT)
    (hGTae : ∀ᵐ ω ∂c.P, ω ∈ I.GT ↔ gb6Rec c.s c.W c.ζ ω ∈ gb6TS c.s)
    (hver : IsGB6RelVersionR c.s c.P I.W c.W c.ζ I.γ c.α I.R I.V)
    (hT : I.T ≤ lastTime 0 (historyProgram c r l))
    (hW : ∀ t ≤ I.T, ∀ ω,
      I.W t ω = joinedRead (futureProgram c r l a) (programRecords c (rootPt r.1) (futureProgram c r l a) ω) t) :
    MeasurableSpace.comap (stgPreRec c.s I.W c.W c.ζ I.GT I.V I.T I.R) inferInstance ≤
      LocalSets.aeSigma (c.sigma r l) c.P := by
  refine I.prefix_retained_of_path hGT hWm hGTm hGTae hver fun t htT => ?_
  have e : I.W t = fun ω =>
      joinedRead (futureProgram c r l a) (programRecords c (rootPt r.1) (futureProgram c r l a) ω) t :=
    funext fun ω => hW t htT ω
  rw [e]
  exact (comap_joinedRead_future_le_sigma c r l a (htT.trans hT)).trans (LocalSets.le_aeSigma _ _)

/-- ROOT2's history time is the last switch time of the history program. -/
theorem historyTime_eq_lastTime (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) :
    historyTime c r l = lastTime 0 (historyProgram c r l) := by
  have hlen : (historyProgram c r l).length = (entryList l).length + 1 := by
    simp only [historyProgram, schedOf, List.length_cons, List.length_reverse]
  have hne : historyProgram c r l ≠ [] := by
    simp only [historyProgram, schedOf, ne_eq, reduceCtorEq, not_false_eq_true]
  unfold historyTime
  rw [hlen, lastTime_eq_getLast 0 _ hne, List.getLast_eq_getElem]
  simp only [schedTime, hlen, Nat.add_sub_cancel]
  rw [List.getD_eq_getElem _ _ (by omega)]

/-- **Part (II) at ROOT2's stage start**: an instance starting at the history time and exploring the joined future
driver up to it. -/
theorem StageInst.prefix_retained_of_joined_historyTime {c : SourceData Ω} {r : ScaledRootIdx c.Θ c.Q}
    {l : List (EntryIdx c.Θ c.Q)} (I : StageInst Ω) (a : ℕ)
    (hGT : ∀ ω ∈ I.GT, PhysGood c.s I.W c.W c.ζ I.γ c.α ω) (hWm : ∀ t, Measurable (I.W t))
    (hGTm : MeasurableSet I.GT) (hGTae : ∀ᵐ ω ∂c.P, ω ∈ I.GT ↔ gb6Rec c.s c.W c.ζ ω ∈ gb6TS c.s)
    (hver : IsGB6RelVersionR c.s c.P I.W c.W c.ζ I.γ c.α I.R I.V) (hT : I.T = historyTime c r l)
    (hW : ∀ t ≤ I.T, ∀ ω,
      I.W t ω = joinedRead (futureProgram c r l a) (programRecords c (rootPt r.1) (futureProgram c r l a) ω) t) :
    MeasurableSpace.comap (stgPreRec c.s I.W c.W c.ζ I.GT I.V I.T I.R) inferInstance ≤
      LocalSets.aeSigma (c.sigma r l) c.P :=
  I.prefix_retained_of_joined a hGT hWm hGTm hGTae hver (hT.trans (historyTime_eq_lastTime c r l)).le hW

end InteractingSLE.Theorem14.GW2Sde
