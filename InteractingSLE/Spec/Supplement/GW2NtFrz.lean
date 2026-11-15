/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2NtInt
import InteractingSLE.Spec.Supplement.GW2GmClock
import InteractingSLE.Spec.Supplement.GW2GmSlit
import InteractingSLE.Spec.Supplement.GW2SyJoin
import InteractingSLE.Spec.Supplement.GW2TlWord

/-!
# GW2's `noThreshold`: after the candidate's own cap the explored curve is the interior slit

Packet PROVE-GW2-NOTHR (round 2, decision D38). The explored driver of the schedule instance is the joined driver of
the future program, which is constant after the program's last time, the history time plus the candidate's cap. So
after that time the explored trace is the vertical slit of the chart at the cap time: an interior point of
`ℍ \ K_{T+cap}`, hence of `ℍ \ K_T`.

* `joinedDriver_frozen`: a time-ordered joined driver is constant after its last time;
* **`schedW_frozen`**: on the history's success the explored driver is constant after `T + cap`;
* `loewnerTip_zero_mem_H`: the tip of the zero driver at a positive time is interior;
* **`schedTr_mem_of_frozen`**: the explored trace after `T + cap` is an interior point of `ℍ \ K_{T+cap}`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H fwdHull fwdMapInv)
open QuantumZipper.RS (shiftDrive)

namespace InteractingSLE.Theorem14.GW2Nt

open Sec5.Prop513Schedule Sec5.Prop513TreeExtract Sec7.StripSideHeightProb GW2TipSystem GW2TipSystem.RootC24
  GW2TipSystem.RootJ31

/-! ### The joined driver after the last time -/

/-- **A time-ordered joined driver is constant after its last time.** -/
theorem joinedDriver_frozen {Ω : Type*} (E : ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞) (ω : Ω) (he : ∀ k, (E k ω).1 0 = 0) :
    ∀ (l : List (ℝ × ℝ≥0)) (j : ℕ) (a : ℝ≥0), TimeOrdered a l → ∀ t : ℝ≥0, lastTime a l - a ≤ t →
      joinedDriver E j a l ω t = joinedDriver E j a l ω (lastTime a l - a)
  | [], _, _, _, _, _ => rfl
  | (p :: l), j, a, hl, t, ht => by
    have hl' : TimeOrdered p.2 l := timeOrdered_tail hl
    have hap : a ≤ p.2 := hl.2 p List.mem_cons_self
    have hlast : p.2 ≤ lastTime p.2 l := le_lastTime hl'
    have hL : lastTime a (p :: l) = lastTime p.2 l := rfl
    rw [hL] at ht ⊢
    change catPath (E j ω).1 (p.2 - a) (joinedDriver E (j + 1) p.2 l ω) t =
      catPath (E j ω).1 (p.2 - a) (joinedDriver E (j + 1) p.2 l ω) (lastTime p.2 l - a)
    have hT₀ : p.2 - a ≤ lastTime p.2 l - a := tsub_le_tsub_right hlast a
    have hdiff : lastTime p.2 l - a - (p.2 - a) = lastTime p.2 l - p.2 := tsub_tsub_tsub_cancel_right hap
    have hih := joinedDriver_frozen E ω he l (j + 1) p.2 hl'
    by_cases htp : t ≤ p.2 - a
    · rw [le_antisymm (htp.trans hT₀) ht]
    · have htp' : p.2 - a < t := lt_of_not_ge htp
      rw [catPath, if_neg htp]
      by_cases hLp : lastTime p.2 l - a ≤ p.2 - a
      · -- the last time is the start of the last instruction
        have hLeq : lastTime p.2 l = p.2 := by
          have h1 : lastTime p.2 l - a = p.2 - a := le_antisymm hLp hT₀
          have h2 := congrArg (· + a) h1
          simp only [tsub_add_cancel_of_le (hap.trans hlast), tsub_add_cancel_of_le hap] at h2
          exact h2
        have hz : lastTime p.2 l - p.2 = 0 := by rw [hLeq, tsub_self]
        rw [hih (t - (p.2 - a)) (by rw [hz]; exact zero_le), hz, joinedDriver_zero E ω he, add_zero,
          catPath, if_pos hLp, hLeq]
      · rw [catPath, if_neg hLp, hih _ ?_, hih (lastTime p.2 l - a - (p.2 - a)) (by rw [hdiff])]
        rw [← hdiff]
        exact tsub_le_tsub_right ht _

/-! ### The explored driver after the cap -/

section Sched

variable {Ω : Type*} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
  (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)

/-- **On the history's success the explored driver is constant after `T + cap`.** -/
theorem schedW_frozen (hord : TimeOrdered 0 (historyProgram c r l)) {ω : Ω} (hold : oldSuccess c r l ω) {t : ℝ≥0}
    (ht : historyTime c r l + candidateCap c r a ≤ t) :
    GW2Rd.schedW c r l a t ω = GW2Rd.schedW c r l a (historyTime c r l + candidateCap c r a) ω := by
  have h1 := congrFun (GW2Rd.schedW_of_oldSuccess c r l a hold) t
  have h2 := congrFun (GW2Rd.schedW_of_oldSuccess c r l a hold) (historyTime c r l + candidateCap c r a)
  rw [h1, h2]
  have hlast := Gm.lastTime_futureProgram c r l a
  have hfr := joinedDriver_frozen (fun j (R : Fin (futureProgram c r l a).length → Exist.StagedLaw.RecData) =>
      (recordDriver R j, (⊤ : ℝ≥0∞))) (programRecords c (rootPt r.1) (futureProgram c r l a) ω)
    (fun k => recordDriver_zero _ k) (futureProgram c r l a) 0 0
    (GW2Rd.timeOrdered_futureProgram c r l a hord) t (by rw [hlast, tsub_zero]; exact ht)
  rw [hlast, tsub_zero] at hfr
  exact hfr

end Sched

/-- **The tip of a driver vanishing on `[0, u]` at `u > 0` is interior** (the vertical slit). -/
theorem loewnerTip_mem_H_of_zero {W : ℝ → ℝ} {u : ℝ} (hu : 0 < u) (hW : ∀ r ∈ Icc (0 : ℝ) (u + 1), W r = 0) :
    loewnerTip W u ∈ H := by
  set W₀ : ℝ → ℝ := fun s : ℝ => (fun _ : ℝ≥0 => (0 : ℝ)) s.toNNReal with hW₀
  have hL := isLoewnerTrace_of_isGeneratingTrace Gm.isGeneratingTrace_zero_slit
  have hLT : IsLoewnerTraceLT W₀ u (fun s : ℝ => Gm.slitTrace s.toNNReal) :=
    ⟨hL.1, hL.2.1.mono Ico_subset_Ici_self, fun t ht _ => hL.2.2 t ht⟩
  have hW₀c : Continuous W₀ := continuous_const
  have hW₀0 : W₀ 0 = 0 := rfl
  have heq : fwdMapInv W u = fwdMapInv W₀ u :=
    fwdMapInv_eq_of_eqOn (t₂ := u + 1) hu.le (by linarith) fun r hr => by rw [hW r hr]
  unfold loewnerTip
  rw [heq, TraceClose.extendFrom_zero_eq hLT hW₀c hW₀0 hu (hL.2.1.mono Icc_subset_Ici_self)]
  change 0 < (Gm.slitTrace u.toNNReal).im
  rw [Gm.slitTrace_im, Real.coe_toNNReal _ hu.le]
  positivity

/-- **After `T + cap` the explored trace is an interior point of `ℍ \ K_{T+cap}`** (history's success, a generating
trace of the explored driver on `[0, ∞)`). -/
theorem schedTr_mem_of_frozen {Ω : Type*} [MeasurableSpace Ω] (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (hord : TimeOrdered 0 (historyProgram c r l)) {ω : Ω}
    (hold : oldSuccess c r l ω) {η : ℝ≥0 → ℂ} (hη : IsGeneratingTrace (fun t => GW2Rd.schedW c r l a t ω) ⊤ η)
    {τ : ℝ≥0} (hτ : historyTime c r l + candidateCap c r a < τ) :
    η τ ∈ H \ fwdHull (fun q : ℝ => GW2Rd.schedW c r l a q.toNNReal ω)
      ((historyTime c r l + candidateCap c r a : ℝ≥0) : ℝ) := by
  set A : ℝ≥0 := historyTime c r l + candidateCap c r a with hA
  set W : ℝ → ℝ := fun q : ℝ => GW2Rd.schedW c r l a q.toNNReal ω with hWdef
  have hL := isLoewnerTrace_of_isGeneratingTrace hη
  have hc := (GW2Rd.continuous_schedW c r l a ω)
  have hWc : Continuous W := hc.comp continuous_real_toNNReal
  have hW0 : W 0 = 0 := by simp only [hWdef, Real.toNNReal_zero, GW2Rd.schedW_zero]
  have hu : (0 : ℝ) < (τ : ℝ) - A := by
    have : (A : ℝ) < τ := hτ
    linarith
  have htip : loewnerTip (shiftDrive W A) ((τ : ℝ) - A) ∈ H := by
    refine loewnerTip_mem_H_of_zero hu fun q hq => ?_
    simp only [QuantumZipper.RS.shiftDrive, hWdef]
    have e1 : ((A : ℝ) + q).toNNReal = A + q.toNNReal := by
      rw [Real.toNNReal_add A.coe_nonneg hq.1, Real.toNNReal_coe]
    rw [e1, Real.toNNReal_coe, schedW_frozen c r l a hord hold le_self_add, sub_self]
  have hmem := Gm.mem_diff_of_shiftTip_mem_H hL hWc hW0 A.coe_nonneg hu.le htip
  have e2 : ((A : ℝ) + ((τ : ℝ) - A)).toNNReal = τ := by rw [add_sub_cancel, Real.toNNReal_coe]
  simpa only [e2] using hmem

end InteractingSLE.Theorem14.GW2Nt
