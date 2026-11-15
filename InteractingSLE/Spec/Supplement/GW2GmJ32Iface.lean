/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2GmJ32Geom
import InteractingSLE.Spec.Supplement.GW2RootJ31Launch

/-!
# J32's interface for the other D-specific GW2 work (ruling R110)

Packet PROVE-GW2-GEOM2. Statements for re-targeting the D-specific GW2 work (the buffer property,
`PkgGoodStatement` / `FrameWordStatement` in `GW2SdeNeeds`) from `RootJ31.constructionFamily` to
`RootJ32.constructionFamily`.

**What is literally shared** (`GW2GmJ32Data`, all `rfl`): the protected root event `G`, the candidate angles,
the failure `F` (J31's buffer), the clock, the drift bound, the reach and slow sets, the sample lifetime
(`sourceSample_fst`), the records `RootJ31.futurePair` and every K32 buffer/contact fact stated through them.
**What differs:** the sample's readings, the stage driver, `X`, `γ`, `S` (read through J32's running-maximum
inverse clock), hence the tests and alive events.

* `alive_subset_G`, **`alive_spec`**: a J32-alive history lies in the protected root event and is a successful,
  time-ordered physical history (the facts J31's alive events supplied);
* `allSucc_of_alive`, `run_live_chart_of_alive`, `next_launch_of_alive`: J31's launch facts for J32's alive events;
* **`test_spec`**: a J32-passed test is after the history time and before the buffer, with a live sample;
* **`ae_runMax_eq`** (the agreement of R110): almost surely, at every live sample, J32's capacity reader (the
  running maximum) is `arctan` of J31's capacity reader on `[0, T + F]`;
* **`ae_capacityDriverRead_eq`**: almost surely, at every live sample, J32's driver reader at capacities up to
  the buffer's is I30's exact-horizon reader of the joined trace (every J31 result proved through that reader on
  `[0, T + F]` transfers);
* `capacityDriverRead_eq_J31_of_inverse`: deterministic: wherever J31's inverse clock on the whole cap window
  agrees with the exact-horizon one, J31's and J32's driver readers coincide.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootJ32

open Exist Staged StagedLaw Restart GW2Schedule GW2Tip RootC24 RootK3

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

theorem alive_subset_G (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) :
    ∀ l : List (EntryIdx c.Θ c.Q),
      (experiment c r).data.alive ((construction c).G r) l ⊆ RootCv.coverEvent c r
  | [] => fun _ h => h
  | _ :: l => fun _ h => alive_subset_G c r l h.1

/-- **A J32-alive history is protected, successful and time-ordered.** -/
theorem alive_spec (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (ω : Ω)
    (ha : ω ∈ (experiment c r).data.alive ((construction c).G r) l) :
    ω ∈ RootCv.coverEvent c r ∧ RootJ31.oldSuccess c r l ω ∧
      Sec5.Prop513Schedule.TimeOrdered 0 (RootJ31.historyProgram c r l) :=
  ⟨alive_subset_G c r l ha, oldSuccess_of_alive c r l ω ha,
    timeOrdered_historyProgram_of_alive c r l ω ha⟩

theorem allSucc_of_alive (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (ω : Ω)
    (ha : ω ∈ (experiment c r).data.alive ((construction c).G r) l) :
    AllSucc (specDelta (schedSpec (rootPt r.1) (RootJ31.historyProgram c r l)))
      (fun j => canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h
        (schedSpec (rootPt r.1) (RootJ31.historyProgram c r l)) j ω)
      (RootJ31.historyProgram c r l).length :=
  (RootJ31.oldSuccess_iff_allSucc c r l ω).mp (oldSuccess_of_alive c r l ω ha)

theorem run_live_chart_of_alive (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (ω : Ω)
    (ha : ω ∈ (experiment c r).data.alive ((construction c).G r) l) :
    let spec := schedSpec (rootPt r.1) (RootJ31.historyProgram c r l)
    let E := fun j => canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h spec j ω
    IsLive (stStatus (ExplState.run c.κ c.b c.jumps spec E (RootJ31.historyProgram c r l).length)) ∧
      stChart (ExplState.run c.κ c.b c.jumps spec E (RootJ31.historyProgram c r l).length) =
        succChart (rootPt r.1) (specDelta spec) E (RootJ31.historyProgram c r l).length :=
  (run_gw2 (κ := c.κ) (b := c.b) (jumps := c.jumps) rfl
    (isFlowProg_spec _ true _) (specDelta_ne_top _) _ _
      (by simp only [schedSpec, length_scheduleProgram]; exact le_rfl)).1
        (allSucc_of_alive c r l ω ha)

theorem next_launch_of_alive (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω)
    (ha : ω ∈ (experiment c r).data.alive ((construction c).G r) l) :
    let spec := schedSpec (rootPt r.1) (RootJ31.futureProgram c r l a)
    let E := fun j => canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h spec j ω
    (ExplState.run c.κ c.b c.jumps spec E ((RootJ31.historyProgram c r l).length + 1)).2.2.2.1
      (RootJ31.historyProgram c r l).length =
        some (succChart (rootPt r.1) (specDelta spec) E (RootJ31.historyProgram c r l).length,
          (RootJ31.candidateAngle c r a : ℝ)) := by
  let spec := schedSpec (rootPt r.1) (RootJ31.futureProgram c r l a)
  let E := fun j => canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h spec j ω
  have hs := Gm.allSucc_future_of_oldSuccess c r l a ω (oldSuccess_of_alive c r l ω ha)
  have hk : (RootJ31.historyProgram c r l).length < spec.2.2.length := by
    simp only [spec, schedSpec, length_scheduleProgram, RootJ31.futureProgram,
      List.length_append, List.length_singleton]
    omega
  have hl := (launches_run_gw2 (κ := c.κ) (b := c.b) (jumps := c.jumps)
    (spec := spec) rfl (isFlowProg_spec _ true _) (specDelta_ne_top _) E hk).1 hs
  have hθ : specAngle spec (RootJ31.historyProgram c r l).length =
      (RootJ31.candidateAngle c r a : ℝ) := RootH29.specAngle_last _ _ _ _
  have hl' : (ExplState.run c.κ c.b c.jumps spec E
      ((RootJ31.historyProgram c r l).length + 1)).2.2.2.1 (RootJ31.historyProgram c r l).length =
      some (succChart (rootPt r.1) (specDelta spec) E (RootJ31.historyProgram c r l).length,
        specAngle spec (RootJ31.historyProgram c r l).length) := hl
  rw [hθ] at hl'
  exact hl'

/-- **A J32-passed test** is after the history time and before the buffer, with a live sample. -/
theorem test_spec (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (q : c.Q) (ω : Ω)
    (ht : ω ∈ (experiment c r).data.tests l a q) :
    RootJ31.historyTime c r l < (q : ℝ≥0) ∧
      (q : ℝ≥0) < RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ω ∧
      0 < (RootJ31.sourceSample c r l a ω).1 ∧ 0 < (sourceSample c r l a ω).1 := by
  have hlive := live_of_entry_lt_failure c r l a ω (ht.1.trans ht.2.1)
  refine ⟨NNReal.coe_lt_coe.mp ((sourceEntry_ge_historyTime c r l a ω).trans_lt ht.1), ?_, hlive,
    by rw [sourceSample_fst]; exact hlive⟩
  have h := ht.2.1
  change ((q : ℝ≥0) : ℝ) <
    ((RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ω : ℝ≥0) : ℝ) at h
  exact_mod_cast h

/-- **The agreement of ruling R110**: almost surely, at every live sample, J32's capacity reader (the running
maximum) is `arctan` of J31's capacity reader on the live window `[0, T + F]`. -/
theorem ae_runMax_eq (h13 : Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) :
    ∀ᵐ ω ∂c.P, ∀ (l : List (EntryIdx c.Θ c.Q)) (a : ℕ),
      0 < (RootJ31.sourceSample c r l a ω).1 →
      ∀ t ≤ RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ω,
        runMax (rootPt r.1) c.s t (RootJ31.futurePair c r l a ω) =
          Real.arctan (RootH29.forwardCapacity (rootPt r.1) c.s t (RootJ31.futurePair c r l a ω)) := by
  filter_upwards [Gm.ae_live_clock h13 c r] with ω hω l a hlive t ht
  obtain ⟨-, -, -, hm, hc, -, -⟩ := hω l a hlive
  exact runMax_eq_of_clock hm.monotoneOn hc ht

/-- **J32's driver reader on the live window is I30's exact-horizon reader of the joined trace**, almost
surely at every live sample. -/
theorem ae_capacityDriverRead_eq (h13 : Theorem13Statement.{u}) (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) :
    ∀ᵐ ω ∂c.P, ∀ (l : List (EntryIdx c.Θ c.Q)) (a : ℕ),
      0 < (RootJ31.sourceSample c r l a ω).1 →
      ∀ c' : ℝ≥0, (c' : ℝ) ≤ RootH29.forwardCapacity (rootPt r.1) c.s
          (RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ω)
          (RootJ31.futurePair c r l a ω) →
        capacityDriverRead (rootPt r.1) c.s (RootJ31.historyTime c r l + RootJ31.candidateCap c r a)
            c' (RootJ31.futurePair c r l a ω) =
          RootJ31.capacityDriverRead (rootPt r.1) c.s
            (RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ω) c'
            (cfRec c.s c.W c.ζ ω, recOf
              ((RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ω : ℝ≥0) : ℝ≥0∞)
              (Gm.futureJoined c r l a ω, ⊤)) := by
  filter_upwards [Gm.ae_live_clock h13 c r] with ω hω l a hlive c' hc'
  obtain ⟨γ, hγ, -, hm, hc, -, -⟩ := hω l a hlive
  obtain ⟨hJ, hJ0⟩ := Gm.continuous_futureJoined c r l a ω
  have hFL : RootJ31.historyTime c r l + RootJ31.sourceBuffer c r l a ω ≤
      RootJ31.historyTime c r l + RootJ31.candidateCap c r a :=
    add_le_add le_rfl (RootJ31.sourceBuffer_le c r l a ω)
  have hpe := Gm.futurePair_eq_recOfDriver c r l a ω
  rw [hpe] at hm hc hc' ⊢
  exact capacityDriverRead_eq_of_clock hJ hJ0 hγ hFL hFL hm.monotoneOn hc hc'

/-- Deterministic: where J31's inverse clock on the whole cap window agrees with the exact-horizon inverse at
all levels up to the capacity at `w`, J31's and J32's driver readers coincide at capacities up to it. -/
theorem capacityDriverRead_eq_J31_of_inverse {x : ℝ} {s w v : ℝ≥0} {p : RecData × RecData}
    (hwv : w ≤ v) (hm : MonotoneOn (fun t => RootH29.forwardCapacity x s t p) (Icc 0 w))
    (hc : ContinuousOn (fun t => RootH29.forwardCapacity x s t p) (Icc 0 w))
    (hinv : ∀ u : ℝ≥0, (u : ℝ) ≤ RootH29.forwardCapacity x s w p →
      RootI30.clockInverse x s v u p = RootI30.clockInverse x s w u p)
    {c : ℝ≥0} (hcw : (c : ℝ) ≤ RootH29.forwardCapacity x s w p) :
    capacityDriverRead x s v c p = RootJ31.capacityDriverRead x s v c p := by
  unfold capacityDriverRead RootJ31.capacityDriverRead
  refine RootB23.traceDriverRead_congr_prefix fun u hu => ?_
  have hu' : (u : ℝ) ≤ RootH29.forwardCapacity x s w p := (NNReal.coe_le_coe.2 hu.2).trans hcw
  change capacityTipRead x s v u p = RootI30.capacityTipRead x s v u p
  rw [capacityTipRead_eq_of_clock hwv hm hc hu', RootI30.capacityTipRead, RootI30.capacityTipRead,
    hinv u hu']

end InteractingSLE.Theorem14.GW2TipSystem.RootJ32
