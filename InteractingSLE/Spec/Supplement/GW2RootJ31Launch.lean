/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootJ31Meas

/-!
# Actual switched launch charts on the concrete alive events

Packet PROVE-T14-GW2ROOT2. The proved physical success flags instantiate
the landed GW2 run theorem. The next candidate launches in its actual
successive mapping-out chart, even before a future test is passed.
No relative-chart SDE or comparison property is assumed.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootJ31

open Exist Staged StagedLaw Restart GW2Schedule GW2Tip RootC24 RootK3

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

/-- The actual retained physical run is live and has the successive Loewner
chart, at every outcome of the constructed alive event. -/
theorem run_live_chart_of_alive (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (ω : Ω)
    (ha : ω ∈ (experiment c r).data.alive ((construction c).G r) l) :
    let spec := schedSpec (rootPt r.1) (historyProgram c r l)
    let E := fun j => canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h spec j ω
    IsLive (stStatus (ExplState.run c.κ c.b c.jumps spec E (historyProgram c r l).length)) ∧
      stChart (ExplState.run c.κ c.b c.jumps spec E (historyProgram c r l).length) =
        succChart (rootPt r.1) (specDelta spec) E (historyProgram c r l).length := by
  exact (run_gw2 (κ := c.κ) (b := c.b) (jumps := c.jumps) rfl
    (isFlowProg_spec _ true _) (specDelta_ne_top _) _ _
      (by simp only [schedSpec, length_scheduleProgram]; exact le_rfl)).1
        (allSucc_of_alive c r l ω ha)

/-- Changing only the next cutoff preserves the successful past, so every
future candidate actually launches in its recorded successive chart. -/
theorem next_launch_of_alive (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω)
    (ha : ω ∈ (experiment c r).data.alive ((construction c).G r) l) :
    let spec := schedSpec (rootPt r.1) (futureProgram c r l a)
    let E := fun j => canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h spec j ω
    (ExplState.run c.κ c.b c.jumps spec E ((historyProgram c r l).length + 1)).2.2.2.1
      (historyProgram c r l).length =
        some (succChart (rootPt r.1) (specDelta spec) E (historyProgram c r l).length,
          (candidateAngle c r a : ℝ)) := by
  let spec := schedSpec (rootPt r.1) (futureProgram c r l a)
  let E := fun j => canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h spec j ω
  have hold := oldSuccess_of_alive c r l ω ha
  have hs : AllSucc (specDelta spec) E (historyProgram c r l).length := by
    intro j hj
    apply (RootCv.recOf_flag_eq_false_iff _ _).mp
    change (stopRec c.hκ c.h12p c.βA c.c₀ c.h
      (schedSpec (rootPt r.1) (futureProgram c r l a)) j ω).2.2 = false
    rw [futureProgram, stopRec_schedSpec_append c.hκ c.h12p c.βA c.c₀ c.h _ _ hj ω]
    exact hold ⟨j, hj⟩
  have hk : (historyProgram c r l).length < spec.2.2.length := by
    simp only [spec, schedSpec, length_scheduleProgram, futureProgram,
      List.length_append, List.length_singleton]
    omega
  have hl := (launches_run_gw2 (κ := c.κ) (b := c.b) (jumps := c.jumps)
    (spec := spec) rfl (isFlowProg_spec _ true _) (specDelta_ne_top _) E hk).1 hs
  have hθ : specAngle spec (historyProgram c r l).length = (candidateAngle c r a : ℝ) :=
    RootH29.specAngle_last _ _ _ _
  have hl' : (ExplState.run c.κ c.b c.jumps spec E
      ((historyProgram c r l).length + 1)).2.2.2.1 (historyProgram c r l).length =
      some (succChart (rootPt r.1) (specDelta spec) E (historyProgram c r l).length,
        specAngle spec (historyProgram c r l).length) := hl
  rw [hθ] at hl'
  exact hl'

end InteractingSLE.Theorem14.GW2TipSystem.RootJ31
