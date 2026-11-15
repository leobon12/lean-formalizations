/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootK32Buffers
import InteractingSLE.Spec.Supplement.GW2JDetR12Alive

/-!
# The actual future buffer gate under the full retained-history kernel

Packet PROVE-T14-GW2ROOT2. COVER and the old flags are known in the literal
retained sigma algebra. Consequently the whole future buffer uses its
live branch under that kernel at almost every alive state. We do not
assume measurability of the still-open inside-window observation gate.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootK32

open Exist Staged StagedLaw Restart GW2Schedule GW2Tip RootC24 RootJ31

variable {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]

omit [StandardBorelSpace Ω] in
/-- Both pieces of the actual buffer gate are retained information. -/
theorem measurableSet_sourceBuffer_gate (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) :
    MeasurableSet[c.sigma r l] {ω | ω ∈ RootCv.coverEvent c r ∧ oldSuccess c r l ω} :=
  (GW2JDetR12.measurableSet_coverEvent_history c r l).inter
    (measurableSet_oldSuccess_rootSigma c r l)

/-- Alive implies that the known gate holds, without any geometry input. -/
theorem sourceBuffer_gate_of_alive (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (ω : Ω)
    (ha : ω ∈ (experiment c r).data.alive ((construction c).G r) l) :
    ω ∈ RootCv.coverEvent c r ∧ oldSuccess c r l ω :=
  ⟨GW2JDetR12.aliveTests_subset _ _ _ l ha, oldSuccess_of_alive c r l ω ha⟩

omit [StandardBorelSpace Ω] in
/-- The next candidate's actual launch needs only the retained success
flags. This is the pathwise form usable under the retained kernel. -/
theorem next_launch_of_oldSuccess (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω) (hold : oldSuccess c r l ω) :
    let spec := schedSpec (rootPt r.1) (futureProgram c r l a)
    let E := fun j => canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h spec j ω
    (ExplState.run c.κ c.b c.jumps spec E ((historyProgram c r l).length + 1)).2.2.2.1
      (historyProgram c r l).length =
        some (succChart (rootPt r.1) (specDelta spec) E (historyProgram c r l).length,
          (candidateAngle c r a : ℝ)) := by
  let spec := schedSpec (rootPt r.1) (futureProgram c r l a)
  let E := fun j => canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h spec j ω
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

/-- Actual old survival persists under the complete retained kernel, at
every alive history. No conditional future law or determination is used. -/
theorem ae_conditional_sourceBuffer_gate_on_alive (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) :
    ∀ᵐ ω₀ ∂c.P, ω₀ ∈ (experiment c r).data.alive ((construction c).G r) l →
      ∀ᵐ ξ ∂condExpKernel c.P (c.sigma r l) ω₀,
        ξ ∈ RootCv.coverEvent c r ∧ oldSuccess c r l ξ := by
  have hmem := Sec7.Aux122Disint.ae_ae_condExpKernel_mem (P := c.P)
    (stageSigma_le c.hβA.1 c.hh.1 c.hcf c.s _ _)
    (measurableSet_sourceBuffer_gate c r l)
  filter_upwards [hmem] with ω₀ hω₀ ha
  exact hω₀ (sourceBuffer_gate_of_alive c r l ω₀ ha)

/-- The full literal future-buffer formula, simultaneously for every
candidate, is valid under the retained kernel at almost every alive state. -/
theorem ae_conditional_sourceBuffer_eq_on_alive (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) :
    ∀ᵐ ω₀ ∂c.P, ω₀ ∈ (experiment c r).data.alive ((construction c).G r) l →
      ∀ᵐ ξ ∂condExpKernel c.P (c.sigma r l) ω₀, ∀ a,
        sourceBuffer c r l a ξ = min (nextRecord c r l a ξ).2.1.toNNReal
          (switchedBuffer (rootPt r.1) c.s (historyTime c r l + candidateCap c r a)
            (historyTime c r l) (candidateCap c r a) (candidateBuffer a) (futurePair c r l a ξ)) := by
  filter_upwards [ae_conditional_sourceBuffer_gate_on_alive c r l] with ω₀ hω₀ ha
  filter_upwards [hω₀ ha] with ξ hξ
  intro a
  exact ite_eq_left hξ

/-- In particular every candidate launches in the actual successive chart
under that kernel, including its physical cutoff-independence. -/
theorem ae_conditional_next_launch_on_alive (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) :
    ∀ᵐ ω₀ ∂c.P, ω₀ ∈ (experiment c r).data.alive ((construction c).G r) l →
      ∀ᵐ ξ ∂condExpKernel c.P (c.sigma r l) ω₀, ∀ a,
        let spec := schedSpec (rootPt r.1) (futureProgram c r l a)
        let E := fun j => canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h spec j ξ
        (ExplState.run c.κ c.b c.jumps spec E ((historyProgram c r l).length + 1)).2.2.2.1
          (historyProgram c r l).length =
            some (succChart (rootPt r.1) (specDelta spec) E (historyProgram c r l).length,
              (candidateAngle c r a : ℝ)) := by
  filter_upwards [ae_conditional_sourceBuffer_gate_on_alive c r l] with ω₀ hω₀ ha
  filter_upwards [hω₀ ha] with ξ hξ
  exact fun a => next_launch_of_oldSuccess c r l a ξ hξ.2

end InteractingSLE.Theorem14.GW2TipSystem.RootK32
