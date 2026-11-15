/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootJ31Alive

/-!
# Measurability and exact physical availability for the explicit D

Packet PROVE-T14-GW2ROOT2. Ambient measurability of the entire gated
observation is proved. Its stronger measurability in a shorter candidate
program's sigma algebra remains a different obligation. Old success is
already measurable in the literal retained history, at every sample.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootJ31

open Exist Staged StagedLaw Restart GW2Schedule GW2Tip RootC24 RootK3

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Every old death flag is known from exactly the retained physical history. -/
theorem measurableSet_oldSuccess_rootSigma (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) :
    MeasurableSet[c.sigma r l] {ω | oldSuccess c r l ω} := by
  have hm : ∀ j : Fin (historyProgram c r l).length,
      Measurable[c.sigma r l] (fun ω =>
        (stopRec c.hκ c.h12p c.βA c.c₀ c.h
          (schedSpec (rootPt r.1) (historyProgram c r l)) j ω).2.2) := by
    intro j
    have hj := RootU19.measurable_stageSigma_stopRec c.hκ c.h12p c.βA c.c₀ c.h
      c.s c.W c.ζ (schedSpec (rootPt r.1) (historyProgram c r l))
      (historyProgram c r l).length j
    have hflag := (measurable_snd.comp measurable_snd).comp hj
    have hsigma : c.sigma r l = stageSigma c.hκ c.h12p c.βA c.c₀ c.h c.s c.W c.ζ
        (schedSpec (rootPt r.1) (historyProgram c r l)) (historyProgram c r l).length := by
      change stageSigma _ _ _ _ _ _ _ _ (schedSpecOf r.1 l) ((entryList l).length + 1) = _
      simp only [schedSpecOf, historyProgram, length_schedOf]
    rw [hsigma]
    exact hflag
  have hs : ∀ j : Fin (historyProgram c r l).length, MeasurableSet[c.sigma r l]
      {ω | (stopRec c.hκ c.h12p c.βA c.c₀ c.h
        (schedSpec (rootPt r.1) (historyProgram c r l)) j ω).2.2 = false} :=
    fun j => hm j (measurableSet_singleton false)
  simpa only [oldSuccess, ofPred_forall] using MeasurableSet.iInter hs

/-- The decoded success flags give precisely the existing deterministic
all-success predicate used by the switched run and its launch charts. -/
theorem oldSuccess_iff_allSucc (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (ω : Ω) :
    oldSuccess c r l ω ↔ AllSucc
      (specDelta (schedSpec (rootPt r.1) (historyProgram c r l)))
      (fun j => canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h
        (schedSpec (rootPt r.1) (historyProgram c r l)) j ω)
      (historyProgram c r l).length := by
  constructor
  · intro hs j hj
    exact (RootCv.recOf_flag_eq_false_iff _ _).mp (hs ⟨j, hj⟩)
  · intro hs j
    exact (RootCv.recOf_flag_eq_false_iff _ _).mpr (hs j j.isLt)

theorem measurable_sourceX (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (q : ℝ) :
    Measurable fun ω => sourceX c r l a ω q :=
  measurable_stageDriverRead_random (measurable_futurePair c r l a)
    (measurable_sourceClock c r l a q.toNNReal) _ _ _ _ _ _ _

theorem measurable_sourceTip (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (q : ℝ) :
    Measurable fun ω => sourceTip c r l a ω q :=
  (measurable_orientTip l.length).comp
    (measurable_jointTipRead_random (measurable_futurePair c r l a)
      (measurable_capacityIncrement_random (measurable_futurePair c r l a)
        measurable_const _ _ _ _) _ _ _ _ _)

theorem measurable_sourceEntry (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) : Measurable (sourceEntry c r l a) :=
  NNReal.continuous_coe.measurable.comp (measurable_const.add
    (measurable_switchedEntry_random (measurable_futurePair c r l a)
      (measurable_sourceBuffer c r l a) _ _ _ _ _ _ _))

theorem measurable_sourceFailure (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) : Measurable (sourceFailure c r l a) :=
  NNReal.continuous_coe.measurable.comp
    (measurable_const.add (measurable_sourceBuffer c r l a))

variable [StandardBorelSpace Ω]

/-- The actual entire gated observation is ambient Borel, including every
killed and exceptional outcome. No a.e. measurable map is used as a law. -/
theorem measurable_observation (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (q : c.Q) :
    Measurable ((experiment c r).data.observation l a q) :=
  Measurable.ite
    ((measurableSet_lt (measurable_sourceEntry c r l a) measurable_const).inter
      (measurableSet_lt measurable_const (measurable_sourceFailure c r l a)))
    ((measurable_sourceX c r l a q).prodMk (measurable_sourceTip c r l a q)) measurable_const

/-- A source-facing all-history availability fact for the actual D. -/
theorem allSucc_of_alive (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (ω : Ω)
    (ha : ω ∈ (experiment c r).data.alive ((construction c).G r) l) :
    AllSucc (specDelta (schedSpec (rootPt r.1) (historyProgram c r l)))
      (fun j => canonSpecFam c.hκ c.h12p c.βA c.c₀ c.h
        (schedSpec (rootPt r.1) (historyProgram c r l)) j ω)
      (historyProgram c r l).length :=
  (oldSuccess_iff_allSucc c r l ω).mp (oldSuccess_of_alive c r l ω ha)

end InteractingSLE.Theorem14.GW2TipSystem.RootJ31
