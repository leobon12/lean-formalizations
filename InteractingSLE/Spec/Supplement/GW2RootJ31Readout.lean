/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootJ31Source
import InteractingSLE.Spec.Supplement.GW2RootJ31Entry
import InteractingSLE.Spec.Supplement.GW2RootJ31Tip

/-!
# Explicit all-history driver samples, observations and clocks

Packet PROVE-T14-GW2ROOT2. These definitions use the actual canonical
future program and its retained old records. Physical query times are
absolute schedule times; sample times are future capacity increments.
Only the Borel construction and exact sample reads are proved here.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootJ31

open Exist Staged StagedLaw Restart GW2Schedule GW2Tip RootC24

variable {Ω : Type u} [MeasurableSpace Ω]

def sourceSample (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω) : RootV7.DriverRecord :=
  switchedSample (2 ^ r.2) ((-1) ^ l.length) (rootPt r.1) c.s
    (historyTime c r l + candidateCap c r a) (rootEntry r.1).2 (historyTime c r l)
    (sourceBuffer c r l a ω) (futurePair c r l a ω)

def sourceDriver (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω) (u : ℝ≥0) : ℝ :=
  stageDriverRead (2 ^ r.2) ((-1) ^ l.length) (rootPt r.1) c.s
    (historyTime c r l + candidateCap c r a) (rootEntry r.1).2 (historyTime c r l)
    u (futurePair c r l a ω)

def sourceClock (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (q : ℝ≥0) (ω : Ω) : ℝ≥0 :=
  capacityIncrement (2 ^ r.2) (rootPt r.1) c.s (historyTime c r l)
    (q - historyTime c r l) (futurePair c r l a ω)

def sourceX (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω) (q : ℝ) : ℝ :=
  sourceDriver c r l a ω (sourceClock c r l a q.toNNReal ω)

def sourceTip (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω) (q : ℝ) : ℂ :=
  orientTip l.length (jointTipRead (2 ^ r.2) (rootPt r.1) c.s
    (historyTime c r l + candidateCap c r a) (rootEntry r.1).2
    (capacityIncrement (2 ^ r.2) (rootPt r.1) c.s (rootEntry r.1).2
      ((historyTime c r l + (q.toNNReal - historyTime c r l)) - (rootEntry r.1).2)
      (futurePair c r l a ω)) (futurePair c r l a ω))

def sourceEntry (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω) : ℝ :=
  (historyTime c r l + switchedEntry (2 ^ r.2) ((-1) ^ l.length) (rootPt r.1) c.s
    (historyTime c r l + candidateCap c r a) (rootEntry r.1).2 (historyTime c r l)
    (sourceBuffer c r l a ω) (futurePair c r l a ω) : ℝ≥0)

def sourceFailure (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω) : ℝ :=
  (historyTime c r l + sourceBuffer c r l a ω : ℝ≥0)

theorem measurable_sourceSample (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) : Measurable (sourceSample c r l a) :=
  measurable_switchedSample_random (measurable_futurePair c r l a)
    (measurable_sourceBuffer c r l a) _ _ _ _ _ _ _

theorem sourceSample_read (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω) {q : ℚ≥0}
    (hq : ((q : ℝ≥0) : ℝ≥0∞) < (sourceSample c r l a ω).1) :
    (sourceSample c r l a ω).2 q = sourceDriver c r l a ω q :=
  switchedSample_read _ _ _ _ _ _ _ _ _ hq

theorem sourceSample_life_eq_zero_of_old_death (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω)
    (hfail : ¬oldSuccess c r l ω) : (sourceSample c r l a ω).1 = 0 := by
  change (capacityIncrement _ _ _ _ (sourceBuffer c r l a ω) _ : ℝ≥0∞) = 0
  rw [sourceBuffer_eq_zero_of_old_death c r l a ω hfail, capacityIncrement_zero,
    ENNReal.coe_zero]

theorem measurable_sourceClock (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (q : ℝ≥0) :
    Measurable (sourceClock c r l a q) :=
  measurable_capacityIncrement_random (measurable_futurePair c r l a) measurable_const _ _ _ _

theorem sourceEntry_nonneg (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω) : 0 ≤ sourceEntry c r l a ω :=
  NNReal.coe_nonneg _

theorem sourceEntry_eq_failure_of_not_reach (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω)
    (hf : sourceSample c r l a ω ∉ RootD25.reachSet) :
    sourceEntry c r l a ω = sourceFailure c r l a ω := by
  unfold sourceEntry sourceFailure
  rw [switchedEntry_eq_buffer_of_not_reach _ _ _ _ _ _ _ _ _ hf]

end InteractingSLE.Theorem14.GW2TipSystem.RootJ31
