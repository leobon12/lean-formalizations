/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootJ31Joined

/-!
# Actual finite programs for future switched candidates

Packet PROVE-T14-GW2ROOT2. A candidate specifies an angle, a positive
own-time cap from the original Q, and a buffer index. The inherited
schedule is unchanged and the next instruction is appended at its
absolute terminal time plus this own-time cap.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootJ31

open Exist Staged StagedLaw Restart GW2Schedule GW2Tip RootC24
open Sec5.Prop513Schedule

variable {Ω : Type u} [MeasurableSpace Ω]

/-- Enumerate the actual source angles, using the root only for nonemptiness. -/
def angleEnumeration (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) : ℕ → c.Θ :=
  ((Set.countable_iff_exists_surjective (s := c.Θ)
    ⟨(r.1.2.1 : ℝ), r.1.2.1.property⟩).mp c.hΘc).choose

/-- Enumerate the original Q, without closing it under sums or differences. -/
def timeEnumeration (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) : ℕ → c.Q :=
  ((Set.countable_iff_exists_surjective (s := c.Q)
    ⟨(r.1.2.2 : ℝ≥0), r.1.2.2.property⟩).mp c.hQc).choose

theorem angleEnumeration_surjective (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) :
    Function.Surjective (angleEnumeration c r) :=
  ((Set.countable_iff_exists_surjective (s := c.Θ)
    ⟨(r.1.2.1 : ℝ), r.1.2.1.property⟩).mp c.hΘc).choose_spec

theorem timeEnumeration_surjective (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) :
    Function.Surjective (timeEnumeration c r) :=
  ((Set.countable_iff_exists_surjective (s := c.Q)
    ⟨(r.1.2.2 : ℝ≥0), r.1.2.2.property⟩).mp c.hQc).choose_spec

def candidateAngle (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (a : ℕ) : c.Θ :=
  angleEnumeration c r (Nat.unpair a).1

def candidateCap (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (a : ℕ) : ℝ≥0 :=
  timeEnumeration c r (Nat.unpair (Nat.unpair a).2).1

def candidateBuffer (a : ℕ) : ℕ := (Nat.unpair (Nat.unpair a).2).2

/-- Every angle, cap and geometric buffer occurs among the candidates. -/
theorem exists_candidate (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (θ : c.Θ) (b : c.Q) (m : ℕ) :
    ∃ a, candidateAngle c r a = θ ∧ candidateCap c r a = b ∧ candidateBuffer a = m := by
  obtain ⟨i, hi⟩ := angleEnumeration_surjective c r θ
  obtain ⟨j, hj⟩ := timeEnumeration_surjective c r b
  refine ⟨Nat.pair i (Nat.pair j m), ?_, ?_, ?_⟩
  · simp only [candidateAngle, Nat.unpair_pair, hi]
  · simp only [candidateCap, Nat.unpair_pair, hj]
  · simp only [candidateBuffer, Nat.unpair_pair]

theorem candidateCap_pos (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (a : ℕ) :
    0 < candidateCap c r a :=
  c.hQpos _ (timeEnumeration c r (Nat.unpair (Nat.unpair a).2).1).property

/-- The original chronological schedule of this retained history. -/
def historyProgram (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) : List (ℝ × ℝ≥0) :=
  schedOf (rootEntry r.1) (entryList l)

/-- Absolute physical time at the end of the retained schedule. -/
def historyTime (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) : ℝ≥0 :=
  schedTime 0 (historyProgram c r l) (historyProgram c r l).length

/-- Append the future piece; this is a physical program, not a replacement
for the inherited history or an assertion of future availability. -/
def futureProgram (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) : List (ℝ × ℝ≥0) :=
  historyProgram c r l ++ [((candidateAngle c r a : ℝ),
    historyTime c r l + candidateCap c r a)]

/-- The two records used for the relative chart after the whole program. -/
def futurePair (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω) : RecData × RecData :=
  (cfRec c.s c.W c.ζ ω,
    joinedRecord (futureProgram c r l a)
      (programRecords c (rootPt r.1) (futureProgram c r l a) ω))

/-- The appended future instruction has exactly the candidate's own-time cap. -/
theorem futureProgram_delta (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) :
    specDelta (schedSpec (rootPt r.1) (futureProgram c r l a))
      (historyProgram c r l).length = (candidateCap c r a : ℝ≥0∞) := by
  rw [futureProgram, RootH29.specDelta_last]
  simp only [historyTime, add_tsub_cancel_left]

theorem measurable_futurePair (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) : Measurable (futurePair c r l a) :=
  (measurable_cfRec c.hcf c.s).prodMk
    (measurable_programJoinedRecord_ambient c (rootPt r.1) (futureProgram c r l a))

end InteractingSLE.Theorem14.GW2TipSystem.RootJ31
