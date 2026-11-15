/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2GmQClock
import InteractingSLE.Spec.Supplement.GW2JDetR12History

/-!
# The retained version of J32's observation gate

Packet PROVE-GW2-GEOM2 (round 5). J32 observes at `q` only on the gate `S < q < F`. With `T` the history time, the
gate is the conjunction of the cover, the old successes, the candidate piece's survival past `q − T`, the separation
buffer past `q − T`, and the sample's first passage of `2` below the capacity increment `capInc(q − T)`. Each of these
is read here from the next history `(θ_a, q') :: l` (`q ≤ q'`):

* `nextLast` (the next history's last record: the same canonical piece, cut at `q' − T`), `nextGate`;
* **`measurableSet_nextGate`**: `nextGate` is retained by `c.sigma r ((θ_a, q') :: l)`;
* **`ae_mem_nextGate_iff`**: almost surely, for every time-ordered history, candidate and `q ≤ q'`, `nextGate` is
  exactly the gate.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.Gm

open Exist Staged StagedLaw Restart GW2Schedule GW2Tip RootC24 RootJ32 Sec5.Prop513TreeExtract
  Sec5.Prop513Schedule

variable {Ω : Type u} [MeasurableSpace Ω]

/-- The next history's last record: the candidate's canonical piece cut at `q' − T`. -/
def nextLast (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (q' : c.Q) (ω : Ω) : RecData :=
  stopRec c.hκ c.h12p c.βA c.c₀ c.h
    (schedSpec (rootPt r.1) (RootJ31.historyProgram c r ((RootJ31.candidateAngle c r a, q') :: l)))
    (RootJ31.historyProgram c r l).length ω

/-- **The retained gate**: J32's observation gate at `q`, read from the next history `(θ_a, q') :: l`. -/
def nextGate (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ)
    (q q' : c.Q) : Set Ω :=
  open scoped Classical in
  if RootJ31.historyTime c r l < (q : ℝ≥0) then
    RootCv.coverEvent c r ∩ {ω | RootJ31.oldSuccess c r l ω} ∩
      {ω | (q : ℝ≥0) - RootJ31.historyTime c r l < RootJ31.candidateCap c r a ∧
        ((nextLast c r l a q' ω).2.2 = false ∨
          (((q : ℝ≥0) - RootJ31.historyTime c r l : ℝ≥0) : ℝ≥0∞) < (nextLast c r l a q' ω).2.1)} ∩
      {ω | (q : ℝ≥0) - RootJ31.historyTime c r l <
        RootJ31.switchedBuffer (rootPt r.1) c.s q' (RootJ31.historyTime c r l)
          (RootJ31.candidateCap c r a) (RootJ31.candidateBuffer a) (nextPair c r l a q' ω)} ∩
      {ω | ∃ u : ℚ≥0, ((u : ℝ≥0)) < RootJ31.capacityIncrement (2 ^ r.2) (rootPt r.1) c.s
          (RootJ31.historyTime c r l) ((q : ℝ≥0) - RootJ31.historyTime c r l) (nextPair c r l a q' ω) ∧
        2 < stageDriverRead (2 ^ r.2) ((-1) ^ l.length) (rootPt r.1) c.s q' (rootEntry r.1).2
          (RootJ31.historyTime c r l) u (nextPair c r l a q' ω)}
  else ∅

variable [StandardBorelSpace Ω]

omit [StandardBorelSpace Ω] in
/-- The next history's last record is retained by the next history. -/
theorem measurable_nextLast (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (q' : c.Q) :
    Measurable[c.sigma r ((RootJ31.candidateAngle c r a, q') :: l)] (nextLast c r l a q') := by
  set l' := (RootJ31.candidateAngle c r a, q') :: l with hl'
  have hlen : (RootJ31.historyProgram c r l).length < (RootJ31.historyProgram c r l').length := by
    rw [hl', RootJ31.historyProgram_cons, List.length_append, List.length_singleton]
    exact Nat.lt_succ_self _
  have hj := RootU19.measurable_stageSigma_stopRec c.hκ c.h12p c.βA c.c₀ c.h
    c.s c.W c.ζ (schedSpec (rootPt r.1) (RootJ31.historyProgram c r l'))
    (RootJ31.historyProgram c r l').length ⟨_, hlen⟩
  have hsigma : c.sigma r l' = stageSigma c.hκ c.h12p c.βA c.c₀ c.h c.s c.W c.ζ
      (schedSpec (rootPt r.1) (RootJ31.historyProgram c r l'))
      (RootJ31.historyProgram c r l').length := by
    change stageSigma _ _ _ _ _ _ _ _ (schedSpecOf r.1 l') ((entryList l').length + 1) = _
    simp only [schedSpecOf, RootJ31.historyProgram, length_schedOf]
  rw [hsigma]
  exact hj

omit [StandardBorelSpace Ω] in
/-- **The retained gate is retained by the next history.** -/
theorem measurableSet_nextGate (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (q q' : c.Q) :
    MeasurableSet[c.sigma r ((RootJ31.candidateAngle c r a, q') :: l)] (nextGate c r l a q q') := by
  classical
  set l' := (RootJ31.candidateAngle c r a, q') :: l with hl'
  unfold nextGate
  split_ifs with hTq
  · have hp := measurable_nextPair c r l a q'
    have hR := measurable_nextLast c r l a q'
    have hcov : MeasurableSet[c.sigma r l'] (RootCv.coverEvent c r) :=
      GW2JDetR12.measurableSet_coverEvent_history c r l'
    have hold : MeasurableSet[c.sigma r l'] {ω | RootJ31.oldSuccess c r l ω} :=
      rootSigma_le_cons c.hκ c.h12p c.βA c.c₀ c.h c.W c.ζ c.s r l _ _
        (RootJ31.measurableSet_oldSuccess_rootSigma c r l)
    have hlife : MeasurableSet[c.sigma r l'] {ω | (q : ℝ≥0) - RootJ31.historyTime c r l <
        RootJ31.candidateCap c r a ∧ ((nextLast c r l a q' ω).2.2 = false ∨
          (((q : ℝ≥0) - RootJ31.historyTime c r l : ℝ≥0) : ℝ≥0∞) <
            (nextLast c r l a q' ω).2.1)} := by
      have hB : MeasurableSet {R : RecData | (q : ℝ≥0) - RootJ31.historyTime c r l <
          RootJ31.candidateCap c r a ∧ (R.2.2 = false ∨
            (((q : ℝ≥0) - RootJ31.historyTime c r l : ℝ≥0) : ℝ≥0∞) < R.2.1)} :=
        (MeasurableSet.const _).inter (((measurable_snd.comp measurable_snd)
          (measurableSet_singleton false)).union
            (measurableSet_lt measurable_const (measurable_fst.comp measurable_snd)))
      exact hR hB
    have hsep : MeasurableSet[c.sigma r l'] {ω | (q : ℝ≥0) - RootJ31.historyTime c r l <
        RootJ31.switchedBuffer (rootPt r.1) c.s q' (RootJ31.historyTime c r l)
          (RootJ31.candidateCap c r a) (RootJ31.candidateBuffer a) (nextPair c r l a q' ω)} :=
      hp (measurableSet_lt measurable_const (RootJ31.measurable_switchedBuffer _ _ _ _ _ _))
    have hent : MeasurableSet[c.sigma r l'] {ω | ∃ u : ℚ≥0, ((u : ℝ≥0)) <
        RootJ31.capacityIncrement (2 ^ r.2) (rootPt r.1) c.s (RootJ31.historyTime c r l)
          ((q : ℝ≥0) - RootJ31.historyTime c r l) (nextPair c r l a q' ω) ∧
        2 < stageDriverRead (2 ^ r.2) ((-1) ^ l.length) (rootPt r.1) c.s q' (rootEntry r.1).2
          (RootJ31.historyTime c r l) u (nextPair c r l a q' ω)} := by
      have hc : Measurable fun p : RecData × RecData =>
          RootJ31.capacityIncrement (2 ^ r.2) (rootPt r.1) c.s (RootJ31.historyTime c r l)
            ((q : ℝ≥0) - RootJ31.historyTime c r l) p :=
        RootJ31.measurable_capacityIncrement_random measurable_id measurable_const _ _ _ _
      have hY : ∀ u : ℚ≥0, Measurable fun p : RecData × RecData =>
          stageDriverRead (2 ^ r.2) ((-1) ^ l.length) (rootPt r.1) c.s q' (rootEntry r.1).2
            (RootJ31.historyTime c r l) u p := fun u =>
        measurable_stageDriverRead_random measurable_id _ _ _ _ _ _ _ measurable_const
      have hB : MeasurableSet {p : RecData × RecData | ∃ u : ℚ≥0, ((u : ℝ≥0)) <
          RootJ31.capacityIncrement (2 ^ r.2) (rootPt r.1) c.s (RootJ31.historyTime c r l)
            ((q : ℝ≥0) - RootJ31.historyTime c r l) p ∧
          2 < stageDriverRead (2 ^ r.2) ((-1) ^ l.length) (rootPt r.1) c.s q' (rootEntry r.1).2
            (RootJ31.historyTime c r l) u p} := by
        rw [Set.ofPred_exists]
        exact MeasurableSet.iUnion fun u =>
          (measurableSet_lt measurable_const hc).inter (measurableSet_lt measurable_const (hY u))
      exact hp hB
    exact (((hcov.inter hold).inter hlife).inter hsep).inter hent
  · exact @MeasurableSet.empty _ (c.sigma r l')

end InteractingSLE.Theorem14.GW2TipSystem.Gm
