/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootK32Active

/-!
# Increasing buffers among the actual enumerated candidates

Packet PROVE-T14-GW2ROOT2. Keep the candidate's source angle and original-Q
cap fixed and vary only its buffer index. The future physical program,
records and full conditioning remain the same. The actual source buffers
exhaust every compact interval before both contact and the next lifetime.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootK32

open Exist.StagedLaw RootC24 RootJ31

/-- Change only the third coordinate of J31's actual triple enumeration. -/
def candidateWithBuffer (a m : ℕ) : ℕ :=
  Nat.pair (Nat.unpair a).1 (Nat.pair (Nat.unpair (Nat.unpair a).2).1 m)

theorem candidateBuffer_withBuffer (a m : ℕ) : candidateBuffer (candidateWithBuffer a m) = m := by
  simp only [candidateWithBuffer, candidateBuffer, Nat.unpair_pair]

variable {Ω : Type u} [MeasurableSpace Ω]

theorem candidateAngle_withBuffer (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (a m : ℕ) :
    candidateAngle c r (candidateWithBuffer a m) = candidateAngle c r a := by
  simp only [candidateWithBuffer, candidateAngle, Nat.unpair_pair]

theorem candidateCap_withBuffer (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q) (a m : ℕ) :
    candidateCap c r (candidateWithBuffer a m) = candidateCap c r a := by
  simp only [candidateWithBuffer, candidateCap, Nat.unpair_pair]

theorem futureProgram_withBuffer (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a m : ℕ) :
    futureProgram c r l (candidateWithBuffer a m) = futureProgram c r l a := by
  rw [futureProgram, candidateAngle_withBuffer, candidateCap_withBuffer]
  rfl

theorem futurePair_withBuffer (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a m : ℕ) :
    futurePair c r l (candidateWithBuffer a m) = futurePair c r l a := by
  unfold futurePair
  rw [futureProgram_withBuffer]

theorem nextRecord_withBuffer (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a m : ℕ) :
    nextRecord c r l (candidateWithBuffer a m) = nextRecord c r l a := by
  unfold nextRecord
  rw [futureProgram_withBuffer]

open scoped Classical in
/-- The actual source formula along this family, on every outcome. -/
theorem sourceBuffer_withBuffer (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a m : ℕ) (ω : Ω) :
    sourceBuffer c r l (candidateWithBuffer a m) ω =
      if ω ∈ RootCv.coverEvent c r ∧ oldSuccess c r l ω then
        min (nextRecord c r l a ω).2.1.toNNReal
          (switchedBuffer (rootPt r.1) c.s (historyTime c r l + candidateCap c r a)
            (historyTime c r l) (candidateCap c r a) m (futurePair c r l a ω)) else 0 := by
  classical
  rw [sourceBuffer, nextRecord_withBuffer, candidateCap_withBuffer, candidateBuffer_withBuffer,
    futurePair_withBuffer]

theorem monotone_sourceBuffer_withBuffer (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω) :
    Monotone (fun m => sourceBuffer c r l (candidateWithBuffer a m) ω) := by
  classical
  intro m m' hmm'
  change sourceBuffer c r l (candidateWithBuffer a m) ω ≤
    sourceBuffer c r l (candidateWithBuffer a m') ω
  rw [sourceBuffer_withBuffer, sourceBuffer_withBuffer]
  split_ifs
  · exact min_le_min le_rfl (monotone_switchedBuffer _ _ _ _ _ _ hmm')
  · exact le_rfl

/-- Eventual exhaustion refers to candidates of D itself, rather than
an auxiliary geometric family that might use different physical records. -/
theorem eventually_lt_sourceBuffer_withBuffer (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω) (t : ℝ≥0)
    (hcov : ω ∈ RootCv.coverEvent c r) (hold : oldSuccess c r l ω)
    (hnext : t < (nextRecord c r l a ω).2.1.toNNReal) (hcap : t < candidateCap c r a)
    (hcontact : ((historyTime c r l + t : ℝ≥0) : ℝ≥0∞) <
      translatedContact (rootPt r.1) c.s
        (historyTime c r l + candidateCap c r a) (futurePair c r l a ω)) :
    ∀ᶠ m in atTop, t < sourceBuffer c r l (candidateWithBuffer a m) ω := by
  classical
  have h := eventually_lt_switchedBuffer (rootPt r.1) c.s
    (historyTime c r l + candidateCap c r a) (historyTime c r l)
    (candidateCap c r a) t (futurePair c r l a ω) hcap hcontact
  filter_upwards [h] with m hm
  rw [sourceBuffer_withBuffer, ite_eq_left ⟨hcov, hold⟩]
  exact lt_min hnext hm

/-- In particular positive physical buffers persist for every index in
this family once one actual candidate has a positive sample lifetime. -/
theorem sourceBuffer_withBuffer_pos_of_live (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a m : ℕ) (ω : Ω)
    (hL : 0 < (sourceSample c r l a ω).1) :
    0 < sourceBuffer c r l (candidateWithBuffer a m) ω := by
  have hg := sourceSample_live_geometry c r l a ω hL
  have hg' : 0 < RootJ31.separationRead (rootPt r.1) c.s
      (historyTime c r l + candidateCap c r (candidateWithBuffer a m)) (historyTime c r l)
      (futurePair c r l (candidateWithBuffer a m) ω) := by
    rw [candidateCap_withBuffer, futurePair_withBuffer]
    exact hg.2.2.2
  apply sourceBuffer_pos c r l (candidateWithBuffer a m) ω hg.1 hg.2.1 _ hg'
  rw [nextRecord_withBuffer]
  exact hg.2.2.1

end InteractingSLE.Theorem14.GW2TipSystem.RootK32
