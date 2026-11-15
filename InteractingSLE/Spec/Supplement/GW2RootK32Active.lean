/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootK32Buffers

/-!
# A live J31 sample supplies its own geometric protection

Packet PROVE-T14-GW2ROOT2. Positive sample life forces positive physical
buffer. The exact positivity criterion then supplies separation of the
entire old prefix. Thus the active geometry obligations and successful
tests need no additional separation premise.
-/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootK32

open Exist StagedLaw Restart RootC24 RootJ31

variable {Ω : Type u} [MeasurableSpace Ω]

theorem sourceSample_life_eq_zero_of_buffer_eq_zero (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω)
    (hF : sourceBuffer c r l a ω = 0) : (sourceSample c r l a ω).1 = 0 := by
  change (capacityIncrement _ _ _ _ (sourceBuffer c r l a ω) _ : ℝ≥0∞) = 0
  rw [hF, capacityIncrement_zero, ENNReal.coe_zero]

theorem sourceBuffer_pos_of_sample_life_pos (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω)
    (hL : 0 < (sourceSample c r l a ω).1) : 0 < sourceBuffer c r l a ω := by
  by_contra hn
  have hz : sourceBuffer c r l a ω = 0 := le_antisymm (le_of_not_gt hn) bot_le
  rw [sourceSample_life_eq_zero_of_buffer_eq_zero c r l a ω hz] at hL
  exact (lt_irrefl 0) hL

/-- An actual live sample certifies the two geometric/availability inputs
that the bare alive gate did not supply. -/
theorem sourceSample_live_geometry (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω)
    (hL : 0 < (sourceSample c r l a ω).1) :
    ω ∈ RootCv.coverEvent c r ∧ oldSuccess c r l ω ∧
      0 < (nextRecord c r l a ω).2.1.toNNReal ∧
      0 < RootJ31.separationRead (rootPt r.1) c.s
        (historyTime c r l + candidateCap c r a) (historyTime c r l) (futurePair c r l a ω) :=
  (sourceBuffer_pos_iff c r l a ω).mp (sourceBuffer_pos_of_sample_life_pos c r l a ω hL)

/-- The complete physical failure prefix is strictly before contact
whenever the actual sample is live. No source a.e. theorem is needed. -/
theorem sourceSample_live_before_contact (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω)
    (hL : 0 < (sourceSample c r l a ω).1) :
    ((historyTime c r l + sourceBuffer c r l a ω : ℝ≥0) : ℝ≥0∞) <
      translatedContact (rootPt r.1) c.s
        (historyTime c r l + candidateCap c r a) (futurePair c r l a ω) :=
  sourceBuffer_lt_contact c r l a ω (sourceSample_live_geometry c r l a ω hL).2.2.2

/-- This applies on exactly the active premise in C24's regularity field. -/
theorem active_before_contact (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω)
    (hSF : sourceEntry c r l a ω < sourceFailure c r l a ω) :
    ((historyTime c r l + sourceBuffer c r l a ω : ℝ≥0) : ℝ≥0∞) <
      translatedContact (rootPt r.1) c.s
        (historyTime c r l + candidateCap c r a) (futurePair c r l a ω) := by
  have hreach := entry_lt_failure_imp_reach c r l a ω hSF
  exact sourceSample_live_before_contact c r l a ω
    (lt_of_le_of_lt bot_le (show RootD25.entryCapacity _ < _ from hreach))

/-- All points of an active physical prefix avoid inversion contact,
including both closed endpoints and every old-prefix point. -/
theorem active_prefix_noncontact (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω)
    (hSF : sourceEntry c r l a ω < sourceFailure c r l a ω) :
    ∀ t ≤ historyTime c r l + sourceBuffer c r l a ω, ∀ w ≤ c.s,
      ((rootPt r.1 : ℂ) + RootG28.frozenTraceRead
        (historyTime c r l + candidateCap c r a) (futurePair c r l a ω).2 t) *
        RootG28.frozenTraceRead c.s (futurePair c r l a ω).1 w + 1 ≠ 0 :=
  (separationRead_pos_iff _ _ _ _ _).mp
    ((separationRead_pos_iff_lt_contact _ _ _ _ _).mpr (active_before_contact c r l a ω hSF))

variable [StandardBorelSpace Ω]

/-- Every actual passed query is strictly before the reconstructed contact
time. This is directly usable in the switched-capacity proof. -/
theorem test_before_contact (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (q : c.Q) (ω : Ω)
    (ht : ω ∈ (experiment c r).data.tests l a q) :
    ((q : ℝ≥0) : ℝ≥0∞) < translatedContact (rootPt r.1) c.s
      (historyTime c r l + candidateCap c r a) (futurePair c r l a ω) := by
  have hq : (q : ℝ≥0) < historyTime c r l + sourceBuffer c r l a ω :=
    NNReal.coe_lt_coe.mp ht.2.1
  exact (ENNReal.coe_lt_coe.mpr hq).trans
    (active_before_contact c r l a ω (ht.1.trans ht.2.1))

end InteractingSLE.Theorem14.GW2TipSystem.RootK32
