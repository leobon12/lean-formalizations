/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW2RootJ31Construction

/-! # Proved temporal and gating facts for the concrete construction -/

set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE.Theorem14.GW2TipSystem.RootJ31

open Exist Staged StagedLaw Restart RootC24 RootK3

variable {Ω : Type u} [MeasurableSpace Ω]

theorem sourceEntry_ge_historyTime (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω) :
    (historyTime c r l : ℝ) ≤ sourceEntry c r l a ω := by
  exact NNReal.coe_le_coe.mpr (le_add_of_nonneg_right (bot_le : (0 : ℝ≥0) ≤ _))

theorem sourceEntry_le_failure (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω) :
    sourceEntry c r l a ω ≤ sourceFailure c r l a ω :=
  NNReal.coe_le_coe.mpr (add_le_add le_rfl (switchedEntry_le_buffer _ _ _ _ _ _ _ _ _))

theorem sourceFailure_le_cap (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω) :
    sourceFailure c r l a ω ≤ (historyTime c r l + candidateCap c r a : ℝ≥0) :=
  NNReal.coe_le_coe.mpr (add_le_add le_rfl (sourceBuffer_le c r l a ω))

/-- The nontrivial direction of reach identification is the clock-dependent
converse. This direction follows from the actual failure convention everywhere. -/
theorem entry_lt_failure_imp_reach (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω)
    (hSF : sourceEntry c r l a ω < sourceFailure c r l a ω) :
    sourceSample c r l a ω ∈ RootD25.reachSet := by
  by_contra hf
  exact (ne_of_lt hSF) (sourceEntry_eq_failure_of_not_reach c r l a ω hf)

/-- Every active regularity obligation is on the actual protected root event. -/
theorem cover_of_entry_lt_failure (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (ω : Ω)
    (hSF : sourceEntry c r l a ω < sourceFailure c r l a ω) :
    ω ∈ RootCv.coverEvent c r := by
  by_contra hf
  have hF : sourceFailure c r l a ω = (historyTime c r l : ℝ) := by
    simp only [sourceFailure, sourceBuffer_eq_zero_of_not_cover c r l a ω hf, add_zero]
  rw [hF] at hSF
  exact (not_lt_of_ge (sourceEntry_ge_historyTime c r l a ω)) hSF

variable [StandardBorelSpace Ω]

/-- An observation before the retained history ends is identically zero. -/
theorem observation_eq_zero_of_le_historyTime (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (q : c.Q)
    (hq : (q : ℝ≥0) ≤ historyTime c r l) :
    (experiment c r).data.observation l a q = fun _ => (0, 0) := by
  funext ω
  apply ite_eq_right
  intro hg
  exact (not_lt_of_ge ((NNReal.coe_le_coe.mpr hq).trans
    (sourceEntry_ge_historyTime c r l a ω))) hg.1

/-- Beyond the finite future cap, the entire gated observation is also zero. -/
theorem observation_eq_zero_of_cap_le (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (q : c.Q)
    (hq : historyTime c r l + candidateCap c r a ≤ (q : ℝ≥0)) :
    (experiment c r).data.observation l a q = fun _ => (0, 0) := by
  funext ω
  apply ite_eq_right
  intro hg
  exact (not_lt_of_ge ((sourceFailure_le_cap c r l a ω).trans
    (NNReal.coe_le_coe.mpr hq))) hg.2

/-- These two parts of the exact C24 observation field are proved without
completion of the retained sigma algebra or exceptional-set changes. -/
theorem measurable_observation_outside_window (c : SourceData Ω)
    (r : ScaledRootIdx c.Θ c.Q) (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (q q' : c.Q)
    (hq : (q : ℝ≥0) ≤ historyTime c r l ∨
      historyTime c r l + candidateCap c r a ≤ (q : ℝ≥0)) :
    Measurable[c.sigma r ((candidateAngle c r a, q') :: l)]
      ((experiment c r).data.observation l a q) := by
  rcases hq with hq | hq
  · rw [observation_eq_zero_of_le_historyTime c r l a q hq]
    exact measurable_const
  · rw [observation_eq_zero_of_cap_le c r l a q hq]
    exact measurable_const

/-- A successful actual test entails success of every old ordinary piece. -/
theorem oldSuccess_of_test (c : SourceData Ω) (r : ScaledRootIdx c.Θ c.Q)
    (l : List (EntryIdx c.Θ c.Q)) (a : ℕ) (q : c.Q) (ω : Ω)
    (ht : ω ∈ (experiment c r).data.tests l a q) : oldSuccess c r l ω := by
  by_contra hf
  have hSF : sourceEntry c r l a ω < sourceFailure c r l a ω := ht.1.trans ht.2.1
  have hF : sourceFailure c r l a ω = (historyTime c r l : ℝ) := by
    simp only [sourceFailure, sourceBuffer_eq_zero_of_old_death c r l a ω hf, add_zero]
  rw [hF] at hSF
  exact (not_lt_of_ge (sourceEntry_ge_historyTime c r l a ω)) hSF

end InteractingSLE.Theorem14.GW2TipSystem.RootJ31
