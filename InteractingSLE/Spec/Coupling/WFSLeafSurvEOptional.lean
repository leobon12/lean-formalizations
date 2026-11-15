/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Coupling.WFSLeafSurvEScalar
import InteractingSLE.Spec.Coupling.WFSLeafClockCAssembly

/-!
# A closed survival martingale at bounded stopping times

This file proves strict conditional gaps before the lifetime and identifies
the terminal value on each bounded lifetime event. Existence of a continuous
history reader for these conditional expectations is not assumed implicitly.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal

namespace InteractingSLE.WFS

open LawUnique Restart.FlowStopIdentG

/-- The optional-sampling identity required of a scalar history reader.
Only bounded stopping times are tested. This is a property of the given reader,
not an assertion that a continuous version exists. -/
def IsOptionalSurvivalReader {Ω : Type*} {mΩ : MeasurableSpace Ω} {nL nR : ℕ}
    (P : Measure Ω) (𝓓 : Filtration ℝ≥0 mΩ) (V : Ω → ℝ≥0∞)
    (Y : Ω → HistorySpace nL nR) (M : HistorySpace nL nR → ℝ≥0 → ℝ) : Prop :=
  ∀ (T : Ω → ℝ≥0∞) (hT : IsStoppingTime 𝓓 fun ω => (T ω : WithTop ℝ≥0)),
    (∃ N : ℝ≥0, ∀ ω, T ω ≤ N) →
    P[fun ω => survivalDiscount (V ω) | hT.measurableSpace] =ᵐ[P]
      fun ω => M (Y ω) (T ω).toNNReal

/-- Strict survival gaps at bounded stopping times. The event `{T < V}` is
observed at `T`, so strict conditional positivity applies on that event. -/
theorem ae_survival_gap_pos_at_stop {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P] {𝓓 : Filtration ℝ≥0 mΩ}
    {V T : Ω → ℝ≥0∞} (hV : IsStoppingTime 𝓓 fun ω => (V ω : WithTop ℝ≥0))
    (hT : IsStoppingTime 𝓓 fun ω => (T ω : WithTop ℝ≥0))
    {nL nR : ℕ} {Y : Ω → HistorySpace nL nR}
    {M : HistorySpace nL nR → ℝ≥0 → ℝ}
    (hread : IsOptionalSurvivalReader P 𝓓 V Y M)
    (hbound : ∃ N : ℝ≥0, ∀ ω, T ω ≤ N) :
    ∀ᵐ ω ∂P, T ω < V ω →
      0 < survivalDiscount (T ω) - M (Y ω) (T ω).toNNReal := by
  have hA : MeasurableSet[hT.measurableSpace] {ω | T ω < V ω} := by
    convert (hV.measurableSet_stopping_time_le hT).compl using 1
    ext ω
    exact (not_le (a := V ω) (b := T ω)).symm
  have hg : StronglyMeasurable[hT.measurableSpace] (fun ω => survivalDiscount (T ω)) :=
    (measurable_survivalDiscount.comp hT.measurable).stronglyMeasurable
  have hlt := ae_condExp_lt_on_event (P := P) hT.measurableSpace_le hA
    (integrable_survivalDiscount hV.measurable') (integrable_survivalDiscount hT.measurable') hg
    (fun ω hω => strictAnti_survivalDiscount hω)
  filter_upwards [hlt, hread T hT hbound] with ω hω he hTV
  exact sub_pos.2 (he ▸ hω hTV)

/-- On `{V ≤ N}`, the optional reader at `V ∧ N` equals the terminal discount.
The proof reuses the stopped-sigma-algebra conditional-expectation identity. -/
theorem ae_survival_reader_terminal_on_le {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P] {𝓓 : Filtration ℝ≥0 mΩ}
    {V : Ω → ℝ≥0∞} (hV : IsStoppingTime 𝓓 fun ω => (V ω : WithTop ℝ≥0))
    {nL nR : ℕ} {Y : Ω → HistorySpace nL nR}
    {M : HistorySpace nL nR → ℝ≥0 → ℝ}
    (hread : IsOptionalSurvivalReader P 𝓓 V Y M) (N : ℝ≥0) :
    ∀ᵐ ω ∂P, V ω ≤ N → M (Y ω) (V ω).toNNReal = survivalDiscount (V ω) := by
  have he := condExp_min_stopping_time_ae_eq_restrict_le_const
    (μ := P) (f := fun ω => survivalDiscount (V ω)) hV N
  have he' := (ae_restrict_iff' (hV.measurableSpace_le _ (hV.measurableSet_le' N))).1 he
  have hf : P[fun ω => survivalDiscount (V ω) | hV.measurableSpace] =
      fun ω => survivalDiscount (V ω) :=
    condExp_of_stronglyMeasurable hV.measurableSpace_le
      (measurable_survivalDiscount.comp hV.measurable).stronglyMeasurable
      (integrable_survivalDiscount hV.measurable')
  have hr := hread (fun ω => min (V ω) (N : ℝ≥0∞)) (hV.min_const N)
    ⟨N, fun _ => min_le_right _ _⟩
  filter_upwards [he', hr] with ω he hr hVN
  have hmin : min (V ω) (N : ℝ≥0∞) = V ω := min_eq_left hVN
  rw [hmin] at hr
  exact hr.symm.trans ((he hVN).trans (congrFun hf ω))

/-- Countably many bounded events identify the reader at every finite lifetime. -/
theorem ae_survival_reader_terminal {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {P : Measure Ω} [IsFiniteMeasure P] {𝓓 : Filtration ℝ≥0 mΩ}
    {V : Ω → ℝ≥0∞} (hV : IsStoppingTime 𝓓 fun ω => (V ω : WithTop ℝ≥0))
    {nL nR : ℕ} {Y : Ω → HistorySpace nL nR}
    {M : HistorySpace nL nR → ℝ≥0 → ℝ}
    (hread : IsOptionalSurvivalReader P 𝓓 V Y M) :
    ∀ᵐ ω ∂P, V ω ≠ ⊤ → M (Y ω) (V ω).toNNReal = survivalDiscount (V ω) := by
  have hall := (ae_all_iff.2 fun n : ℕ => ae_survival_reader_terminal_on_le hV hread (n : ℝ≥0))
  filter_upwards [hall] with ω hω hfin
  obtain ⟨n, hn⟩ := exists_nat_ge (V ω).toNNReal
  apply hω n
  rw [← ENNReal.coe_toNNReal hfin]
  exact ENNReal.coe_le_coe.2 hn

end InteractingSLE.WFS
