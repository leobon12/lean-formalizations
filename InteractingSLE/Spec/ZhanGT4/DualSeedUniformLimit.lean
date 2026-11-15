/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedLimit

/-!
# Removing the natural-number band sequence

Packet PROVE-ZHAN-GT4-A22. The index of the band identities is explicitly a
natural number, matching A21's band theorem.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The band limit requires identities only along the natural-number sequence. -/
theorem integral_indicator_mul_stopped_sub_eq_zero_of_nat_band
    {ι : Type*} [Fintype ι] [Nonempty ι]
    {𝓕 : Filtration ℝ≥0 mΩ} {Y : ι → ℝ≥0 → Ω → ℝ}
    {M : ℝ≥0 → Ω → ℝ} {ε R : ℝ≥0} {T : Ω → ℝ≥0}
    {P : Measure Ω} [IsFiniteMeasure P] {C : ℝ} (hC : 0 ≤ C)
    (hYc : ∀ i ω, Continuous (Y i · ω))
    (hYm : ∀ i u, Measurable[𝓕 u] (Y i u))
    (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0))
    (hTR : ∀ ω, T ω ≤ ε + R)
    (hne : ∀ ω, ε ≤ T ω → ∀ i u, ε ≤ u → u ≤ T ω → Y i u ω ≠ 0)
    (hMm : ∀ u, Measurable[𝓕 u] (M u))
    (hMc : ∀ ω, Continuous (M · ω))
    (hMb : ∀ ω u, u ≤ T ω → |M u ω| ≤ C)
    {s t : ℝ≥0} {ξ : Ω → ℝ} (hξ : Measurable ξ)
    (hξb : ∀ ω, |ξ ω| ≤ 1)
    (hk : ∀ k : ℕ, ∫ ω,
      (bandEv Y (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) ε T).indicator ξ ω *
        (M (min t (bandExit Y (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) ε R T ω)) ω
          - M (min s (bandExit Y (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) ε R T ω)) ω) ∂P = 0) :
    ∫ ω, {ω | ε ≤ T ω}.indicator ξ ω *
      (M (min t (T ω)) ω - M (min s (T ω)) ω) ∂P = 0 := by
  have hkb : ∀ k u ω, |bandStopped Y M ε R T k u ω| ≤ C := by
    intro k u ω
    by_cases hω : ω ∈ bandEv Y (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) ε T
    · rw [bandStopped, indicator_of_mem hω]
      exact hMb ω _ ((min_le_right _ _).trans (bandExit_le hω.1))
    · rw [bandStopped, indicator_of_notMem hω, abs_zero]
      exact hC
  have hid : ∀ k : ℕ, ∫ ω, ξ ω *
      (bandStopped Y M ε R T k t ω - bandStopped Y M ε R T k s ω) ∂P = 0 := by
    intro k
    convert hk k using 1
    apply integral_congr_ae
    filter_upwards [] with ω
    by_cases hω : ω ∈ bandEv Y (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) ε T
    · simp only [bandStopped, indicator_of_mem hω]
    · simp only [bandStopped, indicator_of_notMem hω, sub_self, mul_zero, zero_mul]
  have hlim := integral_mul_sub_eq_zero_of_tendsto hξ hξb
    (fun k u => (measurable_bandStopped hYc hYm hT hMm hMc k u).aestronglyMeasurable)
    hkb (tendsto_bandStopped hYc hTR hne) hid
  convert hlim using 1
  apply integral_congr_ae
  filter_upwards [] with ω
  by_cases hω : ε ≤ T ω
  · simp only [indicator_of_mem (show ω ∈ {ω | ε ≤ T ω} from hω)]
  · simp only [indicator_of_notMem (show ω ∉ {ω | ε ≤ T ω} from hω),
      sub_self, mul_zero, zero_mul]

end InteractingSLE.ZhanGT4
