/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedPathBand
import InteractingSLE.Spec.ZhanGT4.DualTimeChangeBMFrozen
import InteractingSLE.Spec.ZhanGT4.DualSeedExt

/-!
# Removing the seeded band cutoffs

Packet PROVE-ZHAN-GT4-A22. The bounded-convergence step of Astra A.1.6.
The band exits of A21 eventually equal the original horizon on every path whose
gaps are nonzero. This file applies A19's convergence theorem to their actual
indicator processes. It also supplies continuous adapted stopped versions for
a deterministic positive starting time.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The processes used in the band cutoff, including its good-path indicator. -/
def bandStopped {ι : Type*} [Fintype ι] [Nonempty ι]
    (Y : ι → ℝ≥0 → Ω → ℝ) (M : ℝ≥0 → Ω → ℝ)
    (ε R : ℝ≥0) (T : Ω → ℝ≥0) (k : ℕ) (t : ℝ≥0) : Ω → ℝ :=
  (bandEv Y (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) ε T).indicator
    (fun ω => M (min t (bandExit Y (1 / ((k : ℝ) + 1))
      ((k : ℝ) + 1) ε R T ω)) ω)

section Band

variable {ι : Type*} [Fintype ι] [Nonempty ι]
    {𝓕 : Filtration ℝ≥0 mΩ} {Y : ι → ℝ≥0 → Ω → ℝ}
    {M : ℝ≥0 → Ω → ℝ} {ε R : ℝ≥0} {T : Ω → ℝ≥0}

/-- The localized stopped density is measurable. -/
theorem measurable_bandStopped
    (hYc : ∀ i ω, Continuous (Y i · ω))
    (hYm : ∀ i u, Measurable[𝓕 u] (Y i u))
    (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0))
    (hMm : ∀ u, Measurable[𝓕 u] (M u))
    (hMc : ∀ ω, Continuous (M · ω)) (k : ℕ) (t : ℝ≥0) :
    Measurable (bandStopped Y M ε R T k t) := by
  have hS := isStoppingTime_bandExit hYc hYm hT (ε := ε) (R := R)
    (γ := 1 / ((k : ℝ) + 1)) (Γ := (k : ℝ) + 1)
  exact Measurable.indicator
    ((measurable_stopped_min hS hMm hMc t).mono (𝓕.le t) le_rfl)
    (𝓕.le ε _ (measurableSet_bandEv hYm hT))

/-- The band cutoff processes converge pointwise, including paths for which
the horizon precedes the positive starting time. -/
theorem tendsto_bandStopped
    (hYc : ∀ i ω, Continuous (Y i · ω))
    (hTR : ∀ ω, T ω ≤ ε + R)
    (hne : ∀ ω, ε ≤ T ω → ∀ i u, ε ≤ u → u ≤ T ω → Y i u ω ≠ 0)
    (t : ℝ≥0) (ω : Ω) :
    Tendsto (fun k => bandStopped Y M ε R T k t ω) atTop
      (𝓝 ({ω | ε ≤ T ω}.indicator (fun ω => M (min t (T ω)) ω) ω)) := by
  by_cases hεT : ε ≤ T ω
  · have hev := eventually_bandEv_bandExit_eq hYc hεT (hTR ω) (hne ω hεT)
    apply tendsto_const_nhds.congr'
    filter_upwards [hev] with k hk
    simp only [bandStopped, indicator_of_mem hk.1, hk.2,
      indicator_of_mem (show ω ∈ {ω | ε ≤ T ω} from hεT)]
  · have hout : ∀ k, ω ∉ bandEv Y (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) ε T :=
      fun k hk => hεT hk.1
    simp only [bandStopped, indicator_of_notMem (hout _),
      indicator_of_notMem (show ω ∉ {ω | ε ≤ T ω} from hεT)]
    exact tendsto_const_nhds

/-- **The `k → ∞` step**: the good-event martingale identities pass to the
original horizon. Boundedness is only required up to that horizon. -/
theorem integral_indicator_mul_stopped_sub_eq_zero_of_band
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
    (hk : ∀ k, ∫ ω,
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
  have hid : ∀ k, ∫ ω, ξ ω *
      (bandStopped Y M ε R T k t ω - bandStopped Y M ε R T k s ω) ∂P = 0 := by
    intro k
    convert hk k using 1
    apply integral_congr_ae
    filter_upwards [] with ω
    by_cases hω : ω ∈ bandEv Y (1 / ((k : ℝ) + 1)) ((k : ℝ) + 1) ε T
    · simp only [bandStopped, indicator_of_mem hω]
    · simp only [bandStopped, indicator_of_notMem hω, sub_self, mul_zero, zero_mul]
  have h := integral_mul_sub_eq_zero_of_tendsto hξ hξb
    (fun k u => (measurable_bandStopped hYc hYm hT hMm hMc k u).aestronglyMeasurable)
    hkb (tendsto_bandStopped hYc hTR hne) hid
  convert h using 1
  apply integral_congr_ae
  filter_upwards [] with ω
  by_cases hω : ε ≤ T ω
  · simp only [indicator_of_mem (show ω ∈ {ω | ε ≤ T ω} from hω)]
  · simp only [indicator_of_notMem (show ω ∉ {ω | ε ≤ T ω} from hω),
      sub_self, mul_zero, zero_mul]

end Band

/-- Remove the event that the horizon is later than a positive starting time.
The horizon need only be strictly positive pathwise; no uniform lower bound
is required. -/
theorem integral_mul_sub_eq_zero_of_pos_horizon
    {P : Measure Ω} [IsFiniteMeasure P] {M : ℝ≥0 → Ω → ℝ}
    {T : Ω → ℝ≥0} {C : ℝ} (hC : 0 ≤ C)
    (hm : ∀ u, AEStronglyMeasurable (M u) P)
    (hb : ∀ u ω, |M u ω| ≤ C) (hT : Measurable T)
    (hTpos : ∀ ω, 0 < T ω) {s t : ℝ≥0} (hs : 0 < s)
    {ξ : Ω → ℝ} (hξ : Measurable ξ) (hξb : ∀ ω, |ξ ω| ≤ 1)
    (hε : ∀ ε : ℝ≥0, 0 < ε → ε ≤ s →
      ∫ ω, {ω | ε ≤ T ω}.indicator ξ ω * (M t ω - M s ω) ∂P = 0) :
    ∫ ω, ξ ω * (M t ω - M s ω) ∂P = 0 := by
  let ε : ℕ → ℝ≥0 := fun k => s / (k + 1)
  have hεpos : ∀ k, 0 < ε k := fun k => div_pos hs (by positivity)
  have hεle : ∀ k, ε k ≤ s := fun k =>
    div_le_self (zero_le (a := s)) (by
      have : (0 : ℝ≥0) ≤ k := zero_le
      change 1 ≤ (k : ℝ≥0) + 1
      exact le_add_of_nonneg_left this)
  have hε0 : Tendsto ε atTop (𝓝 0) := by
    apply NNReal.tendsto_coe.1
    have h := (tendsto_const_div_atTop_nhds_zero_nat (s : ℝ)).comp
      (tendsto_add_atTop_nat 1)
    simpa only [ε, NNReal.coe_div, NNReal.coe_add, NNReal.coe_natCast,
      NNReal.coe_one, NNReal.coe_zero, Nat.cast_add, Nat.cast_one, Function.comp_def] using h
  let Mk : ℕ → ℝ≥0 → Ω → ℝ := fun k u => {ω | ε k ≤ T ω}.indicator (M u)
  have hkm : ∀ k u, AEStronglyMeasurable (Mk k u) P := fun k u =>
    (hm u).indicator (measurableSet_le measurable_const hT)
  have hkb : ∀ k u ω, |Mk k u ω| ≤ C := by
    intro k u ω
    by_cases hω : ω ∈ {ω | ε k ≤ T ω}
    · simpa only [Mk, indicator_of_mem hω] using hb u ω
    · simpa only [Mk, indicator_of_notMem hω, abs_zero] using hC
  have hlim : ∀ u ω, Tendsto (fun k => Mk k u ω) atTop (𝓝 (M u ω)) := by
    intro u ω
    apply tendsto_const_nhds.congr'
    filter_upwards [hε0.eventually (gt_mem_nhds (hTpos ω))] with k hk
    exact (indicator_of_mem (show ω ∈ {ω | ε k ≤ T ω} from hk.le) (M u)).symm
  apply integral_mul_sub_eq_zero_of_tendsto hξ hξb hkm hkb hlim
  intro k
  convert hε (ε k) (hεpos k) (hεle k) using 1
  apply integral_congr_ae
  filter_upwards [] with ω
  by_cases hω : ω ∈ {ω | ε k ≤ T ω}
  · simp only [Mk, indicator_of_mem hω]
  · simp only [Mk, indicator_of_notMem hω, sub_self, mul_zero, zero_mul]

end InteractingSLE.ZhanGT4
