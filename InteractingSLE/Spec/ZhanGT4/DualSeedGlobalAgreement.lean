/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedGlobalBandIto

/-!
# Actual map coefficient agreement for removing the gap bands

Packet PROVE-ZHAN-GT4-A22. The event-localized map coefficient agrees
with the cut endpoint coefficient when the band exit reaches the target.
Both its measurability and its complementary-event value are checked.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal
namespace InteractingSLE.ZhanGT4
open Girsanov
variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- On an exhausted band the coefficient is the actual mapped-driver coefficient. -/
theorem seedMapBandCoeff_agrees {n : ℕ} {d : Ω → SeedData n} {κ : ℝ}
    {B D : ℝ≥0 → Ω → ℝ} (hdW : ∀ ω, (d ω).W = driftDriver (Real.sqrt κ) B D ω)
    {ε : ℝ≥0} (hε : 0 < ε) {E : Set Ω} {S T : Ω → ℝ≥0} {ω : Ω}
    (hω : ω ∈ E) (hle : ε ≤ S ω) (he : S ω = T ω) (u : ℝ≥0) :
    seedMapBandCoeff d κ B D ε E S u ω = seedEndWindow ε (seedFin2Endpoint T
      (positiveStopped (fun u ω => Real.sqrt κ * (d ω).A 1 u) T)) u ω := by
  have hf : (fun (u : ℝ≥0) ω => Real.sqrt κ * (d ω).F 1 u
      (driftDriver (Real.sqrt κ) B D ω u)) = fun (u : ℝ≥0) ω => Real.sqrt κ * (d ω).A 1 u := by
    funext u ω
    rw [← hdW ω, (d ω).F_driver]
  exact (seed_band_coef_agreement hω hε hle he u).trans (by rw [hf])

/-- The localized coefficient vanishes identically off its event. -/
theorem seedMapBandCoeff_off {n : ℕ} (d : Ω → SeedData n) (κ : ℝ)
    (B D : ℝ≥0 → Ω → ℝ) (ε : ℝ≥0) {E : Set Ω} (S : Ω → ℝ≥0) {ω : Ω}
    (hω : ω ∉ E) (u : ℝ≥0) : seedMapBandCoeff d κ B D ε E S u ω = 0 := by
  have hle : ε ≤ onEvS E ε S ω := by rw [onEvS_of_notMem hω]
  rw [seedMapBandCoeff, seed_restart_coef_eq _ _ _ _ _ _ _ hle,
    onEvS_of_notMem hω, onEv_of_notMem hω, mul_zero]
  exact ite_self 0

/-- The localized coefficient has the facts required by the chosen integral. -/
theorem seedMapBandCoeff_facts {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {n : ℕ} {d : Ω → SeedData n} {κ ρ K : ℝ}
    {B D : ℝ≥0 → Ω → ℝ} {ε : ℝ≥0} {S T : Ω → ℝ≥0} {E : Set Ω}
    (hdW : ∀ ω, (d ω).W = driftDriver (Real.sqrt κ) B D ω)
    (hF : IsSeedDriftField (Real.sqrt κ) ρ K B D (onEvB E (seedMappedDrift κ d T))
      ε (onEvS E ε S) (onEv E (fun ω => (d ω).F 0)) (onEv E (fun ω => (d ω).F 1))
      (onEv E (fun ω => (d ω).F 2)) (onEv E (fun ω => (d ω).F 3))
      (onEv E (fun ω => (d ω).mapTime)))
    (hBc : ∀ ω, Continuous (B · ω)) (hκ : 0 < κ) (hρ : 0 < ρ)
    (hS : IsStoppingTime 𝓕 fun ω => (onEvS E ε S ω : WithTop ℝ≥0))
    (hm : ∀ u : ℝ≥0, ε ≤ u → Measurable[𝓕 u]
      ((E ∩ {ω | u ≤ S ω}).indicator fun ω => (d ω).A 1 u)) :
    StronglyAdapted 𝓕 (seedMapBandCoeff d κ B D ε E S) ∧
      IsRiemannRegular P (seedMapBandCoeff d κ B D ε E S) ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ u ω, |seedMapBandCoeff d κ B D ε E S u ω| ≤ C := by
  apply hF.seed_original_coef_facts hBc (Real.sqrt_pos.2 hκ) hρ hS
  intro u hu
  rw [seedMap_event_value_eq hdW]
  exact hm u hu

/-- Uniformly bounded alive coefficients keep their integral facts after
stopping, removing the endpoint and cutting at a positive time. -/
theorem seedMap_window_facts {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {n : ℕ} {d : Ω → SeedData n} {κ : ℝ} {T : Ω → ℝ≥0} (ε : ℝ≥0)
    (hT : IsStoppingTime 𝓕 fun ω => (T ω : WithTop ℝ≥0))
    (hm : ∀ u, Measurable[𝓕 u] ({ω | u ≤ T ω}.indicator fun ω => (d ω).A 1 u))
    (hc : ∀ ω, ContinuousOn (fun u : ℝ≥0 => (d ω).A 1 u) (Ioc 0 (T ω)))
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ u ω, 0 < u → u ≤ T ω → |(d ω).A 1 u| ≤ C) :
    let w := seedEndWindow ε (seedFin2Endpoint T
      (positiveStopped (fun u ω => Real.sqrt κ * (d ω).A 1 u) T))
    StronglyAdapted 𝓕 w ∧ IsRiemannRegular P w ∧
      ∀ u ω, |w u ω| ≤ |Real.sqrt κ| * C := by
  have hp := isStronglyPredictable_positiveStopped 𝓕
    (X := fun u ω => Real.sqrt κ * (d ω).A 1 u) (S := T)
    (fun u => by
      convert (hm u).const_mul (Real.sqrt κ) using 1
      funext ω
      by_cases hu : u ≤ T ω <;> simp [indicator, hu])
    (fun ω => continuousOn_const.mul (hc ω))
  have hr := isRiemannRegular_positiveStopped P
    (X := fun u ω => Real.sqrt κ * (d ω).A 1 u) (S := T)
    (fun ω => continuousOn_const.mul (hc ω))
  have hb' : ∀ u ω, |positiveStopped (fun u ω => Real.sqrt κ * (d ω).A 1 u) T u ω| ≤
      |Real.sqrt κ| * C := by
    intro u ω
    unfold positiveStopped
    split_ifs with h
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hb u ω h.1 h.2) (abs_nonneg _)
    · simpa only [abs_zero] using mul_nonneg (abs_nonneg (Real.sqrt κ)) hC
  refine ⟨seedEndWindow_adapted (seedFin2Endpoint_adapted hT hp.stronglyAdapted),
    seedEndWindow_isRiemannRegular (seedFin2Endpoint_regular hr), ?_⟩
  intro u ω
  unfold seedEndWindow
  split_ifs
  · exact abs_seedFin2Endpoint_le (mul_nonneg (abs_nonneg _) hC) hb' u ω
  · simpa only [abs_zero] using mul_nonneg (abs_nonneg (Real.sqrt κ)) hC

end InteractingSLE.ZhanGT4
