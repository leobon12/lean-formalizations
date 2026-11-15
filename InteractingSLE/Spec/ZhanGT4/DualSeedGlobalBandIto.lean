/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedGlobalCoeff

/-!
# The actual mapped-driver integral on an event-localized band

Packet PROVE-ZHAN-GT4-A22. Identify every map value, generator and
coefficient on the band event and its zero complement. These identities
are proved before the gap-band exhaustion is applied.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

open Girsanov

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The original-clock first derivative of the event-localized actual map. -/
def seedMapBandCoeff {n : ℕ} (d : Ω → SeedData n) (κ : ℝ) (B D : ℝ≥0 → Ω → ℝ)
    (ε : ℝ≥0) (E : Set Ω) (S : Ω → ℝ≥0) : ℝ≥0 → Ω → ℝ :=
  seedEndCoef ε (Ito.stopCoef
    (seedRestartDeriv 1 (onEv E (fun ω => (d ω).F 1)) (Real.sqrt κ) B D ε)
    (shiftBM B ε) (fun ω => onEvS E ε S ω - ε))

/-- The actual D10 increment on the event, zero on its complement. -/
def seedMapBandIncrement {n : ℕ} (d : Ω → SeedData n) (ε : ℝ≥0)
    (E : Set Ω) (S : Ω → ℝ≥0) (t : ℝ≥0) : Ω → ℝ :=
  E.indicator fun ω => (d ω).A 0 (min t (S ω)) - (d ω).A 0 ε -
    ∫ u in (ε : ℝ)..(min t (S ω) : ℝ≥0), (d ω).d10Rate u

/-- Alive map values are exactly the already measurable alive conformal coefficients. -/
theorem seedMap_event_value_eq {n : ℕ} {d : Ω → SeedData n} {κ : ℝ}
    {B D : ℝ≥0 → Ω → ℝ} (hdW : ∀ ω, (d ω).W = driftDriver (Real.sqrt κ) B D ω)
    (ε : ℝ≥0) (E : Set Ω) (S : Ω → ℝ≥0) (k : ℕ) (u : ℝ≥0) :
    ({ω | u ≤ onEvS E ε S ω}.indicator fun ω =>
      onEv E (fun ω => (d ω).F k) ω u (driftDriver (Real.sqrt κ) B D ω u)) =
    (E ∩ {ω | u ≤ S ω}).indicator fun ω => (d ω).A k u := by
  classical
  funext ω
  by_cases hω : ω ∈ E
  · by_cases hu : u ≤ S ω
    · simp only [indicator_apply, mem_ofPred_eq, mem_inter_iff, onEvS_of_mem hω,
        hu, hω, and_self, ite_eq_left, onEv_of_mem hω]
      rw [← hdW ω, (d ω).F_driver]
    · simp only [indicator_apply, mem_ofPred_eq, mem_inter_iff, onEvS_of_mem hω,
        hu, hω, and_false, ite_eq_right, not_false_eq_true]
  · simp only [indicator_apply, mem_ofPred_eq, mem_inter_iff, hω, false_and, ite_false,
      onEv_of_notMem hω, ite_self]

/-- The actual generator of the localized map is the localized D10 rate. -/
theorem seedMap_event_generator_eq {n : ℕ} {d : Ω → SeedData n} {κ : ℝ} (hκ : 0 < κ)
    {B D : ℝ≥0 → Ω → ℝ} {ε : ℝ≥0} (hε : 0 < ε) {S T : Ω → ℝ≥0} {E : Set Ω}
    {A : Set ℂ} {r a₀ γ Γ lam ρm : ℝ}
    (hdW : ∀ ω, (d ω).W = driftDriver (Real.sqrt κ) B D ω) (hdκ : ∀ ω, (d ω).κ = κ)
    (hST : ∀ ω ∈ E, S ω ≤ T ω)
    (hown : ∀ ω ∈ E, OwnData (d ω).W A (d ω).φ (S ω) (d ω).a (d ω).W')
    (hc : ∀ ω ∈ E, (d ω).SeedConst A ε (S ω) r a₀ γ Γ lam ρm)
    (ω : Ω) {u : ℝ} (hu : u ∈ Icc (ε : ℝ) (onEvS E ε S ω)) :
    seedDriftGenerator (onEv E (fun ω => (d ω).F 1)) (onEv E (fun ω => (d ω).F 2))
      (onEv E (fun ω => (d ω).mapTime)) (onEvB E (seedMappedDrift κ d T))
      (Real.sqrt κ) B D ω u = E.indicator (fun ω => (d ω).d10Rate u) ω := by
  by_cases hω : ω ∈ E
  · rw [onEvS_of_mem hω] at hu
    have ht : u ∈ Ioc (0 : ℝ) (T ω) :=
      ⟨(NNReal.coe_pos.2 hε).trans_le hu.1, hu.2.trans (hST ω hω)⟩
    simp only [seedDriftGenerator, onEv_of_mem hω, onEvB_of_mem hω,
      indicator_of_mem hω, ← hdW ω, Real.sq_sqrt hκ.le, seedMappedDrift_eq hκ.le d T ω ht]
    have hh := (d ω).map_generator_d10_of_const (hown ω hω) (hc ω hω) ε.coe_nonneg
      (by rw [hdκ ω]; exact hκ.ne') hu
    simpa only [hdκ ω] using hh
  · simp only [seedDriftGenerator, onEv_of_notMem hω, onEvB_of_notMem hω,
      indicator_of_notMem hω, mul_zero, add_zero]

/-- The actual positive-band map increment equals the chosen stochastic
integral increment, including the complementary event. -/
theorem seedMap_original_event_Ito {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    {n : ℕ} {d : Ω → SeedData n} {κ ρ K : ℝ} (hκ : 0 < κ)
    {B D : ℝ≥0 → Ω → ℝ} {ε : ℝ≥0} (hε : 0 < ε) {S T : Ω → ℝ≥0} {E : Set Ω}
    {A : Set ℂ} {r a₀ γ Γ lam ρm : ℝ}
    (hdW : ∀ ω, (d ω).W = driftDriver (Real.sqrt κ) B D ω) (hdκ : ∀ ω, (d ω).κ = κ)
    (hST : ∀ ω ∈ E, S ω ≤ T ω)
    (hown : ∀ ω ∈ E, OwnData (d ω).W A (d ω).φ (S ω) (d ω).a (d ω).W')
    (hc : ∀ ω ∈ E, (d ω).SeedConst A ε (S ω) r a₀ γ Γ lam ρm)
    (hF : IsSeedDriftField (Real.sqrt κ) ρ K B D (onEvB E (seedMappedDrift κ d T))
      ε (onEvS E ε S) (onEv E (fun ω => (d ω).F 0)) (onEv E (fun ω => (d ω).F 1))
      (onEv E (fun ω => (d ω).F 2)) (onEv E (fun ω => (d ω).F 3))
      (onEv E (fun ω => (d ω).mapTime)))
    (hB : IsFilteredBrownianReal 𝓕 B P) (hBc : ∀ ω, Continuous (B · ω)) (hρ : 0 < ρ)
    (hS : IsStoppingTime 𝓕 fun ω => (onEvS E ε S ω : WithTop ℝ≥0))
    (hmA : ∀ k (u : ℝ≥0), ε ≤ u → Measurable[𝓕 u]
      ((E ∩ {ω | u ≤ S ω}).indicator fun ω => (d ω).A k u))
    (hmRate : ∀ u : ℝ≥0, ε ≤ u → Measurable[𝓕 u]
      ((E ∩ {ω | u ≤ S ω}).indicator fun ω => (d ω).d10Rate u))
    {t : ℝ≥0} (hεt : ε ≤ t) :
    seedMapBandIncrement d ε E S t =ᵐ[P] fun ω =>
      stochIntegral P 𝓕 B (seedMapBandCoeff d κ B D ε E S) t ω -
        stochIntegral P 𝓕 B (seedMapBandCoeff d κ B D ε E S) 0 ω := by
  let g := seedDriftGenerator (onEv E (fun ω => (d ω).F 1)) (onEv E (fun ω => (d ω).F 2))
    (onEv E (fun ω => (d ω).mapTime)) (onEvB E (seedMappedDrift κ d T)) (Real.sqrt κ) B D
  have hmF (k : ℕ) (u : ℝ≥0) (hu : ε ≤ u) : Measurable[𝓕 u]
      ({ω | u ≤ onEvS E ε S ω}.indicator fun ω =>
        onEv E (fun ω => (d ω).F k) ω u (driftDriver (Real.sqrt κ) B D ω u)) := by
    rw [seedMap_event_value_eq hdW]
    exact hmA k u hu
  have hgen (ω : Ω) (u : ℝ) (hu : u ∈ Icc (ε : ℝ) (onEvS E ε S ω)) :
      g ω u = E.indicator (fun ω => (d ω).d10Rate u) ω :=
    seedMap_event_generator_eq hκ hε hdW hdκ hST hown hc ω hu
  have hmG (u : ℝ≥0) (hu : ε ≤ u) : Measurable[𝓕 u]
      ({ω | u ≤ onEvS E ε S ω}.indicator fun ω => g ω u) := by
    convert hmRate u hu using 1
    funext ω
    classical
    simp only [indicator_apply, mem_ofPred_eq, mem_inter_iff]
    by_cases hω : ω ∈ E
    · simp only [onEvS_of_mem hω, hω, true_and]
      by_cases hs : u ≤ S ω
      · simp only [hs, ite_true]
        exact (hgen ω u ⟨hu, by
          rw [onEvS_of_mem hω]
          exact_mod_cast hs⟩).trans (indicator_of_mem hω _)
      · simp only [hs, ite_false]
    · simp only [hω, false_and, ite_false]
      by_cases hs : u ≤ onEvS E ε S ω
      · simp only [hs, ite_true]
        exact (hgen ω u ⟨hu, hs⟩).trans (indicator_of_notMem hω _)
      · simp only [hs, ite_false]
  have he := hF.seed_original_fieldIto hB hBc (Real.sqrt_pos.2 hκ) hρ hS
    (hmF 0) (hmF 1) (hmF 2) hmG hεt
  filter_upwards [he] with ω hω
  change _ = stochIntegral P 𝓕 B (seedMapBandCoeff d κ B D ε E S) t ω -
    stochIntegral P 𝓕 B (seedMapBandCoeff d κ B D ε E S) 0 ω at hω
  rw [← hω]
  by_cases hE : ω ∈ E
  · have hle : ε ≤ S ω := by simpa only [onEvS_of_mem hE] using hF.le ω
    have hi : (∫ u in (ε : ℝ)..(min t (onEvS E ε S ω) : ℝ≥0), g ω u) =
        ∫ u in (ε : ℝ)..(min t (S ω) : ℝ≥0), (d ω).d10Rate u := by
      rw [onEvS_of_mem hE]
      apply intervalIntegral.integral_congr
      intro u hu
      rw [uIcc_of_le (show (ε : ℝ) ≤ (min t (S ω) : ℝ≥0) from le_min hεt hle)] at hu
      exact (hgen ω u ⟨hu.1, by
        rw [onEvS_of_mem hE]
        exact hu.2.trans (by exact_mod_cast min_le_right t (S ω))⟩).trans (indicator_of_mem hE _)
    change seedMapBandIncrement d ε E S t ω = _ - _ -
      (∫ u in (ε : ℝ)..(min t (onEvS E ε S ω) : ℝ≥0), g ω u)
    rw [hi]
    simp only [seedMapBandIncrement, indicator_of_mem hE, onEv_of_mem hE,
      onEvS_of_mem hE, ← hdW ω, (d ω).F_driver]
  · simp only [seedMapBandIncrement, indicator_of_notMem hE, onEv_of_notMem hE,
      seedDriftGenerator, onEvB_of_notMem hE, mul_zero, add_zero,
      intervalIntegral.integral_zero, sub_self]

end InteractingSLE.ZhanGT4
