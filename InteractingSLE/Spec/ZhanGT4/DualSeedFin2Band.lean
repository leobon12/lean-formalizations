/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedFin2LogAgreement

/-!
# The actual band process and its behavior off the good event

Packet PROVE-ZHAN-GT4-A22. Name the already constructed process and
coefficient, and verify the complementary-event and stopped-energy cases.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

open Girsanov

variable {Ω : Type*} {n : ℕ}

/-- The actual original-clock compensated process on a seed band. -/
def seedFin2BandProcess (d : Ω → SeedData n) (κ : ℝ) (B D : ℝ≥0 → Ω → ℝ)
    (ε : ℝ≥0) (E : Set Ω) (S : Ω → ℝ≥0) : ℝ≥0 → Ω → ℝ :=
  seedEndProcess ε (Ito.fieldStopped
    (seedRestartLog (onEv E (fun ω => (d ω).ell)) (Real.sqrt κ) B D ε)
    (seedRestartDeriv 2 (onEv E (fun ω => (d ω).ellXX)) (Real.sqrt κ) B D ε)
    (seedRestartTime (onEv E (fun ω => (d ω).ellX)) (onEv E (fun ω => (d ω).ellT))
      (onEvB E (fun ω => (d ω).drift)) (Real.sqrt κ) B D ε)
    (shiftBM B ε) (fun ω => onEvS E ε S ω - ε) 0)

/-- Its actual original-clock first spatial coefficient. -/
def seedFin2BandCoeff (d : Ω → SeedData n) (κ : ℝ) (B D : ℝ≥0 → Ω → ℝ)
    (ε : ℝ≥0) (E : Set Ω) (S : Ω → ℝ≥0) : ℝ≥0 → Ω → ℝ :=
  seedEndCoef ε (Ito.stopCoef
    (seedRestartDeriv 1 (onEv E (fun ω => (d ω).ellX)) (Real.sqrt κ) B D ε)
    (shiftBM B ε) (fun ω => onEvS E ε S ω - ε))

theorem seedFin2Band_zero {d : Ω → SeedData n} {κ : ℝ} {B D : ℝ≥0 → Ω → ℝ}
    {ε : ℝ≥0} {E : Set Ω} {S : Ω → ℝ≥0} {ω : Ω} (hω : ω ∉ E) (u : ℝ≥0) :
    seedFin2BandCoeff d κ B D ε E S u ω = 0 ∧ seedFin2BandProcess d κ B D ε E S u ω = 0 := by
  constructor
  · simp only [seedFin2BandCoeff, seedEndCoef, Ito.stopCoef, onEvS_of_notMem hω,
      tsub_self, not_lt_zero, ite_false, ite_self]
  · simp only [seedFin2BandProcess, seedEndProcess, Ito.fieldStopped, onEvS_of_notMem hω,
      tsub_self, min_zero, NNReal.coe_zero, intervalIntegral.integral_same, sub_zero,
      seedRestartLog, shiftField, onEv_of_notMem hω]

/-- The source coefficient equality now uses the exact original negative
noise convention, with only the endpoint value removed. -/
theorem seedFin2Band_coef_agrees {d : Ω → SeedData n} {κ : ℝ} {B D : ℝ≥0 → Ω → ℝ}
    {ε : ℝ≥0} {E : Set Ω} {S T : Ω → ℝ≥0}
    (hdW : ∀ ω, (d ω).W = driftDriver (Real.sqrt κ) B D ω)
    {ω : Ω} (hω : ω ∈ E) (hε : 0 < ε) (hεS : ε ≤ S ω) (hST : S ω = T ω) (u : ℝ≥0) :
    seedFin2BandCoeff d κ B D ε E S u ω =
      seedEndWindow ε (seedFin2Endpoint T (fun u ω => -seedNoise κ d T u ω)) u ω := by
  have he : positiveStopped
      (fun u ω => Real.sqrt κ * (d ω).ellX u (driftDriver (Real.sqrt κ) B D ω u)) T =
      fun u ω => -seedNoise κ d T u ω := by
    funext u ω
    simp only [seedNoise, positiveStopped, hdW ω]
    split_ifs <;> ring
  exact (seed_band_coef_agreement hω hε hεS hST u).trans (by rw [he])

/-- After the horizon the original quadratic integral is constant. -/
theorem seedNoise_quadInt_sub_of_horizon_le {mΩ : MeasurableSpace Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} {κ : ℝ} {d : Ω → SeedData n} {T : Ω → ℝ≥0}
    (hp : IsStronglyProgressive 𝓕 (seedNoise κ d T))
    {C : ℝ} (hb : ∀ u ω, |seedNoise κ d T u ω| ≤ C)
    {ε t : ℝ≥0} (hεt : ε ≤ t) (ω : Ω) (hTε : T ω ≤ ε) :
    quadInt (seedNoise κ d T) t ω - quadInt (seedNoise κ d T) ε ω = 0 := by
  have hi := intervalIntegrable_time (seed_square_progressive hp) (seed_square_bound hb) ω
  have hh := intervalIntegral.integral_add_adjacent_intervals (hi 0 ε) (hi ε t)
  have hz : (∫ u in (ε : ℝ)..t, seedNoise κ d T u.toNNReal ω ^ 2) = 0 := by
    calc _ = ∫ _u in (ε : ℝ)..t, (0 : ℝ) := by
            apply intervalIntegral.integral_congr_ae
            filter_upwards [] with u hu
            rw [uIoc_of_le (show (ε : ℝ) ≤ t from hεt)] at hu
            have huT : ¬ u.toNNReal ≤ T ω := by
              rw [Real.toNNReal_le_iff_le_coe]
              exact not_le_of_gt ((show (T ω : ℝ) ≤ ε from hTε).trans_lt hu.1)
            simp only [seedNoise, positiveStopped, huT, and_false, ite_false,
              zero_pow (by norm_num : 2 ≠ 0)]
      _ = 0 := intervalIntegral.integral_zero
  dsimp only [quadInt]
  linarith only [hh, hz]

end InteractingSLE.ZhanGT4
