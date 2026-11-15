/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedFin2Coeff
import InteractingSLE.Spec.ZhanGT4.DualSeedUniformMartingale

/-!
# Actual normalized-log agreement on exhausted seed bands

Packet PROVE-ZHAN-GT4-A22. The band endpoint equality identifies the
compensated actual field with the normalized seeded log increment and
the quadratic integral of the original predictable noise.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {𝓕 : Filtration ℝ≥0 mΩ}
  {κ ρ K : ℝ} {n : ℕ} {d : Ω → SeedData n} {B D : ℝ≥0 → Ω → ℝ}
  {ε t : ℝ≥0} {S T : Ω → ℝ≥0} {E : Set Ω}

/-- This is the actual compensated-increment stage equality; neither
normalization nor energy agreement is supplied as an extra premise. -/
theorem seed_band_log_agreement (hκ : 0 ≤ κ) (hε : 0 < ε) (hεt : ε ≤ t)
    (hdW : ∀ ω, (d ω).W = driftDriver (Real.sqrt κ) B D ω)
    (hp : IsStronglyProgressive 𝓕 (seedNoise κ d T))
    {C : ℝ} (hb : ∀ u ω, |seedNoise κ d T u ω| ≤ C)
    (hL : IsDriftLogField 𝓕 (Real.sqrt κ) ρ K B D
      (onEvB E (fun ω => (d ω).drift)) ε (onEvS E ε S)
      (onEv E (fun ω => (d ω).ell)) (onEv E (fun ω => (d ω).ellX))
      (onEv E (fun ω => (d ω).ellXX)) (onEv E (fun ω => (d ω).ellXXX))
      (onEv E (fun ω => (d ω).ellT)))
    {ω : Ω} (hω : ω ∈ E) (hST : S ω = T ω)
    (hne : ∀ i u, u ∈ Ioc (0 : ℝ) (T ω) → (d ω).gapVal i u ≠ 0) :
    seedEndProcess ε (Ito.fieldStopped
      (seedRestartLog (onEv E (fun ω => (d ω).ell)) (Real.sqrt κ) B D ε)
      (seedRestartDeriv 2 (onEv E (fun ω => (d ω).ellXX)) (Real.sqrt κ) B D ε)
      (seedRestartTime (onEv E (fun ω => (d ω).ellX)) (onEv E (fun ω => (d ω).ellT))
        (onEvB E (fun ω => (d ω).drift)) (Real.sqrt κ) B D ε)
      (shiftBM B ε) (fun ω => onEvS E ε S ω - ε) 0) t ω -
    seedEndProcess ε (Ito.fieldStopped
      (seedRestartLog (onEv E (fun ω => (d ω).ell)) (Real.sqrt κ) B D ε)
      (seedRestartDeriv 2 (onEv E (fun ω => (d ω).ellXX)) (Real.sqrt κ) B D ε)
      (seedRestartTime (onEv E (fun ω => (d ω).ellX)) (onEv E (fun ω => (d ω).ellT))
        (onEvB E (fun ω => (d ω).drift)) (Real.sqrt κ) B D ε)
      (shiftBM B ε) (fun ω => onEvS E ε S ω - ε) 0) 0 ω =
      (d ω).normEll (min t (T ω)) - (d ω).normEll ε +
        (Girsanov.quadInt (seedNoise κ d T) t ω - Girsanov.quadInt (seedNoise κ d T) ε ω) / 2 := by
  have hεT : ε ≤ T ω := by
    simpa only [onEvS_of_mem hω, hST] using hL.le ω
  have hn (u : ℝ≥0) (hεu : ε ≤ u) (huT : u ≤ T ω) :
      (d ω).normEll u = (d ω).ell u ((d ω).W u) :=
    (d ω).normEll_eq_ell_of_gapVal_ne fun i =>
      hne i u ⟨NNReal.coe_pos.2 (hε.trans_le hεu), huT⟩
  have hl := hL.seed_compensated_band_eq hεt ω
  simp only [onEv_of_mem hω, onEvS_of_mem hω, hST, Real.sq_sqrt hκ] at hl
  simp_rw [← hdW ω] at hl
  have h0 : seedEndProcess ε (Ito.fieldStopped
      (seedRestartLog (onEv E (fun ω => (d ω).ell)) (Real.sqrt κ) B D ε)
      (seedRestartDeriv 2 (onEv E (fun ω => (d ω).ellXX)) (Real.sqrt κ) B D ε)
      (seedRestartTime (onEv E (fun ω => (d ω).ellX)) (onEv E (fun ω => (d ω).ellT))
        (onEvB E (fun ω => (d ω).drift)) (Real.sqrt κ) B D ε)
      (shiftBM B ε) (fun ω => onEvS E ε S ω - ε) 0) 0 ω = (d ω).normEll ε := by
    simp only [seedEndProcess, zero_tsub, Ito.fieldStopped, zero_min, NNReal.coe_zero,
      intervalIntegral.integral_same, sub_zero]
    have hz := seedRestartLog_at_driver (onEv E (fun ω => (d ω).ell)) (Real.sqrt κ) B D ε 0 ω
    simp only [NNReal.coe_zero, add_zero, onEv_of_mem hω, ← hdW ω] at hz
    exact hz.trans (hn ε le_rfl hεT).symm
  have henergy := seedNoise_quadInt_sub hκ hp hb hεt ω hεT
  have hmin := hn (min t (T ω)) (le_min hεt hεT) (min_le_right _ _)
  rw [h0]
  simp only [NNReal.coe_min] at hl hmin henergy ⊢
  rw [← hmin] at hl
  linarith only [hl, henergy]

end InteractingSLE.ZhanGT4
