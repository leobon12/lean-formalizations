/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedEndRestart

/-!
# The positive-band logarithm in its original clock

Packet PROVE-ZHAN-GT4-A22. Identify the compensated stopped band field
with the actual logarithm and its original-time quadratic correction.
The resulting Itô formula uses the original chosen stochastic integral.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {σ ρ K : ℝ} {B D : ℝ≥0 → Ω → ℝ}
  {b : Ω → ℝ → ℝ} {ε : ℝ≥0} {S : Ω → ℝ≥0}
  {ℓ ℓx ℓxx ℓxxx ℓt : Ω → ℝ → ℝ → ℝ}

/-- The compensated restarted field is the actual original-time
logarithm plus its quadratic correction, pathwise. -/
theorem IsDriftLogField.seed_compensated_band_eq
    (h : IsDriftLogField 𝓕 σ ρ K B D b ε S ℓ ℓx ℓxx ℓxxx ℓt)
    {t : ℝ≥0} (hεt : ε ≤ t) (ω : Ω) :
    seedEndProcess ε (Ito.fieldStopped (seedRestartLog ℓ σ B D ε)
      (seedRestartDeriv 2 ℓxx σ B D ε) (seedRestartTime ℓx ℓt b σ B D ε)
      (shiftBM B ε) (fun ω => S ω - ε) 0) t ω =
    ℓ ω (min t (S ω)) (driftDriver σ B D ω (min t (S ω))) + σ ^ 2 / 2 *
      (∫ u in (ε : ℝ)..(min t (S ω) : ℝ≥0), ℓx ω u (driftDriver σ B D ω u) ^ 2) := by
  let q := min (t - ε) (S ω - ε)
  have hq : ε + q = min t (S ω) := IsDriftLogField.add_min_tsub hεt (h.le ω)
  have hqr : (ε : ℝ) + (q : ℝ) = (min t (S ω) : ℝ≥0) := by exact_mod_cast hq
  have hi : (∫ u in (0 : ℝ)..(q : ℝ),
      Ito.fieldGen (seedRestartDeriv 2 ℓxx σ B D ε)
        (seedRestartTime ℓx ℓt b σ B D ε) (shiftBM B ε) u ω) =
      -(σ ^ 2 / 2) * (∫ u in (ε : ℝ)..(min t (S ω) : ℝ≥0),
        ℓx ω u (driftDriver σ B D ω u) ^ 2) := by
    calc
      _ = ∫ u in (0 : ℝ)..(q : ℝ), -(σ ^ 2 / 2) *
          ℓx ω ((ε : ℝ) + u) (driftDriver σ B D ω ((ε : ℝ) + u)) ^ 2 := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [uIcc_of_le q.coe_nonneg] at hu
        have hu' : u ∈ Icc (0 : ℝ) (S ω - ε : ℝ≥0) :=
          ⟨hu.1, hu.2.trans (show (q : ℝ) ≤ (S ω - ε : ℝ≥0) from min_le_right _ _)⟩
        have he := h.gen ω _ (h.mapsTo_add ω hu')
        simp only [Ito.fieldGen, seedRestartDeriv, seedRestartTime, shiftFieldT, shiftField]
        rw [shiftBM_add_shiftOff σ B D ε ω hu'.1]
        linarith only [he]
      _ = _ := by
        rw [intervalIntegral.integral_const_mul,
          intervalIntegral.integral_comp_add_left
            (fun u => ℓx ω u (driftDriver σ B D ω u) ^ 2) (ε : ℝ), add_zero, hqr]
  change seedRestartLog ℓ σ B D ε q ω (shiftBM B ε q ω) - _ = _
  rw [seedRestartLog_at_driver, hqr, hi]
  simp only [NNReal.coe_min]
  ring

/-- Original-clock positive-band Itô formula for the actual logarithm.
Neither a Taylor estimate nor a shifted-integral identity is an input. -/
theorem IsDriftLogField.seed_original_logIto
    {P : Measure Ω}
    (h : IsDriftLogField 𝓕 σ ρ K B D b ε S ℓ ℓx ℓxx ℓxxx ℓt)
    (hB : IsFilteredBrownianReal 𝓕 B P) (hBc : ∀ ω, Continuous (B · ω))
    (hσ : 0 < σ) (hρ : 0 < ρ)
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0))
    {t : ℝ≥0} (hεt : ε ≤ t) :
    (fun ω => ℓ ω (min t (S ω)) (driftDriver σ B D ω (min t (S ω))) -
      ℓ ω ε (driftDriver σ B D ω ε) + σ ^ 2 / 2 *
        (∫ u in (ε : ℝ)..(min t (S ω) : ℝ≥0), ℓx ω u (driftDriver σ B D ω u) ^ 2)) =ᵐ[P]
    fun ω => Girsanov.stochIntegral P 𝓕 B
        (seedEndCoef ε (Ito.stopCoef (seedRestartDeriv 1 ℓx σ B D ε)
          (shiftBM B ε) (fun ω => S ω - ε))) t ω -
      Girsanov.stochIntegral P 𝓕 B
        (seedEndCoef ε (Ito.stopCoef (seedRestartDeriv 1 ℓx σ B D ε)
          (shiftBM B ε) (fun ω => S ω - ε))) 0 ω := by
  filter_upwards [h.seed_original_stochIntegral hB hBc hσ hρ hS t] with ω hω
  rw [h.seed_compensated_band_eq hεt] at hω
  have h0 : seedEndProcess ε (Ito.fieldStopped (seedRestartLog ℓ σ B D ε)
      (seedRestartDeriv 2 ℓxx σ B D ε) (seedRestartTime ℓx ℓt b σ B D ε)
      (shiftBM B ε) (fun ω => S ω - ε) 0) 0 ω =
      ℓ ω ε (driftDriver σ B D ω ε) := by
    simp only [seedEndProcess, zero_tsub, Ito.fieldStopped, zero_min,
      NNReal.coe_zero, intervalIntegral.integral_same, sub_zero]
    simpa only [NNReal.coe_zero, add_zero] using seedRestartLog_at_driver ℓ σ B D ε 0 ω
  rw [h0] at hω
  linarith only [hω]

end InteractingSLE.ZhanGT4
