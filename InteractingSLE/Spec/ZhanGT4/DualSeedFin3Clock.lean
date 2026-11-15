/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedFin3MapField

/-!
# The mapped field and its generator in the original clock

Packet PROVE-ZHAN-GT4-A22. Identify the compensated map band before
removing its localization. The generator is the actual finite-variation
rate, and the stochastic coefficient is the actual first derivative.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The Itô generator along the drifted driver, without a logarithmic square. -/
def seedDriftGenerator (ℓx ℓxx ℓt : Ω → ℝ → ℝ → ℝ) (b : Ω → ℝ → ℝ)
    (σ : ℝ) (B D : ℝ≥0 → Ω → ℝ) (ω : Ω) (t : ℝ) : ℝ :=
  ℓt ω t (driftDriver σ B D ω t) + b ω t * ℓx ω t (driftDriver σ B D ω t) +
    σ ^ 2 / 2 * ℓxx ω t (driftDriver σ B D ω t)

/-- The shifted Brownian generator is exactly the drifted generator at
original time `ε + u`. -/
theorem seedRestart_generator_eq (ℓx ℓxx ℓt : Ω → ℝ → ℝ → ℝ) (b : Ω → ℝ → ℝ)
    (σ : ℝ) (B D : ℝ≥0 → Ω → ℝ) (ε : ℝ≥0) (ω : Ω) {u : ℝ} (hu : 0 ≤ u) :
    Ito.fieldGen (seedRestartDeriv 2 ℓxx σ B D ε) (seedRestartTime ℓx ℓt b σ B D ε)
      (shiftBM B ε) u ω = seedDriftGenerator ℓx ℓxx ℓt b σ B D ω ((ε : ℝ) + u) := by
  simp only [Ito.fieldGen, seedRestartDeriv, seedRestartTime, shiftFieldT, shiftField]
  rw [shiftBM_add_shiftOff σ B D ε ω hu]
  unfold seedDriftGenerator
  ring

/-- The compensated restarted field is the original-time field minus
its generator integral. This identity has no martingale-generator premise. -/
theorem seed_compensated_field_band_eq (ℓ ℓx ℓxx ℓt : Ω → ℝ → ℝ → ℝ)
    (b : Ω → ℝ → ℝ) (σ : ℝ) (B D : ℝ≥0 → Ω → ℝ) (ε : ℝ≥0) (S : Ω → ℝ≥0)
    {t : ℝ≥0} (hεt : ε ≤ t) (ω : Ω) (hεS : ε ≤ S ω) :
    seedEndProcess ε (Ito.fieldStopped (seedRestartLog ℓ σ B D ε)
      (seedRestartDeriv 2 ℓxx σ B D ε) (seedRestartTime ℓx ℓt b σ B D ε)
      (shiftBM B ε) (fun ω => S ω - ε) 0) t ω =
    ℓ ω (min t (S ω)) (driftDriver σ B D ω (min t (S ω))) -
      ∫ u in (ε : ℝ)..(min t (S ω) : ℝ≥0), seedDriftGenerator ℓx ℓxx ℓt b σ B D ω u := by
  let q := min (t - ε) (S ω - ε)
  have hq : ε + q = min t (S ω) := IsDriftLogField.add_min_tsub hεt hεS
  have hqr : (ε : ℝ) + (q : ℝ) = (min t (S ω) : ℝ≥0) := by exact_mod_cast hq
  have hi : (∫ u in (0 : ℝ)..(q : ℝ),
      Ito.fieldGen (seedRestartDeriv 2 ℓxx σ B D ε)
        (seedRestartTime ℓx ℓt b σ B D ε) (shiftBM B ε) u ω) =
      ∫ u in (ε : ℝ)..(min t (S ω) : ℝ≥0), seedDriftGenerator ℓx ℓxx ℓt b σ B D ω u := by
    calc
      _ = ∫ u in (0 : ℝ)..(q : ℝ), seedDriftGenerator ℓx ℓxx ℓt b σ B D ω ((ε : ℝ) + u) := by
        apply intervalIntegral.integral_congr
        intro u hu
        rw [uIcc_of_le q.coe_nonneg] at hu
        exact seedRestart_generator_eq ℓx ℓxx ℓt b σ B D ε ω hu.1
      _ = _ := by
        rw [intervalIntegral.integral_comp_add_left (seedDriftGenerator ℓx ℓxx ℓt b σ B D ω)
          (ε : ℝ), add_zero, hqr]
  change seedRestartLog ℓ σ B D ε q ω (shiftBM B ε q ω) - _ = _
  rw [seedRestartLog_at_driver, hqr, hi]
  rfl

/-- Adapted alive values can be restarted without assuming measurability
of a stochastic remainder or changing the chosen stochastic integral. -/
theorem seed_alive_shift_measurable {𝓕 : Filtration ℝ≥0 mΩ} {ε : ℝ≥0} {S : Ω → ℝ≥0}
    (hle : ∀ ω, ε ≤ S ω) {g : Ω → ℝ → ℝ}
    (hm : ∀ u : ℝ≥0, ε ≤ u → Measurable[𝓕 u]
      ({ω | u ≤ S ω}.indicator fun ω => g ω u)) (u : ℝ≥0) :
    Measurable[LP.LP4HB.shiftFiltration 𝓕 ε u]
      ({ω | u ≤ S ω - ε}.indicator fun ω => g ω ((ε : ℝ) + u)) := by
  have hs (ω : Ω) : u ≤ S ω - ε ↔ ε + u ≤ S ω := by
    constructor
    · intro hu
      have hh := add_le_add_left hu ε
      simpa only [tsub_add_cancel_of_le (hle ω), add_comm u ε] using hh
    · intro hu
      apply (add_le_add_iff_left ε).1
      simpa only [add_tsub_cancel_of_le (hle ω)] using hu
  change Measurable[𝓕 (ε + u)] _
  convert hm (ε + u) (le_add_of_nonneg_right (zero_le (a := u))) using 1
  funext ω
  simp only [hs, NNReal.coe_add]

end InteractingSLE.ZhanGT4
