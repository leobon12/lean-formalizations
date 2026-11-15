/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedFin3Clock

/-!
# Original-clock Itô formula with an unrestricted drifted generator

Packet PROVE-ZHAN-GT4-A22. Alive measurability is needed only for the
actual field, its first two derivatives and its generator. Taylor
pasting, stopped-process measurability and integral identification are proved.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Itô's formula in the original Brownian clock, with the actual drifted
generator and the actual stopped first derivative. -/
theorem IsSeedDriftField.seed_original_fieldIto
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {σ ρ K : ℝ}
    {B D : ℝ≥0 → Ω → ℝ} {b : Ω → ℝ → ℝ} {ε : ℝ≥0} {S : Ω → ℝ≥0}
    {ℓ ℓx ℓxx ℓxxx ℓt : Ω → ℝ → ℝ → ℝ}
    (h : IsSeedDriftField σ ρ K B D b ε S ℓ ℓx ℓxx ℓxxx ℓt)
    (hB : IsFilteredBrownianReal 𝓕 B P) (hBc : ∀ ω, Continuous (B · ω))
    (hσ : 0 < σ) (hρ : 0 < ρ)
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0))
    (hm₀ : ∀ u : ℝ≥0, ε ≤ u → Measurable[𝓕 u]
      ({ω | u ≤ S ω}.indicator fun ω => ℓ ω u (driftDriver σ B D ω u)))
    (hm₁ : ∀ u : ℝ≥0, ε ≤ u → Measurable[𝓕 u]
      ({ω | u ≤ S ω}.indicator fun ω => ℓx ω u (driftDriver σ B D ω u)))
    (hm₂ : ∀ u : ℝ≥0, ε ≤ u → Measurable[𝓕 u]
      ({ω | u ≤ S ω}.indicator fun ω => ℓxx ω u (driftDriver σ B D ω u)))
    (hmG : ∀ u : ℝ≥0, ε ≤ u → Measurable[𝓕 u]
      ({ω | u ≤ S ω}.indicator fun ω => seedDriftGenerator ℓx ℓxx ℓt b σ B D ω u))
    {t : ℝ≥0} (hεt : ε ≤ t) :
    (fun ω => ℓ ω (min t (S ω)) (driftDriver σ B D ω (min t (S ω))) -
      ℓ ω ε (driftDriver σ B D ω ε) -
        ∫ u in (ε : ℝ)..(min t (S ω) : ℝ≥0), seedDriftGenerator ℓx ℓxx ℓt b σ B D ω u) =ᵐ[P]
    fun ω => Girsanov.stochIntegral P 𝓕 B
        (seedEndCoef ε (Ito.stopCoef (seedRestartDeriv 1 ℓx σ B D ε)
          (shiftBM B ε) (fun ω => S ω - ε))) t ω -
      Girsanov.stochIntegral P 𝓕 B
        (seedEndCoef ε (Ito.stopCoef (seedRestartDeriv 1 ℓx σ B D ε)
          (shiftBM B ε) (fun ω => S ω - ε))) 0 ω := by
  have hmR (f : Ω → ℝ → ℝ → ℝ)
      (hmf : ∀ u : ℝ≥0, ε ≤ u → Measurable[𝓕 u]
        ({ω | u ≤ S ω}.indicator fun ω => f ω u (driftDriver σ B D ω u))) (u : ℝ≥0) :
      Measurable[LP.LP4HB.shiftFiltration 𝓕 ε u] ({ω | u ≤ S ω - ε}.indicator fun ω =>
        seedRestartLog f σ B D ε u ω (shiftBM B ε u ω)) := by
    convert seed_alive_shift_measurable (g := fun ω u => f ω u (driftDriver σ B D ω u)) h.le hmf u using 1
    funext ω
    by_cases hs : u ≤ S ω - ε
    · simp only [indicator_of_mem (show ω ∈ {ω | u ≤ S ω - ε} from hs)]
      exact seedRestartLog_at_driver f σ B D ε u ω
    · simp only [indicator_of_notMem (show ω ∉ {ω | u ≤ S ω - ε} from hs)]
  have hmR₁ (u : ℝ≥0) : Measurable[LP.LP4HB.shiftFiltration 𝓕 ε u]
      ({ω | u ≤ S ω - ε}.indicator fun ω =>
        seedRestartDeriv 1 ℓx σ B D ε u ω (shiftBM B ε u ω)) := by
    convert (hmR ℓx hm₁ u).const_mul σ using 1
    funext ω
    by_cases hs : u ≤ S ω - ε <;>
      simp only [seedRestartDeriv, seedRestartLog, pow_one, indicator, mem_ofPred_eq,
        hs, ite_true, ite_false, mul_zero]
  have hmR₂ (u : ℝ≥0) : Measurable[LP.LP4HB.shiftFiltration 𝓕 ε u]
      ({ω | u ≤ S ω - ε}.indicator fun ω =>
        seedRestartDeriv 2 ℓxx σ B D ε u ω (shiftBM B ε u ω)) := by
    convert (hmR ℓxx hm₂ u).const_mul (σ ^ 2) using 1
    funext ω
    by_cases hs : u ≤ S ω - ε <;>
      simp only [seedRestartDeriv, seedRestartLog, indicator, mem_ofPred_eq,
        hs, ite_true, ite_false, mul_zero]
  have hmRG (u : ℝ≥0) : Measurable[LP.LP4HB.shiftFiltration 𝓕 ε u]
      ({ω | u ≤ S ω - ε}.indicator fun ω =>
        Ito.fieldGen (seedRestartDeriv 2 ℓxx σ B D ε)
          (seedRestartTime ℓx ℓt b σ B D ε) (shiftBM B ε) u ω) := by
    convert seed_alive_shift_measurable h.le hmG u using 1
    funext ω
    by_cases hs : u ≤ S ω - ε
    · simp only [indicator_of_mem (show ω ∈ {ω | u ≤ S ω - ε} from hs)]
      exact seedRestart_generator_eq ℓx ℓxx ℓt b σ B D ε ω u.coe_nonneg
    · simp only [indicator_of_notMem (show ω ∉ {ω | u ≤ S ω - ε} from hs)]
  filter_upwards [h.seed_original_stochIntegral hB hBc hσ hρ hS (hmR ℓ hm₀) hmR₁ hmR₂ hmRG t]
    with ω hω
  rw [seed_compensated_field_band_eq ℓ ℓx ℓxx ℓt b σ B D ε S hεt ω (h.le ω)] at hω
  have h0 : seedEndProcess ε (Ito.fieldStopped (seedRestartLog ℓ σ B D ε)
      (seedRestartDeriv 2 ℓxx σ B D ε) (seedRestartTime ℓx ℓt b σ B D ε)
      (shiftBM B ε) (fun ω => S ω - ε) 0) 0 ω = ℓ ω ε (driftDriver σ B D ω ε) := by
    simp only [seedEndProcess, zero_tsub, Ito.fieldStopped, zero_min,
      NNReal.coe_zero, intervalIntegral.integral_same, sub_zero]
    simpa only [NNReal.coe_zero, add_zero] using seedRestartLog_at_driver ℓ σ B D ε 0 ω
  rw [h0] at hω
  linarith only [hω]

end InteractingSLE.ZhanGT4
