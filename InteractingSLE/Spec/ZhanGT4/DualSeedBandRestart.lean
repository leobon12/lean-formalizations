/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedBandStochastic

/-!
# Stochastic logarithmic calculus for the actual restarted seed band

Packet PROVE-ZHAN-GT4-A22. The drifted field supplies the local Taylor
steps, the full pasting, adapted coefficients and the generator identity.
This theorem uses the restarted Brownian filtration explicitly.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

open Girsanov LP.LP4HB

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Sampling the restarted field gives the original logarithm after `ε`. -/
theorem seedRestartLog_at_driver (ℓ : Ω → ℝ → ℝ → ℝ) (σ : ℝ)
    (B D : ℝ≥0 → Ω → ℝ) (ε u : ℝ≥0) (ω : Ω) :
    seedRestartLog ℓ σ B D ε u ω (shiftBM B ε u ω) =
      ℓ ω (ε + u) (driftDriver σ B D ω (ε + u)) := by
  unfold seedRestartLog shiftField
  rw [shiftBM_add_shiftOff' σ B D ε ω u]
  rfl

/-- The actual positive-time seeded field has its stochastic integral
formula in the restarted filtration. No Taylor-control premise remains. -/
theorem IsDriftLogField.seed_restarted_stochIntegral
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {σ ρ K : ℝ}
    {B D : ℝ≥0 → Ω → ℝ} {b : Ω → ℝ → ℝ} {ε : ℝ≥0} {S : Ω → ℝ≥0}
    {ℓ ℓx ℓxx ℓxxx ℓt : Ω → ℝ → ℝ → ℝ}
    (h : IsDriftLogField 𝓕 σ ρ K B D b ε S ℓ ℓx ℓxx ℓxxx ℓt)
    (hB : IsFilteredBrownianReal 𝓕 B P) (hBc : ∀ ω, Continuous (B · ω))
    (hσ : 0 < σ) (hρ : 0 < ρ)
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) (t : ℝ≥0) :
    let B' := shiftBM B ε
    let S' := fun ω => S ω - ε
    let Φ := seedRestartLog ℓ σ B D ε
    let Φ₁ := seedRestartDeriv 1 ℓx σ B D ε
    let Φ₂ := seedRestartDeriv 2 ℓxx σ B D ε
    let Ψ := seedRestartTime ℓx ℓt b σ B D ε
    (fun ω => Ito.fieldStopped Φ Φ₂ Ψ B' S' 0 t ω -
      Ito.fieldStopped Φ Φ₂ Ψ B' S' 0 0 ω) =ᵐ[P]
      fun ω => stochIntegral P (shiftFiltration 𝓕 ε) B' (Ito.stopCoef Φ₁ B' S') t ω -
        stochIntegral P (shiftFiltration 𝓕 ε) B' (Ito.stopCoef Φ₁ B' S') 0 ω := by
  dsimp only
  have hB' := isFilteredBrownianReal_shift hB ε
  have hBc' : ∀ ω, Continuous (shiftBM B ε · ω) := fun ω =>
    ((hBc ω).comp (continuous_const.add continuous_id)).sub continuous_const
  have hS' : IsStoppingTime (shiftFiltration 𝓕 ε)
      (fun ω => ((S ω - ε : ℝ≥0) : WithTop ℝ≥0)) := by
    intro u
    have he : {ω | ((S ω - ε : ℝ≥0) : WithTop ℝ≥0) ≤ u} =
        {ω | (S ω : WithTop ℝ≥0) ≤ ((ε + u : ℝ≥0) : WithTop ℝ≥0)} := by
      ext ω
      simp only [mem_ofPred_eq, WithTop.coe_le_coe, tsub_le_iff_left]
    rw [he]
    exact hS (ε + u)
  have hd := h.isDriverLogField_shift hBc hρ
  have hm₁ (u : ℝ≥0) : Measurable[shiftFiltration 𝓕 ε u]
      ({ω | u ≤ S ω - ε}.indicator fun ω =>
        seedRestartDeriv 1 ℓx σ B D ε u ω (shiftBM B ε u ω)) := by
    convert (hd.meas1 u).const_mul σ using 1
    funext ω
    by_cases hs : u ≤ S ω - ε <;>
      simp only [seedRestartDeriv, pow_one, indicator, mem_ofPred_eq, hs, ite_true, ite_false, mul_zero]
  have hm₂ (u : ℝ≥0) : Measurable[shiftFiltration 𝓕 ε u]
      ({ω | u ≤ S ω - ε}.indicator fun ω =>
        seedRestartDeriv 2 ℓxx σ B D ε u ω (shiftBM B ε u ω)) := by
    convert (hd.meas2 u).const_mul (σ ^ 2) using 1
    funext ω
    by_cases hs : u ≤ S ω - ε <;>
      simp only [seedRestartDeriv, indicator, mem_ofPred_eq, hs, ite_true, ite_false, mul_zero]
  have hmG (u : ℝ≥0) : Measurable[shiftFiltration 𝓕 ε u]
      ({ω | u ≤ S ω - ε}.indicator fun ω =>
        Ito.fieldGen (seedRestartDeriv 2 ℓxx σ B D ε)
          (seedRestartTime ℓx ℓt b σ B D ε) (shiftBM B ε) u ω) := by
    convert ((hd.meas1 u).pow_const 2).const_mul (-(σ ^ 2 / 2)) using 1
    funext ω
    by_cases hs : u ≤ S ω - ε
    · simp only [indicator_of_mem (show ω ∈ {ω | u ≤ S ω - ε} from hs),
        Ito.fieldGen, seedRestartDeriv, seedRestartTime, Real.toNNReal_coe]
      have hh := hd.gen ω u u.coe_nonneg (show (u : ℝ) ≤ (S ω - ε : ℝ≥0) from hs)
      simp only [Real.toNNReal_coe] at hh
      linarith only [hh]
    · simp only [indicator_of_notMem (show ω ∉ {ω | u ≤ S ω - ε} from hs),
        zero_pow (by norm_num : 2 ≠ 0), mul_zero]
  exact (h.seed_restarted_band hBc hσ hρ).stochIntegral hB' hBc' hS'
    hd.meas0 hm₁ hm₂ hmG t

end InteractingSLE.ZhanGT4
