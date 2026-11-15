/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedEndMeas

/-!
# The actual seeded band integral in the original filtration

Packet PROVE-ZHAN-GT4-A22. The drifted field, its generator and its alive
values discharge every analytic and measurable input of the original-grid
integral theorem. No chosen-integral time-shift identity is assumed.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

open Girsanov LP.LP4HB

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- Original-clock stochastic calculus for the actual drifted seed band.
The returned coefficient is zero before the deterministic restart. -/
theorem IsDriftLogField.seed_original_stochIntegral
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
    (fun ω => seedEndProcess ε (Ito.fieldStopped Φ Φ₂ Ψ B' S' 0) t ω -
      seedEndProcess ε (Ito.fieldStopped Φ Φ₂ Ψ B' S' 0) 0 ω) =ᵐ[P]
      fun ω => Girsanov.stochIntegral P 𝓕 B (seedEndCoef ε (Ito.stopCoef Φ₁ B' S')) t ω -
        Girsanov.stochIntegral P 𝓕 B (seedEndCoef ε (Ito.stopCoef Φ₁ B' S')) 0 ω := by
  dsimp only
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
  have hb := h.seed_restarted_band hBc hσ hρ
  have hf := hb.coef_facts (P := P) hBc' hS' hm₁
  have hmX (u : ℝ≥0) := (hb.measurable_stopped hBc' hS' hd.meas0 hmG u).mono
    ((shiftFiltration 𝓕 ε).le u) le_rfl
  have he : cutRate (fun ω => S ω - ε) (fun ω r =>
      seedRestartDeriv 2 ℓxx σ B D ε r ω (shiftBM B ε r.toNNReal ω)) =
        Ito.stopCoef (seedRestartDeriv 2 ℓxx σ B D ε) (shiftBM B ε) (fun ω => S ω - ε) := by
    funext u ω
    simp only [cutRate, Ito.stopCoef, Real.toNNReal_coe]
  have ha₂ : StronglyAdapted (shiftFiltration 𝓕 ε)
      (Ito.stopCoef (seedRestartDeriv 2 ℓxx σ B D ε) (shiftBM B ε) (fun ω => S ω - ε)) := by
    rw [← he]
    intro u
    exact (measurable_cutRate hS' (by
      intro v
      simpa only [Real.toNNReal_coe] using hm₂ v) u).stronglyMeasurable
  exact hb.original_stochIntegral hB hBc hmX hf.1 ha₂ hf.2 t


end InteractingSLE.ZhanGT4
