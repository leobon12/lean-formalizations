/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedBandPasting

/-!
# Stochastic integral identification from actual band pasting

Packet PROVE-ZHAN-GT4-A22. The input is a regular field on a moving tube.
The Taylor estimate and its vanishing remainders are conclusions.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

open Girsanov

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ}
  {Φ Φ₁ Φ₂ Φ₃ Ψ : ℝ → Ω → ℝ → ℝ} {S : Ω → ℝ≥0}

/-- A partition clamped at time zero has zero defect. -/
theorem seedDyadicDefect_zero (X c₁ c₂ B : ℝ≥0 → Ω → ℝ) (n : ℕ) (ω : Ω) :
    seedDyadicDefect X c₁ c₂ B n 0 ω = 0 := by
  simp only [seedDyadicDefect, min_zero, Ito.itoDefect, sub_self, mul_zero,
    zero_pow (by norm_num : 2 ≠ 0), NNReal.coe_zero, Finset.sum_const_zero]

/-- The stopped, compensated field equals its stochastic integral.
All analytic hypotheses describe the actual field near the path; none
asserts an Itô identity or a bound on a Taylor sum. -/
theorem seed_stochIntegral_eq_of_band_field
    (hB : IsFilteredBrownianReal 𝓕 B P) (hBc : ∀ ω, Continuous (B · ω))
    (hX : ∀ u, Measurable (Ito.fieldStopped Φ Φ₂ Ψ B S 0 u))
    (hXc : ∀ ω, Continuous (Ito.fieldStopped Φ Φ₂ Ψ B S 0 · ω))
    (had₁ : StronglyAdapted 𝓕 (Ito.stopCoef Φ₁ B S))
    (had₂ : StronglyAdapted 𝓕 (Ito.stopCoef Φ₂ B S))
    {C₁ : ℝ} (hb₁ : ∀ u ω, |Ito.stopCoef Φ₁ B S u ω| ≤ C₁)
    (hr : IsRiemannRegular P (Ito.stopCoef Φ₁ B S))
    (hfield : ∀ ω, ∃ ρ K : ℝ, 0 < ρ ∧ 0 ≤ K ∧
      (∀ a b y : ℝ, 0 ≤ a → a ≤ b → b ≤ S ω →
        (∀ u ∈ Icc a b, |B u.toNNReal ω - y| < ρ) →
        IsLogField (fun u x => Φ u ω x) (fun u x => Φ₁ u ω x)
          (fun u x => Φ₂ u ω x) (fun u x => Φ₃ u ω x) (fun u x => Ψ u ω x) a b y ρ K) ∧
      ContinuousOn (fun p : ℝ × ℝ => Ψ p.1 ω p.2)
        (seedPathTube (fun u => B u.toNNReal ω) 0 (S ω) (3 * ρ)) ∧
      ContinuousOn (fun p : ℝ × ℝ => Φ₂ p.1 ω p.2)
        (seedPathTube (fun u => B u.toNNReal ω) 0 (S ω) (3 * ρ)) ∧
      (∀ u, |Ito.stopCoef Φ₁ B S u ω| ≤ K) ∧
      (∀ u, |Ito.stopCoef Φ₂ B S u ω| ≤ K)) (t : ℝ≥0) :
    (fun ω => Ito.fieldStopped Φ Φ₂ Ψ B S 0 t ω -
      Ito.fieldStopped Φ Φ₂ Ψ B S 0 0 ω) =ᵐ[P]
      fun ω => stochIntegral P 𝓕 B (Ito.stopCoef Φ₁ B S) t ω -
        stochIntegral P 𝓕 B (Ito.stopCoef Φ₁ B S) 0 ω := by
  apply seed_stochIntegral_sub_eq_of_local_taylor (ε := 0) hB hX had₁ hb₁ hr had₂ bot_le
  · apply Eventually.of_forall
    intro ω
    obtain ⟨ρ, K, -, -, -, -, -, -, h₂⟩ := hfield ω
    exact ⟨K, fun u _ => h₂ u⟩
  · apply Eventually.of_forall
    intro ω
    obtain ⟨ρ, K, hρ, hK, hl, hΨ, hΦ, h₁, h₂⟩ := hfield ω
    simpa only [seedDyadicDefect_zero, sub_zero] using
      seed_stopped_field_taylor_bound t ω hρ hK (hBc ω) (hXc ω) hl hΨ hΦ
        (fun u _ => h₁ u) (fun u _ => h₂ u)

end InteractingSLE.ZhanGT4
