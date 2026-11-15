/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedEndAdapted

/-!
# The original-clock stochastic integral of a restarted band

Packet PROVE-ZHAN-GT4-A22. Apply the actual original-grid Taylor estimate.
No identity between chosen stochastic integrals in different filtrations
is an input.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

open Girsanov LP.LP4HB

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
  {𝓕 : Filtration ℝ≥0 mΩ} {B : ℝ≥0 → Ω → ℝ} {ε : ℝ≥0} {τ : Ω → ℝ≥0}
  {Φ Φ₁ Φ₂ Φ₃ Ψ : ℝ → Ω → ℝ → ℝ} {ρ K : ℝ}

/-- Original-clock Itô identity for the actual compensated band field. -/
theorem SeedRegularBand.original_stochIntegral
    (h : SeedRegularBand (shiftBM B ε) τ Φ Φ₁ Φ₂ Φ₃ Ψ ρ K)
    (hB : IsFilteredBrownianReal 𝓕 B P) (hBc : ∀ ω, Continuous (B · ω))
    (hX : ∀ u, Measurable (Ito.fieldStopped Φ Φ₂ Ψ (shiftBM B ε) τ 0 u))
    (h₁ : StronglyAdapted (shiftFiltration 𝓕 ε) (Ito.stopCoef Φ₁ (shiftBM B ε) τ))
    (h₂ : StronglyAdapted (shiftFiltration 𝓕 ε) (Ito.stopCoef Φ₂ (shiftBM B ε) τ))
    (hr : IsRiemannRegular P (Ito.stopCoef Φ₁ (shiftBM B ε) τ)) (t : ℝ≥0) :
    (fun ω => seedEndProcess ε (Ito.fieldStopped Φ Φ₂ Ψ (shiftBM B ε) τ 0) t ω -
      seedEndProcess ε (Ito.fieldStopped Φ Φ₂ Ψ (shiftBM B ε) τ 0) 0 ω) =ᵐ[P]
      fun ω => Girsanov.stochIntegral P 𝓕 B (seedEndCoef ε (Ito.stopCoef Φ₁ (shiftBM B ε) τ)) t ω -
        Girsanov.stochIntegral P 𝓕 B (seedEndCoef ε (Ito.stopCoef Φ₁ (shiftBM B ε) τ)) 0 ω := by
  apply seed_stochIntegral_sub_eq_of_local_taylor (ε := 0)
    (X := seedEndProcess ε (Ito.fieldStopped Φ Φ₂ Ψ (shiftBM B ε) τ 0)) hB (fun u => hX (u - ε))
    (seedEndCoef_adapted h₁) (C₁ := K)
    (abs_seedEndCoef_le h.bound_nonneg (fun u ω => (h.coef_bound ω u).1) ε)
    (seedEndCoef_isRiemannRegular hr) (seedEndCoef_adapted h₂) bot_le
  · exact Eventually.of_forall fun ω => ⟨K, fun u _ =>
      abs_seedEndCoef_le h.bound_nonneg (fun u ω => (h.coef_bound ω u).2) ε u ω⟩
  · apply Eventually.of_forall
    intro ω
    simpa only [seedDyadicDefect_zero, sub_zero] using h.original_taylor_bound hBc t ω

end InteractingSLE.ZhanGT4
