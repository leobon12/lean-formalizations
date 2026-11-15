/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedFin2Fields

/-!
# Original adapted coefficients of the actual seed bands

Packet PROVE-ZHAN-GT4-A22. Export the adaptedness, Riemann regularity and
uniform bound already obtained from the actual alive first derivative.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal

namespace InteractingSLE.ZhanGT4

open Girsanov LP.LP4HB

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The concrete original band coefficient has all integral-limit facts. -/
theorem IsDriftLogField.seed_original_coef_facts
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ} {σ ρ K : ℝ}
    {B D : ℝ≥0 → Ω → ℝ} {b : Ω → ℝ → ℝ} {ε : ℝ≥0} {S : Ω → ℝ≥0}
    {ℓ ℓx ℓxx ℓxxx ℓt : Ω → ℝ → ℝ → ℝ}
    (h : IsDriftLogField 𝓕 σ ρ K B D b ε S ℓ ℓx ℓxx ℓxxx ℓt)
    (hBc : ∀ ω, Continuous (B · ω))
    (hσ : 0 < σ) (hρ : 0 < ρ)
    (hS : IsStoppingTime 𝓕 fun ω => (S ω : WithTop ℝ≥0)) :
    let w := seedEndCoef ε (Ito.stopCoef (seedRestartDeriv 1 ℓx σ B D ε)
      (shiftBM B ε) (fun ω => S ω - ε))
    StronglyAdapted 𝓕 w ∧ IsRiemannRegular P w ∧
      ∃ C : ℝ, 0 ≤ C ∧ ∀ u ω, |w u ω| ≤ C := by
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
  have hb := h.seed_restarted_band hBc hσ hρ
  have hf := hb.coef_facts (P := P) hBc' hS' hm₁
  refine ⟨seedEndCoef_adapted hf.1, seedEndCoef_isRiemannRegular hf.2,
    (1 + σ + σ ^ 2 + σ ^ 3) * (K + K * K), hb.bound_nonneg, ?_⟩
  exact abs_seedEndCoef_le hb.bound_nonneg (fun u ω => (hb.coef_bound ω u).1) ε

end InteractingSLE.ZhanGT4
