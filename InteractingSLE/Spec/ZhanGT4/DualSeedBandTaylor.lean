/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedBandTube

/-!
# Actual logarithmic cell errors on the moving tube

Packet PROVE-ZHAN-GT4-A22. Remove the fixed spatial cutoff from the
remainder itself. The resulting bound uses the actual time and second
derivative fields, whose simultaneous modulus is supplied by BandTube.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory

namespace InteractingSLE.ZhanGT4

/-- The fixed logarithmic cutoff can be removed from the actual step
remainder when the entire path segment remains in its inner region. -/
theorem seedLogCut_fieldStepRem_eq {ℓ ℓx ℓxx ℓt : ℝ → ℝ → ℝ}
    {β : ℝ → ℝ} {y ρ a b : ℝ} (hρ : 0 < ρ) (hab : a ≤ b)
    (hnear : ∀ u ∈ Icc a b, |β u - y| < ρ) :
    Ito.fieldStepRem (seedLogCutT ℓt y ρ) (seedLogCut2 ℓ ℓx ℓxx y ρ) β a b =
      Ito.fieldStepRem ℓt ℓxx β a b := by
  have hb := hnear b (right_mem_Icc.2 hab)
  have ha := hnear a (left_mem_Icc.2 hab)
  unfold Ito.fieldStepRem
  rw [(seedLogCut_eq_of_near ℓ ℓx ℓxx ℓt hρ ha).2.2.1]
  congr 1
  · apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hab] at hu
    dsimp only
    rw [(seedLogCut_eq_of_near ℓ ℓx ℓxx ℓt hρ hb).2.2.2,
      (seedLogCut_eq_of_near ℓ ℓx ℓxx ℓt hρ (hnear u hu)).2.2.2]
  · congr 1
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le hab] at hu
    dsimp only
    rw [(seedLogCut_eq_of_near ℓ ℓx ℓxx ℓt hρ (hnear u hu)).2.2.1]

/-- The local Taylor bound is expressed entirely in actual fields. -/
theorem IsLogField.seed_log_step_actual
    {ℓ ℓx ℓxx ℓxxx ℓt : ℝ → ℝ → ℝ} {b c y ρ K Cχ : ℝ}
    (h : IsLogField ℓ ℓx ℓxx ℓxxx ℓt b c y ρ K)
    (hC : 0 ≤ Cχ) (hχ : ∀ k ≤ 4, ∀ x, |cutChi k y ρ x| ≤ Cχ)
    {β : ℝ → ℝ} {a z : ℝ} (h₁ : b ≤ a) (haz : a ≤ z) (h₂ : z ≤ c)
    (hβ : ContinuousOn β (Icc a z)) (hnear : ∀ u ∈ Icc a z, |β u - y| < ρ) :
    |ℓ z (β z) - ℓ a (β a) -
        (∫ u in a..z, (ℓt u (β u) + 1 / 2 * ℓxx u (β u))) -
        ℓx a (β a) * (β z - β a) -
        1 / 2 * ℓxx a (β a) * ((β z - β a) ^ 2 - (z - a))| ≤
      (8 * Cχ * K) * |β z - β a| ^ 3 + Ito.fieldStepRem ℓt ℓxx β a z := by
  have hh := h.seed_log_taylor_step hC hχ h₁ haz h₂ hβ hnear
  rwa [seedLogCut_fieldStepRem_eq h.pos haz hnear] at hh

end InteractingSLE.ZhanGT4
