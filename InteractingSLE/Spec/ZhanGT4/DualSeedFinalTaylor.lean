/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.DualSeedFinalCut
import InteractingSLE.Spec.ZhanGT4.DualSeedDrift

/-!
# The actual localized logarithmic Taylor step

Packet PROVE-ZHAN-GT4-A22. Apply the checked random-field Taylor theorem
to the localized logarithm and remove the cutoff along the path. A21's
shifted drifted seed fields supply precisely `IsLogField` on these pieces.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory
open scoped NNReal ENNReal

namespace InteractingSLE.ZhanGT4

/-- The cutoff and its first two derivatives agree with the actual log
field throughout the inner tube. -/
theorem seedLogCut_eq_of_near (ℓ ℓx ℓxx ℓt : ℝ → ℝ → ℝ) {y ρ t x : ℝ}
    (hρ : 0 < ρ) (hx : |x - y| < ρ) :
    seedLogCut ℓ y ρ t x = ℓ t x ∧ seedLogCut1 ℓ ℓx y ρ t x = ℓx t x ∧
      seedLogCut2 ℓ ℓx ℓxx y ρ t x = ℓxx t x ∧ seedLogCutT ℓt y ρ t x = ℓt t x := by
  simp only [seedLogCut, seedLogCut1, seedLogCut2, seedLogCutT,
    cutChi_zero_eq_one hρ hx, cutChi_succ_eq_zero hρ hx (by norm_num : 0 < 1),
    cutChi_succ_eq_zero hρ hx (by norm_num : 0 < 2), zero_mul, one_mul, mul_zero,
    zero_add, and_self]

namespace IsLogField

variable {ℓ ℓx ℓxx ℓxxx ℓt : ℝ → ℝ → ℝ} {b c y ρ K : ℝ}
  (h : IsLogField ℓ ℓx ℓxx ℓxxx ℓt b c y ρ K)

include h

/-- The finite Taylor step for the original logarithm, with explicit cubic
constant and the localized time modulus. No stochastic identity is assumed. -/
theorem seed_log_taylor_step {Cχ : ℝ} (hC : 0 ≤ Cχ)
    (hχ : ∀ k ≤ 4, ∀ x, |cutChi k y ρ x| ≤ Cχ)
    {β : ℝ → ℝ} {a₁ a₂ : ℝ} (h₁ : b ≤ a₁) (h₁₂ : a₁ ≤ a₂) (h₂ : a₂ ≤ c)
    (hβ : ContinuousOn β (Icc a₁ a₂)) (hnear : ∀ u ∈ Icc a₁ a₂, |β u - y| < ρ) :
    |ℓ a₂ (β a₂) - ℓ a₁ (β a₁) -
        (∫ u in a₁..a₂, (ℓt u (β u) + 1 / 2 * ℓxx u (β u))) -
        ℓx a₁ (β a₁) * (β a₂ - β a₁) -
        1 / 2 * ℓxx a₁ (β a₁) * ((β a₂ - β a₁) ^ 2 - (a₂ - a₁))| ≤
      (8 * Cχ * K) * |β a₂ - β a₁| ^ 3 +
        Ito.fieldStepRem (seedLogCutT ℓt y ρ) (seedLogCut2 ℓ ℓx ℓxx y ρ) β a₁ a₂ := by
  have hsub : Icc a₁ a₂ ⊆ Icc b c := Icc_subset_Icc h₁ h₂
  have ha₁ := left_mem_Icc.2 h₁₂
  have ha₂ := right_mem_Icc.2 h₁₂
  have hstep := Ito.field_pathwise_step h₁₂
    (h.hasDerivAt_seedLogCut (hsub ha₁)) (h.hasDerivAt_seedLogCut1 (hsub ha₁))
    (h.lipschitz_seedLogCut2 hC hχ (hsub ha₁)) (h.seedLogCut_sub_eq_integral (β a₂) h₁ h₁₂ h₂)
    (h.continuousOn_seedLogCutT.mono (prod_mono hsub le_rfl))
    (h.continuousOn_seedLogCut2.mono (prod_mono hsub le_rfl)) hβ
  have he (u : ℝ) (hu : u ∈ Icc a₁ a₂) := seedLogCut_eq_of_near ℓ ℓx ℓxx ℓt (t := u) h.pos (hnear u hu)
  have hi : (∫ u in a₁..a₂, (seedLogCutT ℓt y ρ u (β u) +
        1 / 2 * seedLogCut2 ℓ ℓx ℓxx y ρ u (β u))) =
      ∫ u in a₁..a₂, (ℓt u (β u) + 1 / 2 * ℓxx u (β u)) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [uIcc_of_le h₁₂] at hu
    dsimp only
    rw [(he u hu).2.2.2, (he u hu).2.2.1]
  rw [(he a₂ ha₂).1, (he a₁ ha₁).1, (he a₁ ha₁).2.1, (he a₁ ha₁).2.2.1, hi] at hstep
  exact hstep

/-- The time modulus produced by the actual logarithmic cutoff vanishes
on every continuous path. -/
theorem seed_log_modulus_tendsto {t : ℝ≥0} (hb : b = 0) (hc : c = t)
    {β : ℝ → ℝ} (hβ : ContinuousOn β (Icc 0 (t : ℝ))) :
    Tendsto (fun n => seedFieldRemainder (seedLogCutT ℓt y ρ)
      (seedLogCut2 ℓ ℓx ℓxx y ρ) β n t) atTop (𝓝 0) := by
  subst b
  subst c
  exact tendsto_seedFieldRemainder t h.continuousOn_seedLogCutT h.continuousOn_seedLogCut2 hβ

end IsLogField

end InteractingSLE.ZhanGT4
