/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.ZhanGT4.ItoField
import InteractingSLE.Spec.ZhanGT4.DualSeedLawModulus

/-!
# Taylor localization for the logarithmic field

Packet PROVE-ZHAN-GT4-A22. The existing cutoff is exponential. Here the
same smooth bump localizes the logarithm itself, with its actual first
and second derivatives. This is a deterministic localization on each
regular space-time piece supplied by A21.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory

namespace InteractingSLE.ZhanGT4

/-- The localized logarithm. -/
def seedLogCut (ℓ : ℝ → ℝ → ℝ) (y ρ t x : ℝ) : ℝ := cutChi 0 y ρ x * ℓ t x

/-- Its first space derivative. -/
def seedLogCut1 (ℓ ℓx : ℝ → ℝ → ℝ) (y ρ t x : ℝ) : ℝ :=
  cutChi 1 y ρ x * ℓ t x + cutChi 0 y ρ x * ℓx t x

/-- Its second space derivative. -/
def seedLogCut2 (ℓ ℓx ℓxx : ℝ → ℝ → ℝ) (y ρ t x : ℝ) : ℝ :=
  cutChi 2 y ρ x * ℓ t x + 2 * cutChi 1 y ρ x * ℓx t x + cutChi 0 y ρ x * ℓxx t x

/-- Its third space derivative. -/
def seedLogCut3 (ℓ ℓx ℓxx ℓxxx : ℝ → ℝ → ℝ) (y ρ t x : ℝ) : ℝ :=
  cutChi 3 y ρ x * ℓ t x + 3 * cutChi 2 y ρ x * ℓx t x +
    3 * cutChi 1 y ρ x * ℓxx t x + cutChi 0 y ρ x * ℓxxx t x

/-- Its time derivative. -/
def seedLogCutT (ℓt : ℝ → ℝ → ℝ) (y ρ t x : ℝ) : ℝ := cutChi 0 y ρ x * ℓt t x

namespace IsLogField

variable {ℓ ℓx ℓxx ℓxxx ℓt : ℝ → ℝ → ℝ} {b c y ρ K : ℝ}
  (h : IsLogField ℓ ℓx ℓxx ℓxxx ℓt b c y ρ K)

include h

/-- The localized logarithm has the prescribed first derivative everywhere. -/
theorem hasDerivAt_seedLogCut {t : ℝ} (ht : t ∈ Icc b c) (x : ℝ) :
    HasDerivAt (seedLogCut ℓ y ρ t) (seedLogCut1 ℓ ℓx y ρ t x) x := by
  by_cases hx : |x - y| < 3 * ρ
  · exact (hasDerivAt_cutChi 0 y ρ x).mul (h.dx t ht x hx)
  · have hf := far_of_not_near h.pos hx
    have hz : seedLogCut1 ℓ ℓx y ρ t x = 0 := by
      simp [seedLogCut1, cutChi_eq_zero_of_lt h.pos hf]
    rw [hz]
    refine (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [eventually_far hf] with z hz
    simp [seedLogCut, cutChi_eq_zero_of_lt h.pos hz]

/-- The prescribed second derivative is also valid off the regular tube. -/
theorem hasDerivAt_seedLogCut1 {t : ℝ} (ht : t ∈ Icc b c) (x : ℝ) :
    HasDerivAt (seedLogCut1 ℓ ℓx y ρ t) (seedLogCut2 ℓ ℓx ℓxx y ρ t x) x := by
  by_cases hx : |x - y| < 3 * ρ
  · have hd := ((hasDerivAt_cutChi 1 y ρ x).mul (h.dx t ht x hx)).add
      ((hasDerivAt_cutChi 0 y ρ x).mul (h.dxx t ht x hx))
    exact hd.congr_deriv (by dsimp [seedLogCut2]; ring)
  · have hf := far_of_not_near h.pos hx
    have hz : seedLogCut2 ℓ ℓx ℓxx y ρ t x = 0 := by
      simp [seedLogCut2, cutChi_eq_zero_of_lt h.pos hf]
    rw [hz]
    refine (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [eventually_far hf] with z hz
    simp [seedLogCut1, cutChi_eq_zero_of_lt h.pos hz]

/-- The third derivative controls the second-order Taylor remainder. -/
theorem hasDerivAt_seedLogCut2 {t : ℝ} (ht : t ∈ Icc b c) (x : ℝ) :
    HasDerivAt (seedLogCut2 ℓ ℓx ℓxx y ρ t) (seedLogCut3 ℓ ℓx ℓxx ℓxxx y ρ t x) x := by
  by_cases hx : |x - y| < 3 * ρ
  · have hd := (((hasDerivAt_cutChi 2 y ρ x).mul (h.dx t ht x hx)).add
      (((hasDerivAt_cutChi 1 y ρ x).const_mul 2).mul (h.dxx t ht x hx))).add
        ((hasDerivAt_cutChi 0 y ρ x).mul (h.dxxx t ht x hx))
    exact hd.congr_deriv (by dsimp [seedLogCut3]; ring)
  · have hf := far_of_not_near h.pos hx
    have hz : seedLogCut3 ℓ ℓx ℓxx ℓxxx y ρ t x = 0 := by
      simp [seedLogCut3, cutChi_eq_zero_of_lt h.pos hf]
    rw [hz]
    refine (hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq ?_
    filter_upwards [eventually_far hf] with z hz
    simp [seedLogCut2, cutChi_eq_zero_of_lt h.pos hz]

/-- An explicit global third-derivative bound. -/
theorem abs_seedLogCut3_le {Cχ : ℝ} (hC : 0 ≤ Cχ)
    (hχ : ∀ k ≤ 4, ∀ x, |cutChi k y ρ x| ≤ Cχ) {t : ℝ} (ht : t ∈ Icc b c) (x : ℝ) :
    |seedLogCut3 ℓ ℓx ℓxx ℓxxx y ρ t x| ≤ 8 * Cχ * K := by
  by_cases hx : |x - y| < 3 * ρ
  · obtain ⟨h0, h1, h2, h3, _⟩ := h.bound t ht x hx
    have h03 := abs_mul_le_of_le (hχ 3 (by norm_num) x) h0
    have h12 := abs_mul_le_of_le (hχ 2 (by norm_num) x) h1
    have h21 := abs_mul_le_of_le (hχ 1 (by norm_num) x) h2
    have h30 := abs_mul_le_of_le (hχ 0 (by norm_num) x) h3
    calc
      _ ≤ |cutChi 3 y ρ x * ℓ t x| + 3 * |cutChi 2 y ρ x * ℓx t x| +
          3 * |cutChi 1 y ρ x * ℓxx t x| + |cutChi 0 y ρ x * ℓxxx t x| := by
        have h1 := abs_add_le (cutChi 3 y ρ x * ℓ t x) (3 * cutChi 2 y ρ x * ℓx t x)
        have h2 := (abs_add_le
          (cutChi 3 y ρ x * ℓ t x + 3 * cutChi 2 y ρ x * ℓx t x)
          (3 * cutChi 1 y ρ x * ℓxx t x)).trans (add_le_add h1 le_rfl)
        have h3 := (abs_add_le
          (cutChi 3 y ρ x * ℓ t x + 3 * cutChi 2 y ρ x * ℓx t x +
            3 * cutChi 1 y ρ x * ℓxx t x) (cutChi 0 y ρ x * ℓxxx t x)).trans
              (add_le_add h2 le_rfl)
        simpa only [seedLogCut3, mul_assoc, abs_mul,
          abs_of_pos (by norm_num : (0 : ℝ) < 3)] using h3
      _ ≤ _ := by linarith
  · simp only [seedLogCut3, cutChi_eq_zero_of_lt h.pos (far_of_not_near h.pos hx),
      zero_mul, mul_zero, add_zero, abs_zero]
    have hK := h.Knonneg
    positivity

/-- The second derivative is globally Lipschitz after localization. -/
theorem lipschitz_seedLogCut2 {Cχ : ℝ} (hC : 0 ≤ Cχ)
    (hχ : ∀ k ≤ 4, ∀ x, |cutChi k y ρ x| ≤ Cχ) {t : ℝ} (ht : t ∈ Icc b c) (x z : ℝ) :
    |seedLogCut2 ℓ ℓx ℓxx y ρ t x - seedLogCut2 ℓ ℓx ℓxx y ρ t z| ≤
      (8 * Cχ * K) * |x - z| := by
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (𝕜 := ℝ) (s := univ)
    (f := seedLogCut2 ℓ ℓx ℓxx y ρ t) (f' := seedLogCut3 ℓ ℓx ℓxx ℓxxx y ρ t)
    (fun x _ => (h.hasDerivAt_seedLogCut2 ht x).hasDerivWithinAt)
    (fun x _ => by rw [Real.norm_eq_abs]; exact h.abs_seedLogCut3_le hC hχ ht x)
    convex_univ (mem_univ z) (mem_univ x)
  simpa only [Real.norm_eq_abs] using hh

/-- Joint continuity of the localized time derivative. -/
theorem continuousOn_seedLogCutT :
    ContinuousOn (fun p : ℝ × ℝ => seedLogCutT ℓt y ρ p.1 p.2) (Icc b c ×ˢ univ) := by
  refine continuousOn_of_near_far (y := y) h.pos ?_ fun p hp => by
    simp [seedLogCutT, cutChi_eq_zero_of_lt h.pos hp]
  exact ((continuous_cutChi 0 y ρ).comp continuous_snd).continuousOn.mul h.contT

/-- Joint continuity of the localized second derivative. -/
theorem continuousOn_seedLogCut2 :
    ContinuousOn (fun p : ℝ × ℝ => seedLogCut2 ℓ ℓx ℓxx y ρ p.1 p.2) (Icc b c ×ˢ univ) := by
  refine continuousOn_of_near_far (y := y) h.pos ?_ fun p hp => by
    simp [seedLogCut2, cutChi_eq_zero_of_lt h.pos hp]
  have hc (k : ℕ) := ((continuous_cutChi k y ρ).comp continuous_snd).continuousOn
    (s := Icc b c ×ˢ {x | |x - y| < 3 * ρ})
  exact ((hc 2).mul h.cont |>.add ((continuousOn_const.mul (hc 1)).mul h.contX)).add
    ((hc 0).mul h.contXX)

/-- The localized time increments are the integral of the localized time derivative. -/
theorem seedLogCut_sub_eq_integral (x : ℝ) {a₁ a₂ : ℝ}
    (h₁ : b ≤ a₁) (h₁₂ : a₁ ≤ a₂) (h₂ : a₂ ≤ c) :
    seedLogCut ℓ y ρ a₂ x - seedLogCut ℓ y ρ a₁ x =
      ∫ u in a₁..a₂, seedLogCutT ℓt y ρ u x := by
  by_cases hx : |x - y| < 3 * ρ
  · have hsub : Icc a₁ a₂ ⊆ Icc b c := Icc_subset_Icc h₁ h₂
    have hd (u : ℝ) (hu : u ∈ Icc b c) :
        HasDerivWithinAt (fun s => seedLogCut ℓ y ρ s x) (seedLogCutT ℓt y ρ u x) (Icc b c) u :=
      (h.dt u hu x hx).const_mul (cutChi 0 y ρ x)
    have hc : ContinuousOn (fun u => ℓt u x) (Icc a₁ a₂) :=
      h.contT.comp ((continuous_id.prodMk continuous_const).continuousOn)
        (fun u hu => ⟨hsub hu, hx⟩)
    have hcont : ContinuousOn (fun u => seedLogCutT ℓt y ρ u x) (Icc a₁ a₂) :=
      continuousOn_const.mul hc
    symm
    apply intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le h₁₂
      (fun u hu => (hd u (hsub hu)).continuousWithinAt.mono hsub) (fun u hu => ?_)
      (hcont.intervalIntegrable_of_Icc h₁₂)
    exact (hd u (hsub (Ioo_subset_Icc_self hu))).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGT_of_mem ⟨h₁.trans hu.1.le, lt_of_lt_of_le hu.2 h₂⟩)
  · simp [seedLogCut, seedLogCutT, cutChi_eq_zero_of_lt h.pos (far_of_not_near h.pos hx)]

end IsLogField

end InteractingSLE.ZhanGT4
