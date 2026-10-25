import SupercriticalLQGUniqueness.B2.DG20Lim.FiniteLFPPAffine

 

set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal
open LQGMetric LQGMetric.LFPP LQGMetric.Blueprint

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem normalizedContLFPP_one (ξ : ℝ) (φ : C(ℂ, ℝ)) :
    normalizedContLFPP ξ ⟨1, by norm_num⟩ φ =
      lfppContMetric ξ φ φ.continuous := by
  apply Subtype.ext
  ext p
  simp [normalizedContLFPP, ContMetric.smulPos_apply]

theorem lfpp_bad_ratio_iff_normalized
    (ξ : ℝ) (a : Ioi (0 : ℝ)) (φ : C(ℂ, ℝ))
    (A E F : Set ℂ) (C : ℝ≥0∞) :
    C * setDist (normalizedContLFPP ξ a φ) E F <
      (normalizedContLFPP ξ a φ).aroundDist A E F ↔
    C * setDist (lfppContMetric ξ φ φ.continuous) E F <
      (lfppContMetric ξ φ φ.continuous).aroundDist A E F := by
  have h := normalizedContLFPP_good_iff_affine ξ
    (⟨1, by norm_num⟩ : Ioi (0 : ℝ)) a
    (φ := φ) (φ' := φ) (b := 0) (c := 1) (by norm_num)
    0 (by intro x; simp) (Homeomorph.refl ℂ) (by intro x; simp)
    A E F C
  simpa only [Homeomorph.refl_apply, image_id,
    normalizedContLFPP_one] using h

end SupercriticalLQGUniqueness.B2.DG20Lim
