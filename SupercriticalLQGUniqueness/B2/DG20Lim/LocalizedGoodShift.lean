import SupercriticalLQGUniqueness.B2.DG20Lim.LocalizedGoodProbability
import SupercriticalLQGUniqueness.B2.DG20Lim.LocalizedConstShift

 

set_option autoImplicit false
noncomputable section

open Set
open scoped ENNReal
open LQGMetric LQGMetric.LFPP LQGMetric.Blueprint

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem localized_bad_ratio_iff_addConst
    (ξ ε : ℝ) (hε : 0 < ε) (g : DistC) (c : ℝ)
    (A E F : Set ℂ) (C : ℝ≥0∞) :
    C * setDist (lfppContMetric ξ
        (LQGMetric.DFGPS.L217.locMollifyC ε hε (addConst g c))
        (LQGMetric.DFGPS.L217.locMollifyC ε hε (addConst g c)).continuous) E F <
      (lfppContMetric ξ
        (LQGMetric.DFGPS.L217.locMollifyC ε hε (addConst g c))
        (LQGMetric.DFGPS.L217.locMollifyC ε hε (addConst g c)).continuous).aroundDist A E F ↔
    C * setDist (lfppContMetric ξ
        (LQGMetric.DFGPS.L217.locMollifyC ε hε g)
        (LQGMetric.DFGPS.L217.locMollifyC ε hε g).continuous) E F <
      (lfppContMetric ξ
        (LQGMetric.DFGPS.L217.locMollifyC ε hε g)
        (LQGMetric.DFGPS.L217.locMollifyC ε hε g).continuous).aroundDist A E F := by
  let φ := LQGMetric.DFGPS.L217.locMollifyC ε hε g
  let φ' := LQGMetric.DFGPS.L217.locMollifyC ε hε (addConst g c)
  have hφ : ∀ z, φ' z = φ ((0 : ℂ) + 1 * z) + c * locTestMass ε hε := by
    intro z
    simpa only [zero_add, one_mul, φ, φ',
      LQGMetric.DFGPS.L217.locMollifyC,
      ContinuousMap.coe_mk] using locMollify_addConst ε hε g c z
  have h := normalizedContLFPP_good_iff_affine ξ
    (⟨1, by norm_num⟩ : Ioi (0 : ℝ))
    (⟨1, by norm_num⟩ : Ioi (0 : ℝ))
    (φ := φ) (φ' := φ') (b := 0) (c := 1) (by norm_num)
    (c * locTestMass ε hε) hφ (Homeomorph.refl ℂ)
    (by intro z; simp) A E F C
  simpa only [Homeomorph.refl_apply, image_id, normalizedContLFPP_one,
    φ, φ'] using h

end SupercriticalLQGUniqueness.B2.DG20Lim
