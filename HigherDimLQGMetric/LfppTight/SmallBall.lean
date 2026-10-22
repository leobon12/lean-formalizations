import HigherDimLQGMetric.LfppTight.CoupledHolderAll
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! A small radius makes a uniform Hölder upper bound smaller than a shell lower bound. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Filter Topology

namespace HigherDimLQGMetric

theorem l6a_exists_small_ball {M m C β : ℝ}
    (hm : 0 < m) (hC : 0 < C) (hβ : 0 < β) :
    ∃ b : ℝ, 0 < b ∧ b ≤ 1 / 4 ∧ M * (2 * b) ^ β ≤ m / C := by
  have hc : Continuous (fun b : ℝ => M * (2 * b) ^ β) :=
    continuous_const.mul
      ((Real.continuous_rpow_const hβ.le).comp (continuous_const.mul continuous_id))
  have ht : Tendsto (fun b : ℝ => M * (2 * b) ^ β)
      (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    convert (hc.tendsto 0).mono_left nhdsWithin_le_nhds using 1
    simp [Real.zero_rpow hβ.ne']
  have hmc : 0 < m / C := div_pos hm hC
  have he : ∀ᶠ b : ℝ in 𝓝[>] 0, M * (2 * b) ^ β < m / C :=
    ht.eventually (gt_mem_nhds hmc)
  have hpos : ∀ᶠ b : ℝ in 𝓝[>] 0, 0 < b := self_mem_nhdsWithin
  have hsmall : ∀ᶠ b : ℝ in 𝓝[>] 0, b < 1 / 4 :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 4))
  obtain ⟨b, hb, hs, hq⟩ := (hpos.and (he.and hsmall)).exists
  exact ⟨b, hb, hq.le, hs.le⟩

end HigherDimLQGMetric
