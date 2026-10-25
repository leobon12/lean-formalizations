import SupercriticalLQGUniqueness.B2.DG20Pt.PtDistFiniteChain
import SupercriticalLQGUniqueness.B2.DG20Pt.PtDistCollar

 


set_option autoImplicit false
noncomputable section

open Set Topology Metric
open LQGMetric LQGMetric.DG

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_chain_with_collar
    {U : Set ℂ} (hU : IsOpen U) (hUc : IsConnected U)
    {z w : ℂ} (hz : z ∈ U) (hw : w ∈ U) :
    ∃ (K : Set ℂ), IsCompact K ∧ K ⊆ U ∧
      ∃ k₀ : ℕ, 1 ≤ k₀ ∧
        (∀ k, k₀ ≤ k → ∀ v ∈ K, ∀ x : ℂ,
          dist v x < ((2 : ℝ)⁻¹) ^ k / 4 →
          ball x (17 * ((2 : ℝ)⁻¹) ^ k) ⊆ U) ∧
      ∃ N : ℕ, ∃ p : ℕ → ℂ,
        p 0 = z ∧ p (N + 1) = w ∧
        (∀ j, j ≤ N + 1 → p j ∈ K) ∧
        ∀ j, j ≤ N → dist (p j) (p (j + 1)) <
          2 * ((2 : ℝ)⁻¹) ^ k₀ := by
  obtain ⟨q, hq⟩ := t15_exists_isDGPath hU hUc hz hw
  let K : Set ℂ := q '' Icc (0 : ℝ) 1
  have hK : IsCompact K := isCompact_Icc.image_of_continuousOn hq.continuousOn
  have hKU : K ⊆ U := by
    rintro x ⟨t, ht, rfl⟩
    exact hq.mapsTo ht
  obtain ⟨k, hk⟩ := pt_dist_eventual_crossing_ball_subset hK.isBounded hU
    (by simpa only [hK.isClosed.closure_eq] using hKU)
  let k₀ := max 1 k
  have hk₀ : 1 ≤ k₀ := le_max_left _ _
  have hkk₀ : k ≤ k₀ := le_max_right _ _
  have hδ : 0 < 2 * ((2 : ℝ)⁻¹) ^ k₀ := by positivity
  obtain ⟨N, p, hp0, hpN, hpK, hpstep⟩ :=
    pt_dist_finite_chain_of_path hq hδ
  refine ⟨K, hK, hKU, k₀, hk₀, ?_, N, p, hp0, hpN, hpK, ?_⟩
  · intro j hkj v hv x hx
    exact hk j (hkk₀.trans hkj) v hv x hx
  · intro j hj
    exact hpstep j hj

end SupercriticalLQGUniqueness.B2.DG20Pt
