import SupercriticalLQGUniqueness.B2.DG20Pt.PtDistChainTerminal

 


set_option autoImplicit false
noncomputable section

open Set Metric

namespace SupercriticalLQGUniqueness.B2.DG20Pt

theorem pt_dist_chain_geometry
    {U : Set ℂ} (hU : IsOpen U) (hUc : IsConnected U)
    {z w : ℂ} (hz : z ∈ U) (hw : w ∈ U) :
    ∃ K V : Set ℂ, IsCompact K ∧ K ⊆ U ∧
      Bornology.IsBounded V ∧ Convex ℝ V ∧
      ∃ k₀ : ℕ, 1 ≤ k₀ ∧
        (∀ k, k₀ ≤ k → ∀ v ∈ K, ∀ x : ℂ,
          dist v x < ((2 : ℝ)⁻¹) ^ k / 4 →
          ball x (17 * ((2 : ℝ)⁻¹) ^ k) ⊆ U) ∧
      ∃ N : ℕ, ∃ p : ℕ → ℂ,
        p 0 = z ∧ p (N + 1) = w ∧
        (∀ j, j ≤ N + 1 → p j ∈ K ∩ V) ∧
        (∀ j, j ≤ N → dist (p j) (p (j + 1)) <
          2 * ((2 : ℝ)⁻¹) ^ k₀) ∧
        ∀ n, k₀ ≤ n → ∀ j, j ≤ N + 1 →
          closedBall (p j) (((2 : ℝ)⁻¹) ^ n) ⊆ U ∩ V := by
  obtain ⟨K, hK, hKU, k₀, hk₀, hcollar, N, p, hp0, hpN, hpK, hpstep⟩ :=
    pt_dist_chain_with_collar hU hUc hz hw
  obtain ⟨V, hV, hconv, hbuffer⟩ := pt_dist_compact_buffered_region hK
  have hr1 (n : ℕ) : ((2 : ℝ)⁻¹) ^ n ≤ 1 := by
    exact pow_le_one₀ (by norm_num) (by norm_num)
  refine ⟨K, V, hK, hKU, hV, hconv, k₀, hk₀, hcollar,
    N, p, hp0, hpN, ?_, hpstep, ?_⟩
  · intro j hj
    have hjK := hpK j hj
    exact ⟨hjK, hbuffer (p j) hjK 0 (le_refl _) (by norm_num)
      (by simp)⟩
  · intro n hn j hj x hx
    exact ⟨pt_dist_terminal_ball_subset_of_collar hcollar (hpK j hj) hn hx,
      hbuffer (p j) (hpK j hj) _ (by positivity) (hr1 n) hx⟩

end SupercriticalLQGUniqueness.B2.DG20Pt
