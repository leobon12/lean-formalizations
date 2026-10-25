import SupercriticalLQGUniqueness.B2.DG20Lim.R32DyadicGoodRDataAE

 



set_option autoImplicit false
noncomputable section

open Filter Topology
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem RData.exists_shrinking_good_annulus_sequenceR32
    (R : RData) (C : ℝ≥0∞)
    (hsite : ∀ M : ℕ, ∀ᶠ K in atTop,
      ∀ v ∈ dyadicLatticeBox M K, dyadicGoodAtR32 R C K v)
    (z : ℂ) :
    ∃ A : ℕ → RatAnnulus,
      (∀ K, ∃ (x y r : ℚ) (hr : 0 < r), A K = centeredRatAnnulusR32 x y r hr) ∧
      (∀ᶠ K in atTop, (A K).inner.Surrounds z ∧
        R.around (A K) ≤ C * R.across (A K).inner (A K).outer) ∧
      Tendsto (fun K => (((A K).outer.radius : ℝ))) atTop (𝓝 0) := by
  classical
  obtain ⟨M, hM⟩ := exists_nat_gt ‖z‖
  have hQ := eventually_good_sparse_annulus_around_pointR32 R C hsite M z hM
  let Q : ℕ → Prop := fun K =>
    ∃ i ∈ sparseDyadicIndices K,
      let B := centeredRatAnnulusR32
        (dyadicLatticeCenter K (dyadicRoundCenter K z)).1
        (dyadicLatticeCenter K (dyadicRoundCenter K z)).2
        (ratRad64 1 i) (ratRad64_pos (by norm_num) i)
      B.inner.Surrounds z ∧
        R.around B ≤ C * R.across B.inner B.outer
  let A : ℕ → RatAnnulus := fun K =>
    if h : Q K then
      centeredRatAnnulusR32
        (dyadicLatticeCenter K (dyadicRoundCenter K z)).1
        (dyadicLatticeCenter K (dyadicRoundCenter K z)).2
        (ratRad64 1 (Classical.choose h))
        (ratRad64_pos (by norm_num) (Classical.choose h))
    else centeredRatAnnulusR32 0 0 1 (by norm_num)
  have hAK (K : ℕ) (hK : Q K) : A K =
      centeredRatAnnulusR32
        (dyadicLatticeCenter K (dyadicRoundCenter K z)).1
        (dyadicLatticeCenter K (dyadicRoundCenter K z)).2
        (ratRad64 1 (Classical.choose hK))
        (ratRad64_pos (by norm_num) (Classical.choose hK)) := by
    dsimp [A]
    rw [dif_pos hK]
  have hselected : ∀ᶠ K in atTop,
      (A K).inner.Surrounds z ∧
      R.around (A K) ≤ C * R.across (A K).inner (A K).outer := by
    filter_upwards [hQ] with K hK
    have hspec := Classical.choose_spec hK
    rw [hAK K hK]
    exact hspec.2
  have hupper : ∀ᶠ K in atTop,
      (((A K).outer.radius : ℝ)) ≤ 2 / (2 : ℝ) ^ (K / 2) := by
    filter_upwards [hQ] with K hK
    have hi := (Classical.choose_spec hK).1
    have hr := (sparse_radius_bounds hi).2
    rw [hAK K hK]
    change ((3 / 2 * ratRad64 1 (Classical.choose hK) : ℚ) : ℝ) ≤
      2 / (2 : ℝ) ^ (K / 2)
    push_cast
    have h0 : (0 : ℝ) ≤ ((ratRad64 1 (Classical.choose hK) : ℚ) : ℝ) := by
      exact_mod_cast (ratRad64_pos (by norm_num) (Classical.choose hK)).le
    have h2 : 2 * ((ratRad64 1 (Classical.choose hK) : ℚ) : ℝ) ≤ 2 / (2 : ℝ) ^ (K / 2) := by
      simpa only [div_eq_mul_inv, mul_assoc, one_mul] using
        (mul_le_mul_of_nonneg_left hr (by norm_num : (0 : ℝ) ≤ 2))
    linarith
  have hshape : ∀ K, ∃ (x y r : ℚ) (hr : 0 < r), A K = centeredRatAnnulusR32 x y r hr := by
    intro K
    by_cases h : Q K
    · exact ⟨_, _, _, _, hAK K h⟩
    · exact ⟨0, 0, 1, by norm_num, by simp [A, h]⟩
  refine ⟨A, hshape, hselected, ?_⟩
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun _ : ℕ => (0 : ℝ)) (h := fun K => 2 / (2 : ℝ) ^ (K / 2))
    tendsto_const_nhds tendsto_sparse_radius_upper_zero
  · exact Filter.Eventually.of_forall fun K => by
      exact_mod_cast (A K).outer.radius_nonneg
  · exact hupper

end SupercriticalLQGUniqueness.B2.DG20Lim
