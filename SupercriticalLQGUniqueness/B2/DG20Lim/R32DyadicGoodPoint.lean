import SupercriticalLQGUniqueness.B2.DG20Lim.R32DyadicGoodRData

 



set_option autoImplicit false
noncomputable section

open Filter
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Lim

theorem eventually_good_sparse_annulus_around_pointR32
    (R : RData) (C : ℝ≥0∞)
    (hsite : ∀ M : ℕ, ∀ᶠ K in atTop,
      ∀ v ∈ dyadicLatticeBox M K, dyadicGoodAtR32 R C K v)
    (M : ℕ) (z : ℂ) (hz : ‖z‖ < (M : ℝ)) :
    ∀ᶠ K in atTop,
      ∃ i ∈ sparseDyadicIndices K,
        let A := centeredRatAnnulusR32
          (dyadicLatticeCenter K (dyadicRoundCenter K z)).1
          (dyadicLatticeCenter K (dyadicRoundCenter K z)).2
          (ratRad64 1 i) (ratRad64_pos (by norm_num) i)
        A.inner.Surrounds z ∧
          R.around A ≤ C * R.across A.inner A.outer := by
  filter_upwards [hsite (M + 1)] with K hK
  obtain ⟨i, hi, hgood⟩ := hK (dyadicRoundCenter K z)
    (dyadicRoundCenter_mem_box M K z hz)
  exact ⟨i, hi, dyadic_good_inner_surroundsR32 K i z hi, hgood⟩

end SupercriticalLQGUniqueness.B2.DG20Lim
