import SupercriticalLQGUniqueness.B2.DG20Conc.LaneBSmallAnnulusGeometry

 







set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open Set Metric MeasureTheory

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

 
def laneBBlockAnnulus (i : Bool) (v : ℂ) (K : ℕ) : Set ℂ :=
  (fun z => v + (2 : ℝ)⁻¹ ^ K • (z - (⟨1 / 2, 1 / 2⟩ : ℂ))) ''
    laneCUnitUcross i

 
theorem laneB_small_radius_le_one {K : ℕ} (hK : 3 ≤ K) :
    5 * (2 : ℝ)⁻¹ ^ K ≤ 1 := by
  have hpow : (2 : ℝ)⁻¹ ^ K ≤ (2 : ℝ)⁻¹ ^ 3 :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hK
  norm_num at hpow
  linarith

 
theorem laneB_block_annulus_subset_closedBall (i : Bool) (v : ℂ) (K : ℕ) :
    laneBBlockAnnulus i v K ⊆ closedBall v (5 * (2 : ℝ)⁻¹ ^ K) := by
  intro z hz
  obtain ⟨y, hy, rfl⟩ := hz
  rw [mem_closedBall, dist_eq_norm]
  have hnorm := laneB_unit_small_annuli_radius i hy
  simpa only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
    mul_comm (5 : ℝ),
    abs_of_nonneg (by positivity : 0 ≤ (2 : ℝ)⁻¹ ^ K)] using
    (mul_le_mul_of_nonneg_left hnorm (by positivity : 0 ≤ (2 : ℝ)⁻¹ ^ K))

 

theorem laneB_phiMN_small_annuli_gaussian_bad_event :
    ∃ C σ2 : ℝ, 0 < C ∧ 0 < σ2 ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
      {W : WNSpace → Ω → ℝ}, IsWhiteNoise P W →
    ∀ (K : ℕ), 3 ≤ K →
    ∀ {ι : Type*} (kind : ι → Bool) (v : ι → ℂ) (x : ℝ),
      0 ≤ x → (∀ j, v j ∈ (rectAB 1 1).toSet) →
      P.real {ω | ∃ j, ∃ z ∈ laneBBlockAnnulus (kind j) (v j) K,
        5 * x < |phiMN W P 0 K z ω - phiMN W P 0 K (v j) ω|} ≤
        C * 4 ^ K * Real.exp (-x ^ 2 / (2 * σ2)) := by
  obtain ⟨C, σ2, hC, hσ2, htail⟩ :=
    laneB_phiMN_round_annuli_gaussian_bad_event
  refine ⟨C, σ2, hC, hσ2, ?_⟩
  intro Ω _ P W hW K hK ι kind v x hx hv
  exact htail hW K (fun j => laneBBlockAnnulus (kind j) (v j) K) v
    (5 * (2 : ℝ)⁻¹ ^ K) 5 x (laneB_small_radius_le_one hK)
    (by norm_num) hx (le_refl _) hv
    (fun j => laneB_block_annulus_subset_closedBall (kind j) (v j) K)

end SupercriticalLQGUniqueness.B2.DG20Conc
