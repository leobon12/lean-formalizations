import SupercriticalLQGUniqueness.B2.DG20Conc.J1SourceRadius

 







set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Metric

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric.DDDF LQGMetric.WhiteNoise

theorem laneB_dyBlock_diameter_le_two {K : ℕ} {b : ℤ × ℤ}
    {z y : ℂ} (hz : z ∈ T20.dyBlock K b)
    (hy : y ∈ T20.dyBlock K b) :
    dist z y ≤ 2 * (2 : ℝ)⁻¹ ^ K := by
  have hr : 0 ≤ (2 : ℝ)⁻¹ ^ K := by positivity
  simp only [T20.dyBlock, Complex.mem_reProdIm, mem_Icc] at hz hy
  rw [dist_eq_norm]
  have hre : |(z - y).re| ≤ (2 : ℝ)⁻¹ ^ K := by
    rw [Complex.sub_re, abs_le]
    constructor <;> nlinarith [hz.1.1, hz.1.2, hy.1.1, hy.1.2]
  have him : |(z - y).im| ≤ (2 : ℝ)⁻¹ ^ K := by
    rw [Complex.sub_im, abs_le]
    constructor <;> nlinarith [hz.2.1, hz.2.2, hy.2.1, hy.2.2]
  exact (Complex.norm_le_abs_re_add_abs_im _).trans (by linarith)

theorem laneB_visited_block_mem_sourceIdx
    (Q : PsiParams) {K : ℕ} (hε : Q.ε₀ ≤ 1) (hK : 6 ≤ K)
    {b : ℤ × ℤ}
    (hvisit : (T20.dyBlock K b ∩ L23.sq01).Nonempty) :
    b ∈ j1SourceIdx K (j1SourceRadius Q K) := by
  obtain ⟨y, hy, hyU⟩ := hvisit
  apply j1_source_mem_sourceIdx Q K hε hK
  intro z hz
  apply mem_thickening_iff.mpr
  refine ⟨y, hyU, ?_⟩
  have hdiam := laneB_dyBlock_diameter_le_two hz hy
  have hK1 : (1 : ℝ) < K := by exact_mod_cast (by omega : 1 < K)
  have hpow : 1 < (K : ℝ) ^ Q.ε₀ :=
    Real.one_lt_rpow hK1 Q.ε₀_pos
  have hr : 0 < (2 : ℝ)⁻¹ ^ K := by positivity
  dsimp [j1SourceRadius]
  nlinarith

 

theorem laneB_coarseBlocks_subset_sourceIdx
    (Q : PsiParams) {K : ℕ} (hε : Q.ε₀ ≤ 1) (hK : 6 ≤ K)
    {γ : ℝ → ℂ} (hγ : MapsTo γ (Icc (0 : ℝ) 1) L23.sq01) :
    T20.coarseBlocks K γ ⊆ j1SourceIdx K (j1SourceRadius Q K) := by
  classical
  intro b hb
  obtain ⟨_, t, ht, hbt⟩ := Finset.mem_filter.mp hb
  apply laneB_visited_block_mem_sourceIdx Q hε hK
  exact ⟨γ t, hbt, hγ ht⟩

end SupercriticalLQGUniqueness.B2.DG20Conc
