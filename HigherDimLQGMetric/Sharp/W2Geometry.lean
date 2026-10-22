import HigherDimLQGMetric.Sharp.W2Path
import HigherDimLQGMetric.Sharp.W2Det

/-! Euclidean geometry for the uniform upper-distance estimate. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set Metric
open HigherDimLFPP (Rd)

variable {d : ℕ}

private theorem w2_affine_dist {𝕣 : ℝ} (h𝕣 : 0 ≤ 𝕣) (z x y : Rd d) :
    dist (z + 𝕣 • x) (z + 𝕣 • y) = 𝕣 * dist x y := by
  rw [dist_add_left, dist_smul₀, Real.norm_eq_abs, abs_of_nonneg h𝕣]

/-- A nontrivial set remains too large for a small ball after scaling. -/
theorem w2_affine_not_subset_ball {K : Set (Rd d)} (_hK : K.Nontrivial)
    {𝕣 ε : ℝ} (h𝕣 : 0 < 𝕣) (_hε : 0 ≤ ε)
    (hsmall : ∃ x ∈ K, ∃ y ∈ K, 2 * ε < dist x y)
    (z c : Rd d) : ¬ affineSet 𝕣 z K ⊆ ball c (ε * 𝕣) := by
  rintro hsub
  obtain ⟨x, hx, y, hy, hxy⟩ := hsmall
  have hx' : z + 𝕣 • x ∈ ball c (ε * 𝕣) := hsub ⟨x, hx, rfl⟩
  have hy' : z + 𝕣 • y ∈ ball c (ε * 𝕣) := hsub ⟨y, hy, rfl⟩
  have ht := dist_triangle (z + 𝕣 • x) c (z + 𝕣 • y)
  rw [mem_ball] at hx' hy'
  rw [w2_affine_dist h𝕣.le] at ht
  rw [dist_comm (z + 𝕣 • y) c] at hy'
  nlinarith only [hx', hy', ht, hxy, h𝕣]

/-- A fixed nontrivial set has a positive Euclidean separation scale. -/
theorem w2_nontrivial_sep {K : Set (Rd d)} (hK : K.Nontrivial) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, ε ≤ η →
      ∃ x ∈ K, ∃ y ∈ K, 2 * ε < dist x y := by
  obtain ⟨x, hx, y, hy, hxy⟩ := hK
  have hd : 0 < dist x y := dist_pos.mpr hxy
  refine ⟨dist x y / 3, by positivity, ?_⟩
  intro ε hε
  exact ⟨x, hx, y, hy, by linarith only [hε, hd]⟩

/-- A compact Lipschitz path admits a positive uniform margin inside its open domain. -/
theorem w2_path_margin {U : Set (Rd d)} (hU : IsOpen U)
    (P : ℝ → Rd d) (hP : ContinuousOn P (Icc (0 : ℝ) 1))
    (hPU : MapsTo P (Icc (0 : ℝ) 1) U) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t ∈ Icc (0 : ℝ) 1, ball (P t) δ ⊆ U := by
  let K : Set (Rd d) := P '' Icc (0 : ℝ) 1
  have hK : IsCompact K := isCompact_Icc.image_of_continuousOn hP
  have hKU : K ⊆ U := by rintro x ⟨t, ht, rfl⟩; exact hPU ht
  obtain ⟨δ, hδ, hthick⟩ := hK.exists_thickening_subset_open hU hKU
  refine ⟨δ, hδ, ?_⟩
  intro t ht
  exact (ball_subset_thickening (show P t ∈ K from ⟨t, ht, rfl⟩) δ).trans hthick

/-- Scale a fixed path and its Euclidean margin; the constants are independent of scale. -/
theorem w2_scaled_path {U : Set (Rd d)} (hU : IsOpen U) (hUc : IsConnected U)
    {x y : Rd d} (hx : x ∈ U) (hy : y ∈ U) :
    ∃ Λ R δ : ℝ, 0 ≤ Λ ∧ 0 ≤ R ∧ 0 < δ ∧
      ∀ (𝕣 : ℝ), 0 < 𝕣 → ∀ z : Rd d,
        ∃ P : ℝ → Rd d,
          LipschitzOnWith (Real.toNNReal (𝕣 * Λ)) P (Icc 0 1) ∧
          P 0 = z + 𝕣 • x ∧ P 1 = z + 𝕣 • y ∧
          (∀ t ∈ Icc (0 : ℝ) 1, ‖P t - z‖ ≤ R * 𝕣) ∧
          (∀ t ∈ Icc (0 : ℝ) 1, ball (P t) (δ * 𝕣) ⊆ affineSet 𝕣 z U) := by
  obtain ⟨Λ, P₀, hΛ, hLip, h0, h1, hPU⟩ := w2_exists_lipschitz_path hU hUc hx hy
  have hPc : ContinuousOn P₀ (Icc (0 : ℝ) 1) := hLip.continuousOn
  obtain ⟨δ, hδ, hmargin⟩ := w2_path_margin hU P₀ hPc hPU
  have hbounded : Bornology.IsBounded (P₀ '' Icc (0 : ℝ) 1) :=
    (isCompact_Icc.image_of_continuousOn hPc).isBounded
  obtain ⟨R₀, hR₀⟩ := (Metric.isBounded_iff_subset_ball (0 : Rd d)).1 hbounded
  let R : ℝ := max R₀ 0
  have hR : 0 ≤ R := le_max_right _ _
  have hPnorm : ∀ t ∈ Icc (0 : ℝ) 1, ‖P₀ t‖ ≤ R := by
    intro t ht
    have h := hR₀ ⟨t, ht, rfl⟩
    rw [mem_ball, dist_zero_right] at h
    exact h.le.trans (le_max_left _ _)
  refine ⟨Λ, R, δ, hΛ, hR, hδ, ?_⟩
  intro 𝕣 h𝕣 z
  let P : ℝ → Rd d := fun t => z + 𝕣 • P₀ t
  refine ⟨P, ?_, by simp only [P, h0], by simp only [P, h1], ?_, ?_⟩
  · rw [lipschitzOnWith_iff_dist_le_mul]
    intro s hs t ht
    have h := (lipschitzOnWith_iff_dist_le_mul.mp hLip) s hs t ht
    rw [w2_affine_dist h𝕣.le]
    have hcoef : (Real.toNNReal Λ : ℝ) = Λ := Real.coe_toNNReal _ hΛ
    rw [hcoef] at h
    rw [Real.coe_toNNReal _ (mul_nonneg h𝕣.le hΛ)]
    exact mul_le_mul_of_nonneg_left h h𝕣.le |>.trans_eq (by ring)
  · intro t ht
    change ‖z + 𝕣 • P₀ t - z‖ ≤ R * 𝕣
    rw [add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos h𝕣]
    nlinarith only [hPnorm t ht, h𝕣]
  · intro t ht v hv
    have hv' : dist (P₀ t) (𝕣⁻¹ • (v - z)) < δ := by
      have he : v = z + 𝕣 • (𝕣⁻¹ • (v - z)) := by
        rw [smul_smul, mul_inv_cancel₀ h𝕣.ne', one_smul]
        abel
      have hdist : dist (P t) v = 𝕣 * dist (P₀ t) (𝕣⁻¹ • (v - z)) := by
        calc
          dist (P t) v = dist (z + 𝕣 • P₀ t) (z + 𝕣 • (𝕣⁻¹ • (v - z))) := by
            rw [← he]
          _ = _ := w2_affine_dist h𝕣.le z (P₀ t) _
      rw [mem_ball, dist_comm, hdist] at hv
      exact lt_of_mul_lt_mul_left (by simpa only [mul_comm δ 𝕣] using hv) h𝕣.le
    have hU' : 𝕣⁻¹ • (v - z) ∈ U := hmargin t ht (by simpa [mem_ball, dist_comm] using hv')
    refine ⟨𝕣⁻¹ • (v - z), hU', ?_⟩
    change z + 𝕣 • (𝕣⁻¹ • (v - z)) = v
    rw [smul_smul, mul_inv_cancel₀ h𝕣.ne', one_smul]
    abel

end HigherDimLQGMetric
