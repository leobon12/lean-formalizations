import HigherDimLQGMetric.Bilip.CompareDet
import HigherDimLQGMetric.Sharp.CompareCover

/-! The sharp grid-to-path cover, with dimension `d ≥ 2` and the larger-shell event. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGMetric
open Set Metric
open HigherDimLFPP (Rd)
open scoped ENNReal
variable {d : ℕ}

theorem bilip_path_cover_of_grid (hd : 2 ≤ d) (P : ℝ → Rd d)
    {R ε : ℝ} (hR : 0 ≤ R) (hP : ∀ s ∈ Icc (0 : ℝ) 1, ‖P s‖ ≤ R)
    (hε : 0 < ε) (hε1 : ε < 1) (hεR : ε < 1 / (R + 2))
    (good : Rd d → ℝ → Prop)
    (hgrid : ∀ w ∈ gridPts (ε ^ 2 / (10 * d)) ∩
        ball (0 : Rd d) (1 / ε),
      ∃ k : ℕ, ε ^ 2 ≤ 1 / 2 ^ k ∧ 1 / 2 ^ k ≤ ε ∧ good w (1 / 2 ^ k)) :
    ∀ s ∈ Icc (0 : ℝ) 1, ∃ w r,
      ε ^ 2 ≤ r ∧ r ≤ ε ∧ ‖P s - w‖ < r / 2 ∧ good w r := by
  intro s hs
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hmesh : 0 < ε ^ 2 / (10 * d) := by positivity
  obtain ⟨w, hwGrid, hwNear⟩ := exists_gridPt_near hmesh (P s)
  have hnear : ‖P s - w‖ ≤ ε ^ 2 / 10 := by
    have hfactor : (d : ℝ) * (ε ^ 2 / (10 * d)) = ε ^ 2 / 10 := by
      field_simp
    rw [hfactor] at hwNear
    exact hwNear
  have hwNorm : ‖w‖ ≤ R + ε ^ 2 / 10 := by
    have htri : ‖w‖ ≤ ‖P s‖ + ‖P s - w‖ := by
      calc
        ‖w‖ = ‖P s - (P s - w)‖ := by congr 1; abel
        _ ≤ ‖P s‖ + ‖P s - w‖ := norm_sub_le _ _
    linarith [hP s hs]
  have hRinv : R + 1 < 1 / ε := by
    have hprod : ε * (R + 2) < 1 := by
      have h := (lt_div_iff₀ (by linarith : 0 < R + 2)).1 hεR
      nlinarith
    exact (lt_div_iff₀ hε).2 (by nlinarith)
  have hwBall : w ∈ ball (0 : Rd d) (1 / ε) := by
    rw [mem_ball, dist_zero_right]
    have hεsq : ε ^ 2 / 10 < 1 := by nlinarith
    linarith
  obtain ⟨k, hlow, hupp, hgood⟩ := hgrid w ⟨hwGrid, hwBall⟩
  refine ⟨w, 1 / 2 ^ k, hlow, hupp, ?_, hgood⟩
  have hsmall : ε ^ 2 / 10 < (1 / 2 ^ k : ℝ) / 2 := by
    linarith [sq_pos_of_pos hε]
  exact hnear.trans_lt hsmall

/-- A simultaneous good grid cover at all sufficiently fine dyadic meshes
compares two length metrics everywhere. -/
theorem bilip_compare_of_eventual_grids (hd : 2 ≤ d) (D₁ D₂ : ContMetric d)
    (hLen : D₁.IsLength) {C : ℝ} (hC : 0 < C)
    (hgrid : ∀ᶠ n : ℕ in Filter.atTop,
      ∀ w ∈ gridPts ((sharpMesh n) ^ 2 / (10 * d)) ∩
          ball (0 : Rd d) (1 / sharpMesh n),
        ∃ k : ℕ, (sharpMesh n) ^ 2 ≤ 1 / 2 ^ k ∧
          1 / 2 ^ k ≤ sharpMesh n ∧
          internalDiamRd D₂ (sphere w (1 / 2 ^ k)) (shellOpen w ((1 / 2 ^ k) / 4) (4 * (1 / 2 ^ k))) ≤ ENNReal.ofReal C *
            acrossDist D₁ w ((1 / 2 ^ k) / 2) (1 / 2 ^ k)) :
    ∀ u v : Rd d, D₂.1 (u, v) ≤ C * D₁.1 (u, v) := by
  intro u v
  have hη : ∀ η : ℝ, 0 < η → D₂.1 (u, v) ≤ C * (D₁.1 (u, v) + η) := by
    intro η hη
    obtain ⟨P, hPc, hP0, hP1, hPlen⟩ :=
      (D₁.isLength_iff_curves.mp hLen) u v η hη
    have hPlen' : D₁.len P 0 1 ≤ ENNReal.ofReal (D₁.1 (u, v) + η) := by
      rw [ENNReal.ofReal_add (D₁.nonneg u v) hη.le]
      exact hPlen
    have hPcomp : IsCompact (P '' Icc (0 : ℝ) 1) :=
      isCompact_Icc.image_of_continuousOn hPc
    obtain ⟨R, hR⟩ := (isBounded_iff_forall_norm_le.mp hPcomp.isBounded)
    have hR0 : 0 ≤ R := by
      have hu := hR (P 0) ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
      linarith [norm_nonneg (P 0)]
    have hPbound : ∀ s ∈ Icc (0 : ℝ) 1, ‖P s‖ ≤ R := by
      intro s hs
      exact hR (P s) ⟨s, hs, rfl⟩
    apply le_of_approx_pairs D₂
    intro δ hδ
    have hδmesh : ∀ᶠ n : ℕ in Filter.atTop, sharpMesh n < δ / 2 :=
      sharpMesh_tendsto_zero.eventually (Iio_mem_nhds (by linarith))
    have hRmesh : ∀ᶠ n : ℕ in Filter.atTop, sharpMesh n < 1 / (R + 2) :=
      sharpMesh_tendsto_zero.eventually
        (Iio_mem_nhds (by positivity : (0 : ℝ) < 1 / (R + 2)))
    obtain ⟨n, hnGrid, hnδ, hnR⟩ := (hgrid.and (hδmesh.and hRmesh)).exists
    have hnCover := bilip_path_cover_of_grid hd P hR0 hPbound
      (sharpMesh_pos n) (sharpMesh_lt_one n) hnR
      (fun w r => internalDiamRd D₂ (sphere w r) (shellOpen w (r / 4) (4 * r)) ≤ ENNReal.ofReal C * acrossDist D₁ w (r / 2) r)
      hnGrid
    obtain ⟨x, y, hx, hy, hxy⟩ := bilip_compare_of_path_cover (by omega : 2 ≤ d)
      D₁ D₂ hC (sq_pos_of_pos (sharpMesh_pos n)) hη.le P hPc hP0 hP1 hPlen'
      hnCover
    refine ⟨x, y, ?_, ?_, hxy⟩ <;> linarith
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have hη' := hη (δ / C) (div_pos hδ hC)
  rw [mul_add, mul_div_cancel₀ δ hC.ne'] at hη'
  exact hη'

end HigherDimLQGMetric
