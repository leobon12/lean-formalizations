import HigherDimLQGMetric.Sharp.CompareDet
import HigherDimLQGMetric.Sharp.GridNear
import HigherDimLQGMetric.Sharp.GoodScalesAE

/-! Turning a grid cover into a cover of a path. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set Metric
open HigherDimLFPP (Rd)

variable {d : ℕ}

theorem sharpMesh_tendsto_zero :
    Filter.Tendsto sharpMesh Filter.atTop (nhds 0) := by
  have h := tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  change Filter.Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ (n + 1)) Filter.atTop (nhds 0)
  simpa only [pow_succ, zero_mul] using h.mul_const (1 / 2 : ℝ)

theorem le_of_approx_pairs (D : ContMetric d) {u v : Rd d} {B : ℝ}
    (h : ∀ δ : ℝ, 0 < δ → ∃ x y : Rd d,
      ‖x - u‖ ≤ δ ∧ ‖y - v‖ ≤ δ ∧ D.1 (x, y) ≤ B) :
    D.1 (u, v) ≤ B := by
  by_contra hnot
  have hgap : 0 < D.1 (u, v) - B := by linarith
  have hcAt : ContinuousAt (D.1 : Rd d × Rd d → ℝ) (u, v) :=
    D.1.continuous.continuousAt
  obtain ⟨δ, hδ, hc⟩ := (Metric.continuousAt_iff.1 hcAt)
    ((D.1 (u, v) - B) / 2) (by linarith)
  obtain ⟨x, y, hx, hy, hxy⟩ := h (δ / 2) (by linarith)
  have hdist : dist (x, y) (u, v) < δ := by
    have hmax : max (dist x u) (dist y v) ≤ δ / 2 := by
      rw [max_le_iff]
      exact ⟨by simpa only [dist_eq_norm] using hx,
        by simpa only [dist_eq_norm] using hy⟩
    rw [Prod.dist_eq]
    linarith
  have hcont := hc hdist
  rw [Real.dist_eq] at hcont
  have hdiff := (abs_lt.mp hcont).1
  linarith

theorem path_cover_of_grid (hd : 3 ≤ d) (P : ℝ → Rd d)
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
theorem compare_of_eventual_grids (hd : 3 ≤ d) (D₁ D₂ : ContMetric d)
    (hLen : D₁.IsLength) {C : ℝ} (hC : 0 < C)
    (hgrid : ∀ᶠ n : ℕ in Filter.atTop,
      ∀ w ∈ gridPts ((sharpMesh n) ^ 2 / (10 * d)) ∩
          ball (0 : Rd d) (1 / sharpMesh n),
        ∃ k : ℕ, (sharpMesh n) ^ 2 ≤ 1 / 2 ^ k ∧
          1 / 2 ^ k ≤ sharpMesh n ∧
          sphereDiam D₂ w (1 / 2 ^ k) ≤ ENNReal.ofReal C *
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
    have hnCover := path_cover_of_grid hd P hR0 hPbound
      (sharpMesh_pos n) (sharpMesh_lt_one n) hnR
      (fun w r => sphereDiam D₂ w r ≤ ENNReal.ofReal C * acrossDist D₁ w (r / 2) r)
      hnGrid
    obtain ⟨x, y, hx, hy, hxy⟩ := compare_of_path_cover (by omega : 2 ≤ d)
      D₁ D₂ hC (sq_pos_of_pos (sharpMesh_pos n)) hη.le P hPc hP0 hP1 hPlen'
      hnCover
    refine ⟨x, y, ?_, ?_, hxy⟩ <;> linarith
  refine le_of_forall_pos_le_add fun δ hδ => ?_
  have hη' := hη (δ / C) (div_pos hδ hC)
  rw [mul_add, mul_div_cancel₀ δ hC.ne'] at hη'
  exact hη'

end HigherDimLQGMetric
