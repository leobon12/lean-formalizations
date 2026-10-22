import HigherDimLQGMetric.Sec8.Geod
import HigherDimLQGMetric.ScaleBin.Lemma81

/-!
# Section 8: separated sites on a continuous path

A continuous path from `x` to `y` crosses every intermediate Euclidean
radius about `x`. This is the deterministic starting point of Lemma 8.4.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open Set Metric unitInterval
open HigherDimLFPP (Rd)

variable {d : ℕ}

/-- Coordinate form of `latPt`, used to pass a covering site to the bin event. -/
theorem s7b_latPt_coordinates (r : ℝ) (k : Fin d → ℤ) :
    EuclideanSpace.equiv (Fin d) ℝ (HigherDimLFPP.DGZ.latPt (r / (100 * d)) k) =
      fun i => r / (100 * d) * (k i : ℝ) := by
  funext i
  rfl

/-- Every intermediate Euclidean radius is hit by a path from `x` to `y`. -/
theorem s7b_exists_radius_hit (η : C(unitInterval, Rd d))
    (x y : Rd d) (h0 : η 0 = x) (h1 : η 1 = y)
    {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρxy : ρ ≤ ‖y - x‖) :
    ∃ t : unitInterval, ‖η t - x‖ = ρ := by
  let F : unitInterval → ℝ := fun t => ‖η t - x‖
  have hF : Continuous F := by fun_prop
  have hρ : ρ ∈ Icc (F 0) (F 1) := by
    simpa only [F, h0, h1, sub_self, norm_zero, mem_Icc] using And.intro hρ0 hρxy
  obtain ⟨t, ht⟩ := intermediate_value_univ 0 1 hF hρ
  exact ⟨t, ht⟩

/-- Sampling radii twenty mesh units apart makes their rounded centres
separated by more than eighteen mesh units. -/
theorem s7b_centers_separated {x p₁ p₂ z₁ z₂ : Rd d}
    {a ρ₁ ρ₂ : ℝ} (ha : 0 < a)
    (hρ₁ : ‖p₁ - x‖ = ρ₁) (hρ₂ : ‖p₂ - x‖ = ρ₂)
    (hgap : ρ₁ + 20 * a ≤ ρ₂)
    (hclose₁ : ‖p₁ - z₁‖ < a / 2)
    (hclose₂ : ‖p₂ - z₂‖ < a / 2) :
    18 * a < ‖z₁ - z₂‖ := by
  have hrad : ρ₂ - ρ₁ ≤ ‖p₂ - p₁‖ := by
    rw [← hρ₁, ← hρ₂]
    have h := norm_sub_norm_le (p₂ - x) (p₁ - x)
    convert h using 1; abel
  have hpath : ‖p₂ - p₁‖ ≤ ‖p₂ - z₂‖ + ‖z₂ - z₁‖ + ‖z₁ - p₁‖ := by
    calc
      ‖p₂ - p₁‖ = ‖(p₂ - z₂) + (z₂ - z₁) + (z₁ - p₁)‖ := by congr 1; abel
      _ ≤ ‖(p₂ - z₂) + (z₂ - z₁)‖ + ‖z₁ - p₁‖ := norm_add_le _ _
      _ ≤ (‖p₂ - z₂‖ + ‖z₂ - z₁‖) + ‖z₁ - p₁‖ := by
        gcongr
        exact norm_add_le _ _
  rw [norm_sub_rev z₁ p₁] at hpath
  rw [norm_sub_rev z₂ z₁] at hpath
  have h20 : 20 * a ≤ ‖p₂ - p₁‖ := by linarith only [hgap, hrad]
  have hnear : ‖p₂ - z₂‖ + ‖p₁ - z₁‖ < a := by
    linarith only [hclose₁, hclose₂]
  have hdist : ‖p₂ - p₁‖ < ‖z₁ - z₂‖ + a := by
    linarith only [hpath, hnear]
  linarith only [h20, hdist, ha]

/-- The repair for large endpoint separation: sample at a radius controlled by
`θ ≤ min η 1`, so the rounded centre stays inside the macro ball. -/
theorem s7b_sampled_center_bounds {x y p z : Rd d}
    {R η θ ε r : ℝ} (hR : 0 < R) (_hθ : 0 < θ)
    (hθη : θ ≤ η) (hθ1 : θ ≤ 1)
    (_hε : 0 < ε) (hεθ : ε < θ / 18)
    (hr : 0 < r) (hrε : r ≤ ε * R)
    (hx : ‖x‖ < 3 * R) (hxy : η * R ≤ ‖y - x‖)
    (hpLo : θ * R / 4 ≤ ‖p - x‖)
    (hpHi : ‖p - x‖ ≤ θ * R / 2)
    (hz : ‖p - z‖ < r / 2) :
    ‖z‖ < 5 * R ∧ x ∉ closedBall z (4 * r) ∧ y ∉ closedBall z (4 * r) := by
  have hθR : θ * R ≤ R := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hθ1 hR.le
  have hηR : θ * R ≤ η * R := mul_le_mul_of_nonneg_right hθη hR.le
  have hεR : ε * R < θ * R / 18 := by
    have h := mul_lt_mul_of_pos_right hεθ hR
    have heq : θ / 18 * R = θ * R / 18 := by ring
    rwa [heq] at h
  have hz' : ‖z - p‖ < r / 2 := by simpa only [norm_sub_rev] using hz
  have hzx : ‖z - x‖ ≤ ‖z - p‖ + ‖p - x‖ := by
    calc
      ‖z - x‖ = ‖(z - p) + (p - x)‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  have hznorm : ‖z‖ ≤ ‖z - x‖ + ‖x‖ := by
    calc
      ‖z‖ = ‖(z - x) + x‖ := by congr 1; abel
      _ ≤ _ := norm_add_le _ _
  have hcenter : ‖z‖ < 5 * R := by
    have hr2 : r / 2 ≤ ε * R / 2 := by linarith only [hrε]
    linarith only [hznorm, hzx, hz', hpHi, hx, hr2, hεR, hθR, hR]
  have hxz : ‖p - x‖ - ‖p - z‖ ≤ ‖x - z‖ := by
    have h := norm_sub_norm_le (p - x) (p - z)
    have heq : (p - x) - (p - z) = z - x := by abel
    rw [heq] at h
    simpa only [norm_sub_rev z x] using h
  have hxyP : ‖y - x‖ - ‖p - x‖ ≤ ‖y - p‖ := by
    have h := norm_sub_norm_le (y - x) (p - x)
    convert h using 1; abel
  have hyz : ‖y - p‖ - ‖z - p‖ ≤ ‖y - z‖ := by
    have h := norm_sub_norm_le (y - p) (z - p)
    convert h using 1; abel
  have hεsmall : 9 * r / 2 < θ * R / 4 := by
    have hrbound := hrε
    linarith only [hrbound, hεR, hR]
  have hxout : 4 * r < ‖x - z‖ := by
    linarith only [hxz, hpLo, hz, hεsmall]
  have hyout : 4 * r < ‖y - z‖ := by
    have hrad : θ * R / 2 ≤ ‖y - p‖ := by
      linarith only [hxyP, hxy, hηR, hpHi]
    have hYZ : θ * R / 2 - r / 2 < ‖y - z‖ := by
      linarith only [hrad, hyz, hz']
    linarith only [hYZ, hεsmall, hr]
  refine ⟨hcenter, ?_, ?_⟩
  · simpa only [mem_closedBall, dist_eq_norm, norm_sub_rev] using not_le.mpr hxout
  · simpa only [mem_closedBall, dist_eq_norm, norm_sub_rev] using not_le.mpr hyout

end HigherDimLQGMetric
