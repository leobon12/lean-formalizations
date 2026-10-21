import SmallGammaGeodesics.CC.Prop21Pull

/-!
# [3] Prop 2.1: the geometry of the zoom at `(z, r)` (packet CC6b; CC0 Details D10)

Source: `planning/audits/CC0-conformal-covariance-plan.md`, Details (a) **D10** ("take `R` with
`α_z⁻¹ B̄_1 ⊆ B_{R/4}` for all `z ∈ K`"). Deterministic facts about the zoomed map
`ϕ̃ = zoomMap ϕ z r`, the inverse zoom `ψ̃ = zoomPsi ϕ ψ z r`, the local domain
`Ṽ_B = ψ̃(B_{R/2})` and the set `T = ψ̃(∂B_{R/4})`, for `z` in a compact set and `r` small
(`ZoomGeom`, `zoomGeom_of`):

* `Ṽ_B` is open, `ϕ̃(Ṽ_B) = B_{R/2}`, `Ṽ_B ⊆ r⁻¹(V − z)`, so `(ϕ̃, W̃, Ṽ_B)` is a conformal
  neighbourhood;
* `B_1 ⊆ Ṽ_B` and `ϕ̃(B_1) ⊆ B_{R/4}`; `T ⊆ Ṽ_B` and `ϕ̃(T) = ∂B_{R/4}`;
* `B_1 ⊆ c⁻¹ B_{R/2}` (`c = ϕ'(z)`), an open set;
* `zoomMap_eq_inv`: `ϕ̃(u) = Ξinv(c u)` on `B_1` (the zoomed map is the inverse near-identity
  extension after the rotation-dilation by `c`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace SmallGammaGeodesics.CC

open LQGMetric

/-- **The zoom geometry at `(z, r)`** (D10). -/
structure ZoomGeom (ϕ ψ : ℂ → ℂ) (W V : Set ℂ) (z : ℂ) (r R : ℝ) : Prop where
  R_pos : 0 < R
  conf : IsConfNbhd (zoomMap ϕ z r) (zoomSet z r W) (zoomPsi ϕ ψ z r '' ball 0 (R / 2))
  sub : zoomPsi ϕ ψ z r '' ball 0 (R / 2) ⊆ zoomSet z r V
  ball_sub : ball (0 : ℂ) 1 ⊆ zoomPsi ϕ ψ z r '' ball 0 (R / 2)
  T_sub : zoomPsi ϕ ψ z r '' sphere 0 (R / 4) ⊆ zoomPsi ϕ ψ z r '' ball 0 (R / 2)
  map_ball : ∀ u ∈ ball (0 : ℂ) 1, zoomMap ϕ z r u ∈ ball (0 : ℂ) (R / 4)
  map_T : ∀ w ∈ zoomPsi ϕ ψ z r '' sphere 0 (R / 4), zoomMap ϕ z r w ∈ sphere (0 : ℂ) (R / 4)
  T_surj : ∀ w ∈ sphere (0 : ℂ) (R / 4),
    ∃ w' ∈ zoomPsi ϕ ψ z r '' sphere 0 (R / 4), zoomMap ϕ z r w' = w
  image : zoomMap ϕ z r '' (zoomPsi ϕ ψ z r '' ball 0 (R / 2)) = ball 0 (R / 2)
  ad_open : IsOpen ((fun w => deriv ϕ z * w) ⁻¹' ball (0 : ℂ) (R / 2))
  ball_ad : ball (0 : ℂ) 1 ⊆ (fun w => deriv ϕ z * w) ⁻¹' ball (0 : ℂ) (R / 2)

variable {ϕ ψ : ℂ → ℂ} {W V : Set ℂ} {z : ℂ} {r R C : ℝ} {Ξinv : ℂ → ℂ}

/-- `ψ̃(Ξinv(c u)) = u` and `ϕ̃(u) = Ξinv(c u)` for `u ∈ B_1`, when `|c| + C r ≤ R`. -/
theorem zoomPsi_inv_eq (hR : 0 < R) (hZ : IsZoomExt ϕ ψ W z r R C (zoomExt ϕ ψ z r R) Ξinv)
    (hcR : ‖deriv ϕ z‖ + C * r ≤ R) {u : ℂ} (hu : u ∈ ball (0 : ℂ) 1) :
    zoomPsi ϕ ψ z r (Ξinv (deriv ϕ z * u)) = u ∧
      ‖Ξinv (deriv ϕ z * u)‖ ≤ ‖deriv ϕ z‖ + C * r := by
  set c := deriv ϕ z
  have hc := hZ.deriv_ne_zero
  set y := Ξinv (c * u) with hy
  have hnorm : ‖y‖ ≤ ‖c‖ + C * r := by
    have h1 := hZ.inv_norm_sub_le (c * u)
    have h2 : ‖c * u‖ ≤ ‖c‖ := by
      rw [norm_mul]
      have := mem_ball_zero_iff.1 hu
      nlinarith [norm_nonneg c, norm_nonneg u]
    calc ‖y‖ = ‖(y - c * u) + c * u‖ := by rw [sub_add_cancel]
      _ ≤ ‖y - c * u‖ + ‖c * u‖ := norm_add_le _ _
      _ ≤ ‖c‖ + C * r := by linarith
  have hΞ : zoomExt ϕ ψ z r R y = c * u := hZ.nearId.left_inv _
  have hχ : zoomInv ϕ ψ z r y = c * u := by
    rw [← hΞ, zoomExt_eq_zoomInv hR (hnorm.trans hcR)]
  refine ⟨?_, hnorm⟩
  rw [zoomPsi, hχ, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

/-- `ϕ̃(u) = Ξinv(c u)` on `B_1`. -/
theorem zoomMap_eq_inv (hR : 0 < R) (hZ : IsZoomExt ϕ ψ W z r R C (zoomExt ϕ ψ z r R) Ξinv)
    (hcR : ‖deriv ϕ z‖ + C * r ≤ R) {u : ℂ} (hu : u ∈ ball (0 : ℂ) 1) :
    zoomMap ϕ z r u = Ξinv (deriv ϕ z * u) := by
  obtain ⟨h1, h2⟩ := zoomPsi_inv_eq hR hZ hcR hu
  have hy : Ξinv (deriv ϕ z * u) ∈ closedBall (0 : ℂ) (2 * R) :=
    mem_closedBall_zero_iff.2 (h2.trans (by linarith))
  conv_lhs => rw [← h1]
  exact zoomMap_zoomPsi hZ hy

/-- **The zoom geometry** (D10) for `z` with `B(z, ρ_K) ⊆ V`, `m ≤ |ϕ'(z)| ≤ M`, `M + 1 < R/4`,
`C r ≤ 1`, `C r R² ≤ 1` and `r (R/2 + 1) < m ρ_K`. -/
theorem zoomGeom_of (hϕ : IsConfNbhd ϕ W V) (hr : 0 < r) (hR : 0 < R)
    (hZ : IsZoomExt ϕ ψ W z r R C (zoomExt ϕ ψ z r R) Ξinv) {m M ρK : ℝ} (hm : 0 < m)
    (hmc : m ≤ ‖deriv ϕ z‖) (hcM : ‖deriv ϕ z‖ ≤ M) (hMR : M + 1 < R / 4)
    (hCr0 : 0 ≤ C * r) (hCr1 : C * r ≤ 1) (hCrR : C * r * R ^ 2 ≤ 1) (hball : ball z ρK ⊆ V)
    (hrρ : r * (R / 2 + 1) < m * ρK) : ZoomGeom ϕ ψ W V z r R := by
  have hc := hZ.deriv_ne_zero
  have hcpos : 0 < ‖deriv ϕ z‖ := norm_pos_iff.2 hc
  have hB2 : ball (0 : ℂ) (R / 2) ⊆ closedBall 0 (2 * R) :=
    ball_subset_closedBall.trans (closedBall_subset_closedBall (by linarith))
  have hS2 : sphere (0 : ℂ) (R / 4) ⊆ ball 0 (R / 2) := fun w hw =>
    mem_ball_zero_iff.2 (by rw [mem_sphere_zero_iff_norm.1 hw]; linarith)
  have hcR : ‖deriv ϕ z‖ + C * r ≤ R := by linarith
  -- the local domain is open
  have hVo : IsOpen (zoomPsi ϕ ψ z r '' ball 0 (R / 2)) := by
    refine isOpen_image_conf isOpen_ball ?_ ?_
    · intro y hy
      have hy4 : y ∈ ball (0 : ℂ) (4 * R) := ball_subset_ball (by linarith) hy
      exact ((hZ.differentiableOn.differentiableAt (isOpen_ball.mem_nhds hy4)).const_mul
        _).differentiableWithinAt
    · intro y hy y' hy' hyy
      rw [← zoomMap_zoomPsi hZ (hB2 hy), ← zoomMap_zoomPsi hZ (hB2 hy'), hyy]
  -- the local domain lies in `r⁻¹(V − z)`
  have hsub : zoomPsi ϕ ψ z r '' ball 0 (R / 2) ⊆ zoomSet z r V := by
    rintro _ ⟨y, hy, rfl⟩
    rw [mem_zoomSet]
    refine hball (mem_ball.2 ?_)
    rw [dist_eq_norm, add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hr]
    have hyR : ‖y‖ < R / 2 := mem_ball_zero_iff.1 hy
    have hT := hZ.taylor0 y (hB2 hy)
    have hχ : ‖zoomInv ϕ ψ z r y‖ ≤ R / 2 + 1 := by
      have h1 : C * r * ‖y‖ ^ 2 ≤ 1 := by
        have : ‖y‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (by linarith) 2
        nlinarith
      calc ‖zoomInv ϕ ψ z r y‖ = ‖(zoomInv ϕ ψ z r y - y) + y‖ := by rw [sub_add_cancel]
        _ ≤ ‖zoomInv ϕ ψ z r y - y‖ + ‖y‖ := norm_add_le _ _
        _ ≤ R / 2 + 1 := by linarith
    have hψt : ‖zoomPsi ϕ ψ z r y‖ ≤ (R / 2 + 1) / m := by
      rw [zoomPsi, norm_mul, norm_inv, inv_mul_le_iff₀ hcpos]
      calc ‖zoomInv ϕ ψ z r y‖ ≤ R / 2 + 1 := hχ
        _ ≤ ‖deriv ϕ z‖ * ((R / 2 + 1) / m) := by
            rw [mul_div_assoc', le_div_iff₀ hm]
            nlinarith
    calc r * ‖zoomPsi ϕ ψ z r y‖ ≤ r * ((R / 2 + 1) / m) := mul_le_mul_of_nonneg_left hψt hr.le
      _ < ρK := by
          rw [mul_div_assoc', div_lt_iff₀ hm]
          linarith
  refine ⟨hR, (hϕ.zoom z hr.ne').mono hVo hsub, hsub, fun u hu => ?_, image_mono hS2,
    fun u hu => ?_, ?_, fun w hw => ⟨zoomPsi ϕ ψ z r w, mem_image_of_mem _ hw,
      zoomMap_zoomPsi hZ (hB2 (hS2 hw))⟩, ?_, ?_, fun u hu => ?_⟩
  · obtain ⟨h1, h2⟩ := zoomPsi_inv_eq hR hZ hcR hu
    exact ⟨_, mem_ball_zero_iff.2 (lt_of_le_of_lt h2 (by linarith)), h1⟩
  · rw [zoomMap_eq_inv hR hZ hcR hu]
    exact mem_ball_zero_iff.2 (lt_of_le_of_lt (zoomPsi_inv_eq hR hZ hcR hu).2 (by linarith))
  · rintro _ ⟨w, hw, rfl⟩
    rw [zoomMap_zoomPsi hZ (hB2 (hS2 hw))]
    exact hw
  · rw [image_image]
    exact (image_congr fun y hy => zoomMap_zoomPsi hZ (hB2 hy)).trans (image_id _)
  · exact isOpen_ball.preimage (continuous_const.mul continuous_id)
  · show deriv ϕ z * u ∈ ball (0 : ℂ) (R / 2)
    rw [mem_ball_zero_iff, norm_mul]
    have := mem_ball_zero_iff.1 hu
    nlinarith [norm_nonneg u]

end SmallGammaGeodesics.CC
