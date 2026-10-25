import SupercriticalLQGUniqueness.B2.PfeLocal.L1Geom
import SupercriticalLQGUniqueness.B2.DG20Pt.FieldComparison
import LQGMetric.Papers.DDDF.P18Scale
import LQGMetric.Papers.DDDF.P16Law

 











set_option autoImplicit false
noncomputable section

open Set Metric
open scoped ENNReal
open LQGMetric LQGMetric.DDDF

namespace SupercriticalLQGUniqueness.B2.PfeLocal

 
def l1AcrossUnit (ξ : ℝ) (b : Set.Ioi (0 : ℝ)) (ψ : C(ℂ, ℝ)) (i : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (b : ℝ)⁻¹ *
    crossLenIn ξ ψ (closedBall i l1d) (sphere i (l1d / 16)) (sphere i (3 * l1d / 4))

theorem l1_dist_affine (z : ℂ) {r : ℝ} (hr : 0 < r) (u v : ℂ) :
    dist (z + (r : ℂ) * u) (z + (r : ℂ) * v) = r * dist u v := by
  rw [dist_eq_norm, dist_eq_norm, show z + (r : ℂ) * u - (z + (r : ℂ) * v) =
    (r : ℂ) * (u - v) by ring, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]

theorem l1_affine_surj (z : ℂ) {r : ℝ} (hr : 0 < r) (w : ℂ) :
    z + (r : ℂ) * ((w - z) / r) = w := by
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  field_simp; ring

theorem l1_image_closedBall (z : ℂ) {r : ℝ} (hr : 0 < r) (i : ℂ) (d : ℝ) :
    (fun u => z + (r : ℂ) * u) '' closedBall i d = closedBall (z + (r : ℂ) * i) (r * d) := by
  ext w
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [mem_closedBall, l1_dist_affine z hr]
    exact mul_le_mul_of_nonneg_left (mem_closedBall.1 hu) hr.le
  · intro hw
    refine ⟨(w - z) / r, ?_, l1_affine_surj z hr w⟩
    rw [mem_closedBall]
    have := mem_closedBall.1 hw
    rw [← l1_affine_surj z hr w, l1_dist_affine z hr] at this
    exact le_of_mul_le_mul_left this hr

theorem l1_image_sphere (z : ℂ) {r : ℝ} (hr : 0 < r) (i : ℂ) (d : ℝ) :
    (fun u => z + (r : ℂ) * u) '' sphere i d = sphere (z + (r : ℂ) * i) (r * d) := by
  ext w
  constructor
  · rintro ⟨u, hu, rfl⟩
    rw [mem_sphere, l1_dist_affine z hr, mem_sphere.1 hu]
  · intro hw
    refine ⟨(w - z) / r, ?_, l1_affine_surj z hr w⟩
    rw [mem_sphere]
    have := mem_sphere.1 hw
    rw [← l1_affine_surj z hr w, l1_dist_affine z hr] at this
    exact mul_left_cancel₀ hr.ne' this

 
theorem l1_crossLenIn_affine (ξ : ℝ) (φ ψ : ℂ → ℝ) (z : ℂ) {r : ℝ} (hr : 0 < r) (c : ℝ)
    (hψ : ∀ u, φ (z + (r : ℂ) * u) = ψ u + c) (S K₁ K₂ : Set ℂ) :
    crossLenIn ξ φ ((fun u => z + (r : ℂ) * u) '' S) ((fun u => z + (r : ℂ) * u) '' K₁)
        ((fun u => z + (r : ℂ) * u) '' K₂) =
      ENNReal.ofReal r * (ENNReal.ofReal (Real.exp (ξ * c)) * crossLenIn ξ ψ S K₁ K₂) := by
  have e : ∀ T : Set ℂ, (fun u => z + (r : ℂ) * u) '' T =
      (· + z) '' ((fun u => (r : ℂ) * u) '' T) := by
    intro T; rw [image_image]; congr 1; funext u; ring
  rw [e, e, e, crossLenIn_image_add, crossLenIn_image_mul ξ _ _ _ _ hr]
  have hf : (fun x => (fun x => φ (x + z)) ((r : ℂ) * x)) = fun x => ψ x + c := by
    funext x
    simp only
    rw [add_comm]
    exact hψ x
  rw [hf, B2.DG20Pt.crossLenIn_add_const]

theorem l1_ennreal_scale (x y w u v : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (_hw : 0 ≤ w)
    (hu : 0 ≤ u) (_hv : 0 ≤ v) (h : x * y * w = u * v) (X : ℝ≥0∞) :
    ENNReal.ofReal x * (ENNReal.ofReal y * (ENNReal.ofReal w * X)) =
      ENNReal.ofReal u * (ENNReal.ofReal v * X) := by
  rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul hx, ← ENNReal.ofReal_mul (by positivity),
    ← mul_assoc, ← ENNReal.ofReal_mul hu, h]

 
theorem l1_acrossCost_scale (ξ : ℝ) (a b : Set.Ioi (0 : ℝ)) (φ ψ : C(ℂ, ℝ)) (z : ℂ)
    {r : ℝ} (hr : 0 < r) (c : ℝ) (hψ : ∀ u, φ (z + (r : ℂ) * u) = ψ u + c) (i : ℂ) :
    l1AcrossCost ξ a φ z r i =
      ENNReal.ofReal (r * b / a * Real.exp (ξ * c)) * l1AcrossUnit ξ b ψ i := by
  have ha : (0 : ℝ) < a := a.2
  have hb : (0 : ℝ) < b := b.2
  unfold l1AcrossCost l1AcrossUnit
  rw [show r * l1d / 16 = r * (l1d / 16) by ring, show 3 * (r * l1d) / 4 = r * (3 * l1d / 4) by ring,
    ← l1_image_closedBall z hr, ← l1_image_sphere z hr, ← l1_image_sphere z hr,
    l1_crossLenIn_affine ξ φ ψ z hr c hψ]
  refine l1_ennreal_scale _ _ _ _ _ (inv_nonneg.2 ha.le) hr.le (Real.exp_pos _).le
    (by positivity) (inv_nonneg.2 hb.le) ?_ _
  field_simp

 
theorem l1_aroundCost_scale (ξ : ℝ) (a b : Set.Ioi (0 : ℝ)) (φ ψ : C(ℂ, ℝ)) (z : ℂ)
    {r : ℝ} (hr : 0 < r) (c : ℝ) (hψ : ∀ u, φ (z + (r : ℂ) * u) = ψ u + c) (k : Fin 4) :
    l1AroundCost ξ a φ z r k =
      ENNReal.ofReal (r * b / a * Real.exp (ξ * c)) * l1AroundCost ξ b ψ 0 1 k := by
  have ha : (0 : ℝ) < a := a.2
  have hb : (0 : ℝ) < b := b.2
  unfold l1AroundCost
  rw [← l1_image_aroundOpen z hr, ← l1_image_start z hr, ← l1_image_end z hr,
    show ({z + (r : ℂ) * l1Start 0 1 k} : Set ℂ) =
      (fun u => z + (r : ℂ) * u) '' {l1Start 0 1 k} by rw [image_singleton],
    show ({z + (r : ℂ) * l1End 0 1 k} : Set ℂ) =
      (fun u => z + (r : ℂ) * u) '' {l1End 0 1 k} by rw [image_singleton],
    l1_crossLenIn_affine ξ φ ψ z hr c hψ]
  refine l1_ennreal_scale _ _ _ _ _ (inv_nonneg.2 ha.le) hr.le (Real.exp_pos _).le
    (by positivity) (inv_nonneg.2 hb.le) ?_ _
  field_simp

end SupercriticalLQGUniqueness.B2.PfeLocal
