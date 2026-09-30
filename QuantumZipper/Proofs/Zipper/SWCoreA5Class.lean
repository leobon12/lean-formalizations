import QuantumZipper.Proofs.Zipper.SWCoreDefs
import QuantumZipper.Proofs.GFF.CircleMeanValue
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn
import Mathlib.Analysis.Calculus.FDeriv.Measurable

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-A5-CLASS: deterministic estimates uniform over an area map class

Task SWC-A5-CLASS (helper for SWC-A5). For the class `AreaClass a b c d ρ M m`
(`SWCoreDefs.lean`), with constants depending only on the class parameters:

* `areaClass_deriv_bounds`: Cauchy bounds `‖ψ'‖ ≤ C` and `‖ψ'(u) - ψ'(z)‖ ≤ L ‖u - z‖` on
  `closedBall z r₀`, `z ∈ K = rectC a b c d`;
* `areaClass_ball_subset_image`: quantitative inverse function theorem,
  `closedBall (ψ z) (κ r) ⊆ ψ '' closedBall z r` for `r ≤ r₁`;
* `areaClass_inv_modulus`: its corollary (with injectivity of `ψ` on the thickening);
* `areaClass_logAvg`: `∫ log‖ψ'‖ d fc(z,r)` is uniformly close to `log‖ψ'(z)‖` for small `r`.

Sources: Cauchy estimates and the inverse function theorem are standard (Ahlfors, *Complex
Analysis*, 3rd ed., Ch. 4 §2.3 (Cauchy's estimate) and Ch. 4 §3.3 (local mapping)). Own elementary
proof from mathlib's Cauchy estimate `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`, the mean
value inequality, and mathlib's quantitative inverse function theorem
`ApproximatesLinearOn.surjOn_closedBall_of_nonlinearRightInverse`.
-/

open MeasureTheory Filter Set Metric

namespace QuantumZipper
namespace SWCore

/-- Cauchy estimate on a closed disc inside an open-set domain of holomorphy. -/
theorem swA5_norm_deriv_le {f : ℂ → ℂ} {U : Set ℂ} (hf : DifferentiableOn ℂ f U) {u : ℂ}
    {R B : ℝ} (hR : 0 < R) (hsub : closedBall u R ⊆ U)
    (hB : ∀ v ∈ closedBall u R, ‖f v‖ ≤ B) : ‖deriv f u‖ ≤ B / R := by
  apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR
  · apply DifferentiableOn.diffContOnCl
    rw [closure_ball u hR.ne']
    exact hf.mono hsub
  · intro v hv
    exact hB v (sphere_subset_closedBall hv)

/-- Explicit Cauchy bounds for the class, on `closedBall z (ρ/4)`. -/
theorem swA5_bounds_explicit {a b c d ρ M m : ℝ} (hρ : 0 < ρ) {ψ : ℂ → ℂ}
    (hψ : ψ ∈ AreaClass a b c d ρ M m) {z : ℂ} (hz : z ∈ rectC a b c d) {u : ℂ}
    (hu : u ∈ closedBall z (ρ / 4)) :
    u ∈ thickening ρ (rectC a b c d) ∧ DifferentiableAt ℂ ψ u ∧
      ‖deriv ψ u‖ ≤ 4 * |M| / ρ ∧
      ‖deriv ψ u - deriv ψ z‖ ≤ 16 * |M| / ρ ^ 2 * ‖u - z‖ := by
  obtain ⟨hd, -, hbd, -⟩ := hψ
  set T := thickening ρ (rectC a b c d) with hTdef
  have hTo : IsOpen T := isOpen_thickening
  have hball : ∀ v, dist v z < ρ → v ∈ T := fun v hv =>
    ball_subset_thickening hz ρ (mem_ball.2 hv)
  have hM : ∀ v ∈ T, ‖ψ v‖ ≤ |M| := fun v hv => (hbd v hv).1.trans (le_abs_self M)
  -- first derivative bound on `closedBall z (ρ/2)`
  have hd1 : ∀ v, dist v z ≤ ρ / 2 → ‖deriv ψ v‖ ≤ 4 * |M| / ρ := by
    intro v hv
    have hsub : closedBall v (ρ / 4) ⊆ T := by
      intro w hw
      apply hball
      have := dist_triangle w v z
      rw [mem_closedBall] at hw
      linarith
    have h := swA5_norm_deriv_le hd (by linarith : (0 : ℝ) < ρ / 4) hsub
      (fun w hw => hM w (hsub hw))
    calc ‖deriv ψ v‖ ≤ |M| / (ρ / 4) := h
      _ = 4 * |M| / ρ := by field_simp
  have hd' : DifferentiableOn ℂ (deriv ψ) T := hd.deriv hTo
  have hd2 : ∀ w, dist w z ≤ ρ / 4 → ‖deriv (deriv ψ) w‖ ≤ 16 * |M| / ρ ^ 2 := by
    intro w hw
    have hsub : closedBall w (ρ / 4) ⊆ closedBall z (ρ / 2) := by
      intro v hv
      rw [mem_closedBall] at hv ⊢
      have := dist_triangle v w z
      linarith
    have h := swA5_norm_deriv_le hd' (by linarith : (0 : ℝ) < ρ / 4)
      (hsub.trans fun v hv => hball v (by rw [mem_closedBall] at hv; linarith))
      (fun v hv => hd1 v (hsub hv))
    calc ‖deriv (deriv ψ) w‖ ≤ 4 * |M| / ρ / (ρ / 4) := h
      _ = 16 * |M| / ρ ^ 2 := by field_simp; ring
  have hmemT : ∀ w ∈ closedBall z (ρ / 4), w ∈ T := fun w hw =>
    hball w (by rw [mem_closedBall] at hw; linarith)
  refine ⟨hmemT u hu, hd.differentiableAt (hTo.mem_nhds (hmemT u hu)),
    hd1 u (by rw [mem_closedBall] at hu; linarith), ?_⟩
  exact Convex.norm_image_sub_le_of_norm_deriv_le
    (fun w hw => hd'.differentiableAt (hTo.mem_nhds (hmemT w hw)))
    (fun w hw => hd2 w (mem_closedBall.1 hw)) (convex_closedBall z _)
    (mem_closedBall_self (by linarith)) hu

/-- **(1) Cauchy bounds**, uniform over the class. -/
theorem areaClass_deriv_bounds {a b c d ρ M m : ℝ} (hρ : 0 < ρ) :
    ∃ C L r₀ : ℝ, 0 < C ∧ 0 < L ∧ 0 < r₀ ∧ r₀ < ρ ∧
      ∀ ψ ∈ AreaClass a b c d ρ M m, ∀ z ∈ rectC a b c d,
        ∀ u ∈ Metric.closedBall z r₀, DifferentiableAt ℂ ψ u ∧ ‖deriv ψ u‖ ≤ C ∧
          ‖deriv ψ u - deriv ψ z‖ ≤ L * ‖u - z‖ := by
  refine ⟨4 * |M| / ρ + 1, 16 * |M| / ρ ^ 2 + 1, ρ / 4, by positivity, by positivity,
    by linarith, by linarith, ?_⟩
  intro ψ hψ z hz u hu
  obtain ⟨-, h1, h2, h3⟩ := swA5_bounds_explicit hρ hψ hz hu
  exact ⟨h1, by linarith, h3.trans (by nlinarith [norm_nonneg (u - z)])⟩

/-- **(2) Quantitative inverse function theorem**, uniform over the class. -/
theorem areaClass_ball_subset_image {a b c d ρ M m : ℝ} (hρ : 0 < ρ) (hm : 0 < m) :
    ∃ r₁ κ : ℝ, 0 < r₁ ∧ r₁ < ρ ∧ 0 < κ ∧ ∀ ψ ∈ AreaClass a b c d ρ M m, ∀ z ∈ rectC a b c d,
      ∀ r, 0 < r → r ≤ r₁ → Metric.closedBall (ψ z) (κ * r) ⊆ ψ '' Metric.closedBall z r := by
  set L : ℝ := 16 * |M| / ρ ^ 2 + 1 with hL
  have hL0 : 0 < L := by positivity
  refine ⟨min (ρ / 4) (m / (2 * L)), m / 2, by positivity,
    (min_le_left _ _).trans_lt (by linarith), by positivity, ?_⟩
  intro ψ hψ z hz r hr hr₁
  have hr4 : r ≤ ρ / 4 := hr₁.trans (min_le_left _ _)
  have hLr : L * r ≤ m / 2 := by
    have h := hr₁.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  set A := deriv ψ z with hA
  have hAm : m ≤ ‖A‖ := hψ.2.2.2 z hz
  have hA0 : A ≠ 0 := by
    intro h; rw [h, norm_zero] at hAm; linarith
  have hsub : closedBall z r ⊆ closedBall z (ρ / 4) := closedBall_subset_closedBall hr4
  have hB := fun u (hu : u ∈ closedBall z r) => swA5_bounds_explicit hρ hψ hz (hsub hu)
  -- the linear model `u ↦ A u`
  set f' : ℂ →L[ℂ] ℂ := A • ContinuousLinearMap.id ℂ ℂ with hf'
  have hf'x : ∀ x, f' x = A * x := fun x => by simp [hf']
  let fsymm : f'.NonlinearRightInverse :=
    { toFun := fun y => A⁻¹ * y
      nnnorm := ‖A‖₊⁻¹
      bound' := fun y => by simp [norm_inv]
      right_inv' := fun y => by rw [hf'x]; field_simp }
  have happrox : ApproximatesLinearOn ψ f' (closedBall z r) (Real.toNNReal (L * r)) := by
    intro x hx y hy
    rw [Real.coe_toNNReal _ (by positivity), hf'x]
    have hg : ∀ w ∈ closedBall z r, HasDerivWithinAt (fun u => ψ u - A * u)
        (deriv ψ w - A) (closedBall z r) w := by
      intro w hw
      have h : HasDerivAt (fun u => ψ u - A * u) (deriv ψ w - A * 1) w :=
        (hB w hw).2.1.hasDerivAt.sub ((hasDerivAt_id w).const_mul A)
      rw [mul_one] at h
      exact h.hasDerivWithinAt
    have hbd : ∀ w ∈ closedBall z r, ‖deriv ψ w - A‖ ≤ L * r := by
      intro w hw
      refine (hB w hw).2.2.2.trans ?_
      have : ‖w - z‖ ≤ r := by rw [← dist_eq_norm]; exact mem_closedBall.1 hw
      have h16 : 16 * |M| / ρ ^ 2 ≤ L := by linarith
      nlinarith [norm_nonneg (w - z), show (0 : ℝ) ≤ 16 * |M| / ρ ^ 2 by positivity]
    have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hg hbd (convex_closedBall z r)
      hy hx
    calc ‖ψ x - ψ y - A * (x - y)‖ = ‖(ψ x - A * x) - (ψ y - A * y)‖ := by ring_nf
      _ ≤ L * r * ‖x - y‖ := this
  have hsurj := happrox.surjOn_closedBall_of_nonlinearRightInverse fsymm (ε := r) hr.le
    (b := z) subset_rfl
  have hnn : ((fsymm.nnnorm : ℝ))⁻¹ = ‖A‖ := by
    show ((‖A‖₊⁻¹ : NNReal) : ℝ)⁻¹ = ‖A‖
    simp
  rw [hnn, Real.coe_toNNReal _ (by positivity)] at hsurj
  refine (closedBall_subset_closedBall ?_).trans hsurj
  nlinarith

/-- **(2') Inverse modulus**: corollary of (2) and injectivity on the thickening. -/
theorem areaClass_inv_modulus {a b c d ρ M m : ℝ} (hρ : 0 < ρ) (hm : 0 < m) :
    ∃ r₁ κ : ℝ, 0 < r₁ ∧ 0 < κ ∧ ∀ ψ ∈ AreaClass a b c d ρ M m,
      ∀ z ∈ rectC a b c d, ∀ u ∈ Metric.thickening ρ (rectC a b c d), ∀ r, 0 < r → r ≤ r₁ →
        ‖ψ u - ψ z‖ ≤ κ * r → ‖u - z‖ ≤ r := by
  obtain ⟨r₁, κ, hr₁, hr₁ρ, hκ, H⟩ := areaClass_ball_subset_image (a := a) (b := b) (c := c)
    (d := d) (M := M) hρ hm
  refine ⟨r₁, κ, hr₁, hκ, ?_⟩
  intro ψ hψ z hz u hu r hr hrr h
  have hmem : ψ u ∈ closedBall (ψ z) (κ * r) := by rw [mem_closedBall, dist_eq_norm]; exact h
  obtain ⟨v, hv, hvu⟩ := H ψ hψ z hz r hr hrr hmem
  have hvT : v ∈ thickening ρ (rectC a b c d) := by
    apply ball_subset_thickening hz ρ
    rw [mem_ball]; exact (mem_closedBall.1 hv).trans_lt (hrr.trans_lt hr₁ρ)
  have := hψ.2.1 hvT hu hvu
  subst this
  rw [← dist_eq_norm]; exact mem_closedBall.1 hv

/-- Elementary log estimate. -/
theorem swA5_abs_log_sub_le {x y δ m : ℝ} (hm : 0 < m) (hy : m ≤ y) (hxy : |x - y| ≤ δ)
    (hδ : δ ≤ m / 2) : |Real.log x - Real.log y| ≤ 2 * δ / m := by
  have hy0 : 0 < y := by linarith
  have h1 := abs_sub_le_iff.1 hxy
  have hx0 : 0 < x := by linarith
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans hxy
  rw [abs_sub_le_iff]
  constructor
  · rw [← Real.log_div hx0.ne' hy0.ne']
    refine (Real.log_le_sub_one_of_pos (by positivity)).trans ?_
    rw [div_sub_one hy0.ne', div_le_div_iff₀ hy0 hm]
    nlinarith
  · rw [← Real.log_div hy0.ne' hx0.ne']
    refine (Real.log_le_sub_one_of_pos (by positivity)).trans ?_
    rw [div_sub_one hx0.ne', div_le_div_iff₀ hx0 hm]
    nlinarith

/-- **(3) Log-average estimate**, uniform over the class. -/
theorem areaClass_logAvg {a b c d ρ M m : ℝ} (hc : 0 < c) (hρ : 0 < ρ) (hm : 0 < m) :
    ∀ η : ℝ, 0 < η → ∃ r₂ : ℝ, 0 < r₂ ∧ ∀ ψ ∈ AreaClass a b c d ρ M m, ∀ z ∈ rectC a b c d,
      ∀ r, 0 < r → r ≤ r₂ →
        |∫ w, Real.log ‖deriv ψ w‖ ∂foldedCircle z r - Real.log ‖deriv ψ z‖| ≤ η := by
  intro η hη
  set L : ℝ := 16 * |M| / ρ ^ 2 + 1 with hL
  have hL0 : 0 < L := by positivity
  refine ⟨min (min (ρ / 4) c) (min (m / (2 * L)) (η * m / (2 * L))), by positivity, ?_⟩
  intro ψ hψ z hz r hr hr₂
  have hr4 : r ≤ ρ / 4 := hr₂.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hrc : r ≤ c := hr₂.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hLr : L * r ≤ m / 2 := by
    have h := hr₂.trans ((min_le_right _ _).trans (min_le_left _ _))
    rw [le_div_iff₀ (by positivity)] at h
    linarith
  have hLη : 2 * (L * r) / m ≤ η := by
    have h := hr₂.trans ((min_le_right _ _).trans (min_le_right _ _))
    rw [le_div_iff₀ (by positivity)] at h
    rw [div_le_iff₀ hm]; linarith
  rw [foldedCircle_eq_circleUnif hr.le (hrc.trans hz.2.1)]
  set g : ℂ → ℝ := fun w => Real.log ‖deriv ψ w‖ with hg
  set A := Real.log ‖deriv ψ z‖ with hA
  have hpt : ∀ᵐ w ∂circleUnif z r, |g w - A| ≤ η := by
    filter_upwards [CircleMV.ae_circleUnif z r] with w hw
    rw [abs_of_pos hr] at hw
    have hwb : w ∈ closedBall z (ρ / 4) := by
      rw [mem_closedBall, dist_eq_norm, hw]; exact hr4
    obtain ⟨-, -, -, h3⟩ := swA5_bounds_explicit hρ hψ hz hwb
    have h16 : 16 * |M| / ρ ^ 2 ≤ L := by linarith
    have hdiff : |‖deriv ψ w‖ - ‖deriv ψ z‖| ≤ L * r := by
      refine (abs_norm_sub_norm_le _ _).trans (h3.trans ?_)
      rw [hw]
      nlinarith [show (0 : ℝ) ≤ 16 * |M| / ρ ^ 2 by positivity]
    exact (swA5_abs_log_sub_le hm (hψ.2.2.2 z hz) hdiff hLr).trans hLη
  have hmeas : Measurable g := Real.measurable_log.comp (measurable_deriv ψ).norm
  have hint : Integrable g (circleUnif z r) := by
    refine Integrable.of_bound hmeas.aestronglyMeasurable (|A| + η) ?_
    filter_upwards [hpt] with w hw
    rw [Real.norm_eq_abs]
    have := abs_sub_abs_le_abs_sub (g w) A
    linarith
  have heq : ∫ w, g w ∂circleUnif z r - A = ∫ w, (g w - A) ∂circleUnif z r := by
    rw [integral_sub hint (integrable_const A)]
    simp
  rw [heq]
  have := norm_integral_le_of_norm_le_const (μ := circleUnif z r) (C := η)
    (f := fun w => g w - A) (by simpa [Real.norm_eq_abs] using hpt)
  simpa [Real.norm_eq_abs] using this

end SWCore
end QuantumZipper
