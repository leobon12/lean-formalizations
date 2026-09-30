import QuantumZipper.Proofs.Zipper.SWCoreB7bAvg

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-B7b-WT (1): deterministic estimates for the `𝔥₀` weight

Task SWC-B7b-WT (decision D64). Deterministic inputs for the weighted transport of
`𝔥₀ + X`, `𝔥₀ = (2/√κ) log|·|`:

* `h0cut_abs_sub_le` — the cut-off `h0cut κ c` is `|2/√κ|/c`-Lipschitz;
* `h0avg_push_close` — the average of `𝔥₀` over a pushed semicircle `fc(t,r).map ψ` is within
  `|2/√κ|/(c₀/2) · (4M/ρ) · r` of `𝔥₀(ψ t)` (cut off at `c₀/2`), for class maps staying at
  distance `≥ c₀` from `0`;
* `abs_exp_sub_exp_le` — `|eˣ − eʸ| ≤ 2 eʸ |x − y|` for `|x − y| ≤ 1`.

Own elementary proofs (cost rule of AGENT_GUIDE): mean-value inequality with the Cauchy bound
`norm_deriv_le_of_class`, and `log x − log y ≤ x/y − 1`.
-/

noncomputable section

open MeasureTheory Filter Set Metric Function
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace SWCore

open Thm18Asm.G1RC

/-- `h0cut κ c` is Lipschitz with constant `|2/√κ| / c`. -/
theorem h0cut_abs_sub_le (κ : ℝ) {c : ℝ} (hc : 0 < c) (z w : ℂ) :
    |h0cut κ c z - h0cut κ c w| ≤ |2 / Real.sqrt κ| / c * ‖z - w‖ := by
  have key : ∀ x y : ℝ, c ≤ x → c ≤ y → Real.log x - Real.log y ≤ |x - y| / c := by
    intro x y hx hy
    have hx0 : 0 < x := lt_of_lt_of_le hc hx
    have hy0 : 0 < y := lt_of_lt_of_le hc hy
    have h1 := Real.log_le_sub_one_of_pos (div_pos hx0 hy0)
    rw [Real.log_div hx0.ne' hy0.ne'] at h1
    have e : x / y - 1 = (x - y) / y := by field_simp
    rw [e] at h1
    have h2 : (x - y) / y ≤ |x - y| / c :=
      calc (x - y) / y ≤ |x - y| / y := div_le_div_of_nonneg_right (le_abs_self _) hy0.le
        _ ≤ |x - y| / c := div_le_div_of_nonneg_left (abs_nonneg _) hc hy
    linarith
  set x := max ‖z‖ c
  set y := max ‖w‖ c
  have hx : c ≤ x := le_max_right _ _
  have hy : c ≤ y := le_max_right _ _
  have hxy : |x - y| ≤ ‖z - w‖ :=
    (abs_max_sub_max_le_abs _ _ _).trans (abs_norm_sub_norm_le z w)
  have hl : |Real.log x - Real.log y| ≤ |x - y| / c := by
    rw [abs_le]
    constructor
    · have := key y x hy hx
      rw [abs_sub_comm] at this
      linarith
    · exact key x y hx hy
  have e : h0cut κ c z - h0cut κ c w = 2 / Real.sqrt κ * (Real.log x - Real.log y) := by
    simp only [h0cut, x, y]; ring
  rw [e, abs_mul]
  calc |2 / Real.sqrt κ| * |Real.log x - Real.log y|
      ≤ |2 / Real.sqrt κ| * (‖z - w‖ / c) :=
        mul_le_mul_of_nonneg_left (hl.trans (div_le_div_of_nonneg_right hxy hc.le))
          (abs_nonneg _)
    _ = |2 / Real.sqrt κ| / c * ‖z - w‖ := by ring

/-- `|eˣ − eʸ| ≤ 2 eʸ |x − y|` when `|x − y| ≤ 1`. -/
theorem abs_exp_sub_exp_le {x y : ℝ} (h : |x - y| ≤ 1) :
    |Real.exp x - Real.exp y| ≤ 2 * Real.exp y * |x - y| := by
  have e : Real.exp x - Real.exp y = Real.exp y * (Real.exp (x - y) - 1) := by
    rw [Real.exp_sub]; field_simp
  rw [e, abs_mul, abs_of_pos (Real.exp_pos y)]
  have := Real.abs_exp_sub_one_le h
  nlinarith [Real.exp_pos y]

variable {a b ρ M m : ℝ} {ψ : ℂ → ℂ}

/-- **The `𝔥₀`-average over a pushed semicircle is close to `𝔥₀(ψ t)`.** -/
theorem h0avg_push_close (κ : ℝ) (hψ : ψ ∈ BdryClass a b ρ M m) (hρ : 0 < ρ) {c₀ : ℝ}
    (hc₀ : 0 < c₀) (hsep : ∀ z ∈ thickening ρ (segC a b), c₀ ≤ ‖ψ z‖) {t r : ℝ}
    (ht : t ∈ Icc a b) (hr : 0 < r) (hrρ : r < ρ / 2) :
    |(∫ w, h0rev κ w ∂((foldedCircle (t : ℂ) r).map ψ)) - h0cut κ (c₀ / 2) (ψ t)| ≤
      |2 / Real.sqrt κ| / (c₀ / 2) * (4 * M / ρ * r) := by
  have hball2 : closedBall (t : ℂ) r ⊆ thickening (ρ / 2) (segC a b) :=
    swcN2_ball_sub_thick ht hrρ
  have hball : closedBall (t : ℂ) r ⊆ thickening ρ (segC a b) :=
    swcN2_ball_sub_thick ht (by linarith)
  have hψc : ContinuousOn ψ (thickening ρ (segC a b)) := hψ.1.continuousOn
  have hpt : ∀ θ, foldH (circleMap (t : ℂ) r θ) ∈ closedBall (t : ℂ) r :=
    swcN2_fold_circle_mem hr.le
  set D : ℝ := |2 / Real.sqrt κ| / (c₀ / 2) * (4 * M / ρ * r) with hD
  set c : ℝ := h0cut κ (c₀ / 2) (ψ t) with hc
  set F : ℝ → ℝ := fun θ => h0cut κ (c₀ / 2) (ψ (foldH (circleMap (t : ℂ) r θ))) with hF
  have hgc : Continuous fun θ : ℝ => ψ (foldH (circleMap (t : ℂ) r θ)) :=
    (hψc.mono hball).comp_continuous
      (CircleFubini.continuous_foldH'.comp (continuous_circleMap _ _)) hpt
  have hrep : ∫ w, h0rev κ w ∂((foldedCircle (t : ℂ) r).map ψ) = ∫ θ, F θ ∂circM := by
    rw [swcN2_fc_map_eq hr.le (hψc.mono hball)]
    rw [integral_map hgc.measurable.aemeasurable]
    · refine integral_congr_ae (Eventually.of_forall fun θ => ?_)
      simp only [hF]
      exact (h0cut_eq (le_trans (by linarith) (hsep _ (hball (hpt θ))))).symm
    · exact (measurable_const.mul (Real.measurable_log.comp measurable_norm)).aestronglyMeasurable
  -- pointwise closeness
  have hpw : ∀ θ, |F θ - c| ≤ D := by
    intro θ
    have hmv : ‖ψ (foldH (circleMap (t : ℂ) r θ)) - ψ t‖ ≤
        4 * M / ρ * ‖foldH (circleMap (t : ℂ) r θ) - t‖ :=
      (convex_closedBall (t : ℂ) r).norm_image_sub_le_of_norm_deriv_le
        (fun z hz => hψ.1.differentiableAt (isOpen_thickening.mem_nhds (hball hz)))
        (fun z hz => norm_deriv_le_of_class hψ hρ (hball2 hz))
        (mem_closedBall_self hr.le) (hpt θ)
    have hdist : ‖foldH (circleMap (t : ℂ) r θ) - t‖ ≤ r := by
      have := hpt θ; rwa [mem_closedBall, dist_eq_norm] at this
    have hM0 : 0 ≤ 4 * M / ρ := by
      have := norm_deriv_le_of_class hψ hρ (hball2 (mem_closedBall_self hr.le))
      exact (norm_nonneg _).trans this
    calc |F θ - c| ≤ |2 / Real.sqrt κ| / (c₀ / 2) *
          ‖ψ (foldH (circleMap (t : ℂ) r θ)) - ψ t‖ := h0cut_abs_sub_le κ (by positivity) _ _
      _ ≤ D := by
        rw [hD]
        refine mul_le_mul_of_nonneg_left (hmv.trans ?_) (by positivity)
        exact mul_le_mul_of_nonneg_left hdist hM0
  have hFm : AEStronglyMeasurable F circM :=
    ((continuous_h0cut κ (by positivity)).comp hgc).aestronglyMeasurable
  have hFi : Integrable F circM := by
    refine Integrable.mono' (integrable_const (|c| + D)) hFm (Eventually.of_forall fun θ => ?_)
    rw [Real.norm_eq_abs]
    have := hpw θ
    have h1 := abs_sub_abs_le_abs_sub (F θ) c
    linarith
  rw [hrep]
  have e : ∫ θ, F θ ∂circM - c = ∫ θ, (F θ - c) ∂circM := by
    rw [integral_sub hFi (integrable_const c)]
    simp
  rw [e]
  have := norm_integral_le_of_norm_le_const (μ := circM) (f := fun θ => F θ - c) (C := D)
    (Eventually.of_forall fun θ => by rw [Real.norm_eq_abs]; exact hpw θ)
  rw [Real.norm_eq_abs] at this
  simpa using this

end SWCore
end QuantumZipper
