import SupercriticalConformalCovariance.BiLip.FieldId
import SupercriticalConformalCovariance.BiLip.Round

/-!
# Lemma 2.1, step 2: deterministic consequences of the geometry at `(z, r)`

* `log_deriv_inv_bound`: the log-derivative correction of l. 120–122: on `B̄_{3ρ}(φ z)`,
  `|log |(φ⁻¹)′(y)| + log |φ′(z)|| ≤ 2ε`;
* `ballO_subset_image`, `preimage_mem_ball`, `ballO_zero_subset_normMap_image`: the inclusions consumed
  by the field identity `rescaled_restrict_eq`.
-/

set_option autoImplicit false

noncomputable section

open Set Metric Filter Topology

namespace SupercriticalConformalCovariance.BiLip

variable {φ : ℂ → ℂ} {U : Set ℂ} {z : ℂ} {r ε : ℝ}

theorem abs_log_le_of_norm_sub_one_le {q : ℂ} (hε : ε ≤ 1 / 2) (hq : ‖q - 1‖ ≤ ε) :
    |Real.log ‖q‖| ≤ 2 * ε := by
  have hε0 : 0 ≤ ε := le_trans (norm_nonneg _) hq
  have h1 : ‖q‖ ≤ 1 + ε := by
    have := norm_le_norm_add_norm_sub' q 1
    calc ‖q‖ = ‖1 + (q - 1)‖ := by ring_nf
      _ ≤ ‖(1 : ℂ)‖ + ‖q - 1‖ := norm_add_le _ _
      _ ≤ 1 + ε := by rw [norm_one]; linarith
  have h2 : 1 - ε ≤ ‖q‖ := by
    have h := norm_sub_norm_le (1 : ℂ) q
    rw [norm_one, norm_sub_rev] at h
    linarith
  have hqpos : 0 < ‖q‖ := by linarith
  rw [abs_le]
  constructor
  · -- `log ‖q‖ ≥ 1 − 1/‖q‖ ≥ −ε/(1−ε) ≥ −2ε`
    have hlog := Real.one_sub_inv_le_log_of_pos hqpos
    have : 1 - ‖q‖⁻¹ ≥ -(2 * ε) := by
      rw [ge_iff_le, sub_eq_add_neg, ← sub_le_iff_le_add', show -(2 * ε) - 1 = -(1 + 2 * ε) by ring,
        neg_le_neg_iff]
      rw [inv_le_comm₀ hqpos (by linarith)]
      have : (1 + 2 * ε)⁻¹ ≤ 1 - ε := by
        rw [inv_le_iff_one_le_mul₀ (by linarith)]
        nlinarith
      linarith
    linarith
  · have := Real.log_le_sub_one_of_pos hqpos
    linarith

/-- **The log-derivative correction** on `B̄_{3ρ}(φ z)`. -/
theorem log_deriv_inv_bound (hG : GeomGood φ U z r ε) (hε : ε ≤ 1 / 2) (hU : IsOpen U)
    (hd : DifferentiableOn ℂ φ U) (hinj : InjOn φ U) {y : ℂ}
    (hy : y ∈ closedBall (φ z) (3 * (r * ‖deriv φ z‖))) :
    |Real.log ‖deriv (Function.invFunOn φ U) y‖ + Real.log ‖deriv φ z‖| ≤ 2 * ε := by
  obtain ⟨hxB, hφx, -, -, hdx⟩ := geom_inv hG hinj hy
  set x := Function.invFunOn φ U y with hx
  have hxU : x ∈ U := hG.2.2.1 hxB
  have hφx' : deriv φ x ≠ 0 := QuantumZipper.CA.Koebe.deriv_ne_zero_of_injOn hU hd hinj hxU
  have hder := QuantumZipper.CA.Koebe.hasDerivAt_invFunOn_of_injOn hU hd hinj hxU
  rw [hφx] at hder
  rw [hder.deriv, norm_inv, Real.log_inv]
  have hq := abs_log_le_of_norm_sub_one_le hε hdx
  rw [norm_div, Real.log_div (norm_ne_zero_iff.2 hG.2.1) (norm_ne_zero_iff.2 hφx')] at hq
  rw [show -Real.log ‖deriv φ x‖ + Real.log ‖deriv φ z‖ =
    Real.log ‖deriv φ z‖ - Real.log ‖deriv φ x‖ by ring]
  exact hq

theorem ballO_subset_image (hG : GeomGood φ U z r ε) (hinj : InjOn φ U) :
    (ballO (φ z) (3 * (r * ‖deriv φ z‖)) : Set ℂ) ⊆ φ '' U := by
  intro y hy
  obtain ⟨hxB, hφx, -⟩ := geom_inv hG hinj (ball_subset_closedBall hy)
  exact ⟨_, hG.2.2.1 hxB, hφx⟩

theorem preimage_mem_ball (hG : GeomGood φ U z r ε) (hinj : InjOn φ U) {s : ℝ} (h4 : 4 * r < s)
    {x : ℂ} (hxU : x ∈ U) (hx : φ x ∈ ball (φ z) (3 * (r * ‖deriv φ z‖))) : x ∈ ball z s := by
  obtain ⟨hxB, hφx, -⟩ := geom_inv hG hinj (ball_subset_closedBall hx)
  have hψ : Function.invFunOn φ U (φ x) = x := hinj.leftInvOn_invFunOn hxU
  rw [hψ] at hxB
  exact closedBall_subset_ball h4 hxB

theorem ballO_zero_subset_normMap_image (hG : GeomGood φ U z r ε) (hinj : InjOn φ U) {s : ℝ}
    (h4 : 4 * r < s) : (ballO 0 3 : Set ℂ) ⊆ normMap φ z r '' ball 0 (s / r) := by
  have hr := hG.1
  have hφd := hG.2.1
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have ha : (r : ℂ) * deriv φ z ≠ 0 := mul_ne_zero hrC hφd
  intro w hw
  have hw3 : ‖w‖ < 3 := by simpa [ballO] using hw
  set y := φ z + ((r : ℂ) * deriv φ z) * w with hy
  have hyB : y ∈ closedBall (φ z) (3 * (r * ‖deriv φ z‖)) := by
    rw [mem_closedBall, dist_eq_norm, hy, add_sub_cancel_left, norm_mul, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
    have : 0 < r * ‖deriv φ z‖ := mul_pos hr (norm_pos_iff.2 hφd)
    nlinarith [norm_nonneg w]
  obtain ⟨hxB, hφx, -⟩ := geom_inv hG hinj hyB
  set x := Function.invFunOn φ U y with hx
  refine ⟨(x - z) / r, ?_, ?_⟩
  · rw [mem_ball, dist_zero_right, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr,
      div_lt_div_iff_of_pos_right hr, ← dist_eq_norm]
    exact lt_of_le_of_lt (mem_closedBall.1 hxB) h4
  · have hxw : z + (r : ℂ) * ((x - z) / r) = x := by field_simp; ring
    rw [normMap, hxw, hφx, hy]
    field_simp
    ring

end SupercriticalConformalCovariance.BiLip
