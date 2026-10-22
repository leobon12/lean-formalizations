import HigherDimLQGContinuity.Core.Interfaces
import HigherDimLQGContinuity.Favorable.Prob

/-!
# Uniform lower tail of the unit source distance at an arbitrary pin

The pin-one argument of `p8a_small_prob` applies to the radius-ten law
needed in Step 0 (P2).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

open Set Metric MeasureTheory
open HigherDimLQGMetric
open HigherDimLFPP (Rd e₁)
open scoped ENNReal

/-- The unit-distance lower tail derived from the fixed inverse crossing
moment, for any pin radius covered by Lemma 2.1. -/
theorem q11_small_distance_prob {d : ℕ} (hd : 2 ≤ d) {ξbar s : ℝ}
    (hs : 0 < s) (hU : UniformEstimates d ξbar s) :
    ∃ Kinv : ℝ, 0 < Kinv ∧
      ∀ ξ ∈ Ioc (0 : ℝ) ξbar, ∀ D : DistRd d → ContMetric d,
        IsStrongExpMetric d ξ (distExp d ξ) D → ∀ w : ℝ, 0 < w →
          pinLaw d s {g | (rho D g).1 (0, e₁ d) < w} ≤ ENNReal.ofReal (Kinv * w) := by
  obtain ⟨K, hK⟩ := hU.cross 0 (1 / 4) (1 / 2) 1 (by norm_num) (by norm_num) one_pos
  refine ⟨max K 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro ξ hξ D hD w hw
  have hl := p5b_ae_isLength_rho hd hD hs
  have hX := p5b_aemeasurable_setDistIn_univ hD.measurable (pinLaw d s) hl
    (sphere (0 : Rd d) (1 / 4)) (sphere (0 : Rd d) (1 / 2))
  have hmk := p5b_markov (μ := pinLaw d s)
    (f := fun g => (setDistIn (rho D g) univ (sphere (0 : Rd d) (1 / 4))
      (sphere (0 : Rd d) (1 / 2)))⁻¹ ^ (1 : ℝ))
    (hX.inv.pow_const 1) (inv_pos.mpr hw) (hK ξ hξ D hD)
  have he₁ : ‖e₁ d - 0‖ = 1 := by
    rw [sub_zero]
    exact HigherDimLFPP.norm_e₁ (by omega)
  have hsub : {g | (rho D g).1 (0, e₁ d) < w} ≤ᵐ[pinLaw d s]
      {g | ENNReal.ofReal w⁻¹ ≤ (setDistIn (rho D g) univ (sphere (0 : Rd d) (1 / 4))
        (sphere (0 : Rd d) (1 / 2)))⁻¹ ^ (1 : ℝ)} := by
    filter_upwards [hl] with g hg hlt
    change (rho D g).1 (0, e₁ d) < w at hlt
    have hcr := p8a_setDistIn_le_apply hg (z := 0) (x := 0) (y := e₁ d)
      (r₁ := 1 / 4) (r₂ := 1 / 2)
      (by norm_num) (by rw [sub_zero, norm_zero]; norm_num) (by rw [he₁]; norm_num)
    have hlt' : ENNReal.ofReal ((rho D g).1 (0, e₁ d)) < ENNReal.ofReal w :=
      (ENNReal.ofReal_lt_ofReal_iff hw).mpr hlt
    rw [ENNReal.rpow_one, ENNReal.ofReal_inv_of_pos hw]
    exact ENNReal.inv_le_inv.mpr (hcr.trans hlt'.le)
  calc
    pinLaw d s {g | (rho D g).1 (0, e₁ d) < w} ≤ _ := measure_mono_ae hsub
    _ ≤ ENNReal.ofReal (K / w⁻¹) := hmk
    _ ≤ ENNReal.ofReal (max K 1 * w) := by
      apply ENNReal.ofReal_le_ofReal
      rw [div_inv_eq_mul]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) hw.le

end HigherDimLQGContinuity
