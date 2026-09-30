import QuantumZipper.Proofs.Thm18.A1RSLip

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A1RS (12): the pointwise parameter coupling of the smeared loops

The members of the smeared-loop family `a1rfNu W t left d s ρ` (A1RFSmear.lean) at two parameter
points `(t, d, s)` and `(t + h, d', s')` are coupled at the same angles `(θ₁, θ₂)`: the side-circle
points `w = fold(d + s e^{iθ₁})`, `w' = fold(d' + s' e^{iθ₁})` (`‖w − w'‖ ≤ ‖d − d'‖ + |s − s'|`),
pushed to `Φ_t(w)`, `Φ_{t+h}(w')` (`Φ_t = f_t ∘ ψ`), smoothed to
`U = fold(Φ_t(w) + ρ e^{iθ₂})`, `U' = fold(Φ_{t+h}(w') + ρ e^{iθ₂})` and pulled back by
`f_t⁻¹`, `f_{t+h}⁻¹`. **`norm_smear_param_le`**: off the strips `{Im w ≤ τ₁}`, `{Im U ≤ τ}` (and
the same for the primed points)

`τ ‖f_t⁻¹ U − f_{t+h}⁻¹ U'‖ ≤ √(R_h² + 4t) (2B/τ₁ ‖w − w'‖ + 24ε + 8√h) + √((R_h + D)² + 4t) D`,

`D = 3ε + 6√h`, `ε` the oscillation of the driver on `[t, t + h]`, `B` a bound of `Φ_t` on
`ℍ ∩ ball 0 (R+1)`, `R_h` a bound of the heights. Inputs: Cauchy–Lipschitz for `Φ_t`
(`norm_sub_le_of_holo_bdd`), the uniform time displacement of `Φ` (`norm_sidePush_add_sub_le`),
the two-point upper bound for `f_t⁻¹` (`norm_fwdMapInv_sub_mul_le`) and the time displacement of
`f_t⁻¹` (`norm_fwdMapInv_add_sub_mul_le`). All bounds are polynomial in `1/τ`, `1/τ₁`, so with
`τ, τ₁` small powers of the parameter increment they give a power modulus of the Neumann energy
(`abs_kernelCov2_map_le`). Own elementary argument.
-/

noncomputable section

open MeasureTheory Set Filter Metric Complex
open scoped Topology ENNReal

namespace QuantumZipper
namespace R18
namespace A1RS

open Thm18Asm

theorem circleMap_sub_circleMap_center (c c' : ℂ) (ρ θ : ℝ) :
    circleMap c ρ θ - circleMap c' ρ θ = c - c' := by
  simp only [circleMap]; ring

/-- **Pointwise parameter coupling of the smeared loops.** -/
theorem norm_smear_param_le {W : ℝ → ℝ} (hG : G1zDrvGood W) (left : Bool) {t h ε τ τ₁ R B Rh ρ θ : ℝ}
    (ht : 0 < t) (hh : 0 ≤ h)
    (hosc1 : ∀ r ∈ Icc (0 : ℝ) h, |W (t + r) - W t| ≤ ε)
    (hosc2 : ∀ q ∈ Icc (0 : ℝ) h, |W (t + h - q) - W (t + h)| ≤ ε)
    (hB : ∀ z ∈ H, ‖z‖ < R + 1 → ‖fwdMap W t (g1zSideMap left W z)‖ ≤ B)
    (hτ : 0 < τ) (hτ₁ : 0 < τ₁) (hτ₁1 : τ₁ ≤ 1) {w w' : ℂ} (hw : τ₁ ≤ w.im) (hw' : τ₁ ≤ w'.im)
    (hwR : ‖w‖ ≤ R) (hwR' : ‖w'‖ ≤ R)
    (hU : τ ≤ (foldH (circleMap (fwdMap W t (g1zSideMap left W w)) ρ θ)).im)
    (hU' : τ ≤ (foldH (circleMap (fwdMap W (t + h) (g1zSideMap left W w')) ρ θ)).im)
    (hUR : (foldH (circleMap (fwdMap W t (g1zSideMap left W w)) ρ θ)).im ≤ Rh)
    (hUR' : (foldH (circleMap (fwdMap W (t + h) (g1zSideMap left W w')) ρ θ)).im ≤ Rh) :
    τ * ‖fwdMapInv W t (foldH (circleMap (fwdMap W t (g1zSideMap left W w)) ρ θ)) -
        fwdMapInv W (t + h) (foldH (circleMap (fwdMap W (t + h) (g1zSideMap left W w')) ρ θ))‖ ≤
      Real.sqrt (Rh ^ 2 + 4 * t) * (2 * B / τ₁ * ‖w - w'‖ + (24 * ε + 8 * Real.sqrt h)) +
        Real.sqrt ((Rh + (3 * ε + 6 * Real.sqrt h)) ^ 2 + 4 * t) * (3 * ε + 6 * Real.sqrt h) := by
  set Φ : ℝ → ℂ → ℂ := fun s z => fwdMap W s (g1zSideMap left W z) with hΦ
  set U := foldH (circleMap (Φ t w) ρ θ) with hUdef
  set U' := foldH (circleMap (Φ (t + h) w') ρ θ) with hU'def
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans (hosc1 0 ⟨le_rfl, hh⟩)
  have hD0 : 0 ≤ 3 * ε + 6 * Real.sqrt h := by positivity
  have hw0 : w ∈ H := show 0 < w.im by linarith
  have hw0' : w' ∈ H := show 0 < w'.im by linarith
  -- space part
  have hd := (A1R.sidePush_props hG ht left).1
  have hlip := norm_sub_le_of_holo_bdd hd hB hτ₁ hτ₁1 hw hw' hwR hwR'
  -- time part of the pushing map
  have htime : ‖Φ t w' - Φ (t + h) w'‖ ≤ 24 * ε + 8 * Real.sqrt h := by
    rcases eq_or_lt_of_le hh with h0 | hpos
    · subst h0
      simp only [add_zero, sub_self, norm_zero, Real.sqrt_zero, mul_zero]
      positivity
    · rw [norm_sub_rev]
      exact norm_sidePush_add_sub_le hG ht.le hpos hosc1 left hw0'
  have hUU : ‖U - U'‖ ≤ 2 * B / τ₁ * ‖w - w'‖ + (24 * ε + 8 * Real.sqrt h) := by
    refine (TwoPoint.norm_foldH_sub_le _ _).trans ?_
    rw [circleMap_sub_circleMap_center]
    calc ‖Φ t w - Φ (t + h) w'‖ ≤ ‖Φ t w - Φ t w'‖ + ‖Φ t w' - Φ (t + h) w'‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ _ := add_le_add hlip htime
  have h1 := norm_fwdMapInv_sub_mul_le hG.1 hG.2.1 ht.le hτ hU hU' hUR hUR'
  have h2 : τ * ‖fwdMapInv W t U' - fwdMapInv W (t + h) U'‖ ≤
      Real.sqrt ((Rh + (3 * ε + 6 * Real.sqrt h)) ^ 2 + 4 * t) * (3 * ε + 6 * Real.sqrt h) := by
    rcases eq_or_lt_of_le hh with h0 | hpos
    · subst h0
      simp only [add_zero, sub_self, norm_zero, mul_zero]
      positivity
    · rw [norm_sub_rev]
      exact norm_fwdMapInv_add_sub_mul_le hG.1 hG.2.1 ht.le hpos hosc2 hτ hU' hUR'
  have hsplit : ‖fwdMapInv W t U - fwdMapInv W (t + h) U'‖ ≤
      ‖fwdMapInv W t U - fwdMapInv W t U'‖ + ‖fwdMapInv W t U' - fwdMapInv W (t + h) U'‖ :=
    norm_sub_le_norm_sub_add_norm_sub _ _ _
  have h1' : τ * ‖fwdMapInv W t U - fwdMapInv W t U'‖ ≤
      Real.sqrt (Rh ^ 2 + 4 * t) * (2 * B / τ₁ * ‖w - w'‖ + (24 * ε + 8 * Real.sqrt h)) :=
    h1.trans (mul_le_mul_of_nonneg_left hUU (Real.sqrt_nonneg _))
  calc τ * ‖fwdMapInv W t U - fwdMapInv W (t + h) U'‖
      ≤ τ * (‖fwdMapInv W t U - fwdMapInv W t U'‖ +
          ‖fwdMapInv W t U' - fwdMapInv W (t + h) U'‖) :=
        mul_le_mul_of_nonneg_left hsplit hτ.le
    _ ≤ _ := by rw [mul_add]; exact add_le_add h1' h2

end A1RS
end R18
end QuantumZipper
