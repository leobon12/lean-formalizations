import QuantumZipper.Proofs.Thm18.ASepModC
import QuantumZipper.Proofs.Thm18.ASepInvLip
import QuantumZipper.Proofs.Zipper.Cor15RezipRegTame

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ASEP (mod D): Frostman bound for the pushed base `σ.map (w ↦ f_τ(a w))`

* `isFrostman_map_of_coLip`: the pushforward of a Frostman probability measure by a map that is
  locally co-Lipschitz on a carrying set is Frostman (same exponent);
* `isFrostman_alphaA`: the base `σ.map (gA …)` of the A-sep family is `1`-Frostman with a
  constant uniform over the parameter box; the co-Lipschitz bound is the inverse-map Lipschitz
  bound (C3) `norm_fwdMapInv_sub_le`, and `σ = fc(d, r)` is `1`-Frostman (`isFrostman_fc`).

Own elementary argument (covering by one ball).
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace QuantumZipper
namespace ASep

/-- **Frostman bound for a locally co-Lipschitz pushforward.** -/
theorem isFrostman_map_of_coLip {σ : Measure ℂ} [IsProbabilityMeasure σ] {g : ℂ → ℂ}
    (hg : Measurable g) {E : Set ℂ} (hE : ∀ᵐ x ∂σ, x ∈ E) {L δ₀ C β : ℝ} (hL : 0 < L)
    (hδ₀ : 0 < δ₀) (hβ : 0 < β) (hC : 0 ≤ C) (hσ : IsFrostman σ β C)
    (hco : ∀ x ∈ E, ∀ y ∈ E, ‖g x - g y‖ ≤ δ₀ → ‖x - y‖ ≤ L * ‖g x - g y‖) :
    IsFrostman (σ.map g) β (C * (2 * L) ^ β + (2 / δ₀) ^ β) := by
  intro w s hs
  rw [Measure.map_apply hg measurableSet_closedBall]
  have hA : 0 ≤ C * (2 * L) ^ β * s ^ β := by positivity
  have hB : 0 ≤ (2 / δ₀) ^ β * s ^ β := by positivity
  rw [add_mul]
  by_cases hsmall : 2 * s ≤ δ₀
  · by_cases hne : ∃ x₁ ∈ E, g x₁ ∈ closedBall w s
    · obtain ⟨x₁, hx₁E, hx₁⟩ := hne
      have hsub : g ⁻¹' closedBall w s ≤ᵐ[σ] closedBall x₁ (2 * L * s) := by
        filter_upwards [hE] with x hxE hx
        have hx' : g x ∈ closedBall w s := hx
        rw [mem_closedBall, dist_eq_norm] at hx' hx₁ ⊢
        have h2 : ‖g x - g x₁‖ ≤ 2 * s := by
          calc ‖g x - g x₁‖ = ‖(g x - w) - (g x₁ - w)‖ := by ring_nf
            _ ≤ ‖g x - w‖ + ‖g x₁ - w‖ := norm_sub_le _ _
            _ ≤ 2 * s := by linarith
        have := hco x hxE x₁ hx₁E (h2.trans hsmall)
        calc ‖x - x₁‖ ≤ L * ‖g x - g x₁‖ := this
          _ ≤ L * (2 * s) := mul_le_mul_of_nonneg_left h2 hL.le
          _ = 2 * L * s := by ring
      have h1 := ENNReal.toReal_mono (measure_ne_top σ _) (measure_mono_ae hsub)
      refine (h1.trans (hσ x₁ _ (by positivity))).trans ?_
      rw [Real.mul_rpow (by positivity) hs.le, ← mul_assoc]
      linarith
    · push Not at hne
      have hsub : g ⁻¹' closedBall w s ≤ᵐ[σ] (∅ : Set ℂ) := by
        filter_upwards [hE] with x hxE hx
        exact hne x hxE hx
      have h0 : σ (g ⁻¹' closedBall w s) = 0 :=
        le_antisymm ((measure_mono_ae hsub).trans (by simp)) bot_le
      rw [h0, ENNReal.toReal_zero]
      linarith
  · push Not at hsmall
    have h1 : (σ (g ⁻¹' closedBall w s)).toReal ≤ 1 := by
      have := prob_le_one (μ := σ) (s := g ⁻¹' closedBall w s)
      exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using this)
    have h2 : 1 ≤ (2 / δ₀) ^ β * s ^ β := by
      rw [← Real.mul_rpow (by positivity) hs.le]
      refine Real.one_le_rpow ?_ hβ.le
      rw [div_mul_eq_mul_div, le_div_iff₀ hδ₀]; linarith
    linarith

theorem mul_mem_compl_fwdHull {W : ℝ → ℝ} (hW : Continuous W) {d : ℂ} {r a₀ a₁ T m : ℝ}
    (ha₀ : 0 < a₀) (hm : 0 < m)
    (hgood0 : ∀ a ∈ Icc a₀ a₁, ∀ w ∈ foldSph d r, ∃ u, IsForwardSol W ((a : ℂ) * w) T u)
    (hlow : ∀ z ∈ scaledSph d r a₀ a₁, ∀ s ∈ Icc (0 : ℝ) T, m ≤ ‖fwdMap W s z‖)
    {τ a : ℝ} (hτ : τ ∈ Icc (0 : ℝ) T) (ha : a ∈ Icc a₀ a₁) {x : ℂ} (hx : x ∈ foldSph d r)
    (hxH : x ∈ H) : (a : ℂ) * x ∈ H \ fwdHull W τ := by
  have hawH : 0 < ((a : ℂ) * x).im := by
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact mul_pos (ha₀.trans_le ha.1) hxH
  exact mem_compl_fwdHull_of_lower hW hawH hm (hgood0 _ ha x hx) (hlow _ (mem_scaledSph ha hx)) hτ

/-- **The pushed base of the A-sep family is `1`-Frostman, uniformly over the box.** -/
theorem isFrostman_alphaA {W : ℝ → ℝ} (hW : Continuous W) (hW0 : W 0 = 0) {d : ℂ}
    {r a₀ a₁ T m : ℝ} (hr : 0 < r) (ha₀ : 0 < a₀) (hm : 0 < m)
    (hgood0 : ∀ a ∈ Icc a₀ a₁, ∀ w ∈ foldSph d r, ∃ u, IsForwardSol W ((a : ℂ) * w) T u)
    (hlow : ∀ z ∈ scaledSph d r a₀ a₁, ∀ s ∈ Icc (0 : ℝ) T, m ≤ ‖fwdMap W s z‖)
    {τ a : ℝ} (hτ : τ ∈ Icc (0 : ℝ) T) (ha : a ∈ Icc a₀ a₁) :
    IsFrostman ((foldedCircle d r).map (gA W d r τ a)) 1
      (6 / r * (2 * (Real.exp (8 * T / m ^ 2) / a₀)) ^ (1 : ℝ) +
        (2 / (m / 2 * Real.exp (-(8 * T / m ^ 2)))) ^ (1 : ℝ)) := by
  have hT : 0 ≤ T := hτ.1.trans hτ.2
  have ha0 : 0 < a := ha₀.trans_le ha.1
  refine isFrostman_map_of_coLip (measurable_gA hW hW0 hm hgood0 hlow hτ ha)
    (E := foldSph d r ∩ H)
    ((ae_mem_foldSph d hr.le).and (TwoPoint.foldedCircle_ae_mem_H d hr))
    (by positivity) (by positivity) one_pos (by positivity)
    (Cor15Group.isFrostman_fc d hr) ?_
  intro x hx y hy hclose
  rw [gA_of_mem hx.1, gA_of_mem hy.1] at hclose ⊢
  have hxc := mul_mem_compl_fwdHull hW ha₀ hm hgood0 hlow hτ ha hx.1 hx.2
  have hyc := mul_mem_compl_fwdHull hW ha₀ hm hgood0 hlow hτ ha hy.1 hy.2
  have hζ : 0 < (fwdMap W τ ((a : ℂ) * x)).im := FwdHolo.mapsTo_fwdMap hW hτ.1 hxc
  have h3 := norm_fwdMapInv_sub_le hW hW0 hT hm hyc.1 (hgood0 a ha y hy.1)
    (hlow _ (mem_scaledSph ha hy.1)) hτ hζ hclose
  rw [RS.fwdMapInv_fwdMap hW hW0 hτ.1 hxc] at h3
  have e : ‖(a : ℂ) * x - (a : ℂ) * y‖ = a * ‖x - y‖ := by
    rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha0]
  rw [e] at h3
  have h4 : a₀ * ‖x - y‖ ≤ a * ‖x - y‖ := mul_le_mul_of_nonneg_right ha.1 (norm_nonneg _)
  rw [div_mul_eq_mul_div, le_div_iff₀ ha₀]
  linarith

end ASep
end QuantumZipper
