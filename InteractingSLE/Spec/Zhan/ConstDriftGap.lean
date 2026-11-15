/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Zhan.ConstDriftGapProc
import InteractingSLE.Spec.Zhan.ConstDrift

/-!
# `UpperGapStatement κ` for `κ > 0`

Packet PROVE-ZHAN-A6. Astra, *Formalization proofs and dependency audit* (ruling R35), the scale calculation
(`ig1_formalization_proofs.txt` L1441–L1450): almost surely, for every rational `q`, the upper gap (3.15)
`X_t = q − ξ_t + ∫₀ᵗ tanh(X/2)`, `ξ_t = √κ β_t + σ t`, `|σ| < 1`, has `∫₀^∞ 1/(1 + cosh X) < ∞`.

Proof. Take a version `B` of `β` with every path continuous and `B 0 = 0` (an `nullAugmented` Brownian motion,
`Ito.isFilteredBrownianReal_modify`). With `p = min(κ/8, 1)`, the powers `φ₁ = s_σ^p` and `φ₂(x) = s_{−σ}(−x)^p` of
the scale functions from `−∞` and from `+∞` are nonnegative, smooth, with `L φᵢ ≤ 0` (`ConstDriftGapScale.lean`),
so `∫₀^∞ κ φᵢ'(X)² < ∞` almost surely (`ae_bdd_integral_sq_upGapProc`). Pointwise
`1/(1 + cosh x) ≤ C₁ φ₁'(x)² + C₂ φ₂'(x)²` (`φ₁'` dominates on `x ≤ 0`, `φ₂'` on `x ≥ 0`), and every solution of
(3.15) on `[0, T]` is the process `upGapProc` there (`eqOn_upGapProc`).

## Main results

* `upperGapStatement` : `0 < κ → UpperGapStatement κ`.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

universe u

namespace InteractingSLE

namespace Zhan

variable {κ σ : ℝ}

/-! ### The reflected power `φ₂(x) = s_{−σ}(−x)^p` -/

/-- `φ₂(x) = s_{−σ}(−x)^p` (the power of the scale function from `+∞`). -/
def scalePowR (κ σ p x : ℝ) : ℝ := scalePow κ (-σ) p (-x)

theorem hasDerivAt_scalePowR (hκ : 0 < κ) (hσ : σ < 1) (p x : ℝ) :
    HasDerivAt (scalePowR κ σ p) (-scalePowD κ (-σ) p (-x)) x := by
  have h := (hasDerivAt_scalePow hκ (by linarith : -1 < -σ) p (-x)).comp x (hasDerivAt_neg x)
  exact h.congr_deriv (by ring)

theorem contDiff_scalePowR (hκ : 0 < κ) (hσ : σ < 1) (p : ℝ) : ContDiff ℝ 3 (scalePowR κ σ p) := by
  have h : ContDiff ℝ 3 (scalePow κ (-σ) p) :=
    (contDiff_scalePow hκ (by linarith : -1 < -σ) p).of_le (WithTop.coe_le_coe.2 le_top)
  exact h.comp contDiff_neg

theorem scalePowR_nonneg (hκ : 0 < κ) (hσ : σ < 1) (p x : ℝ) : 0 ≤ scalePowR κ σ p x :=
  scalePow_nonneg κ (-σ) p (-x) hκ (by linarith)

theorem hasDerivAt_scalePowRD (hκ : 0 < κ) (hσ : σ < 1) (p x : ℝ) :
    HasDerivAt (fun x => -scalePowD κ (-σ) p (-x)) (scalePowDD κ (-σ) p (-x)) x := by
  have h := ((hasDerivAt_scalePowD hκ (by linarith : -1 < -σ) p (-x)).comp x (hasDerivAt_neg x)).neg
  exact h.congr_deriv (by ring)

theorem scalePowR_gen_nonpos (hκ : 0 < κ) (hσ : σ < 1) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : ℝ) :
    -scalePowD κ (-σ) p (-x) * (Real.tanh (x / 2) - σ) + κ / 2 * scalePowDD κ (-σ) p (-x) ≤ 0 := by
  have h := scalePow_gen_nonpos hκ (by linarith : -1 < -σ) hp0 hp1 (-x)
  have e : Real.tanh (-x / 2) = -Real.tanh (x / 2) := by rw [neg_div, Real.tanh_neg]
  rw [e] at h
  linarith

/-! ### The main theorem -/

/-- **`UpperGapStatement κ` for `κ > 0`.** -/
theorem upperGapStatement (hκ : 0 < κ) : UpperGapStatement.{u} κ := by
  intro σ hσ Ω mΩ P 𝓗 β hβ
  have : IsProbabilityMeasure P := hβ.1.toIsPreBrownianReal.isGaussianProcess.isProbabilityMeasure
  have hσl : -1 < σ := neg_lt_of_abs_lt hσ
  have hσr : σ < 1 := lt_of_abs_lt hσ
  -- a version with every path continuous and `B 0 = 0`
  have hae : ∀ᵐ ω ∂P, Continuous (β · ω) ∧ β 0 ω = 0 := by
    filter_upwards [hβ.1.cont, hβ.1.toIsPreBrownianReal.eval_zero_ae_eq_zero] with ω h1 h2 using ⟨h1, h2⟩
  set G : Set Ω := (toMeasurable P {ω | ¬ (Continuous (β · ω) ∧ β 0 ω = 0)})ᶜ with hGdef
  have hGm : MeasurableSet G := (measurableSet_toMeasurable _ _).compl
  have hGc : P Gᶜ = 0 := by rw [hGdef, compl_compl, measure_toMeasurable]; exact ae_iff.1 hae
  have hgood : ∀ ω ∈ G, Continuous (β · ω) ∧ β 0 ω = 0 := fun ω hω => by
    by_contra h; exact hω (subset_toMeasurable _ _ h)
  obtain ⟨B, hB, hBc, hB0, hβB⟩ : ∃ B : ℝ≥0 → Ω → ℝ, IsFilteredBrownianReal (Ito.nullAugmented 𝓗 P) B P ∧
      (∀ ω, Continuous (B · ω)) ∧ (∀ ω, B 0 ω = 0) ∧ ∀ ω ∈ G, ∀ t, β t ω = B t ω := by
    classical
    obtain ⟨hB, hBc⟩ := Ito.isFilteredBrownianReal_modify hβ hGm hGc fun ω hω => (hgood ω hω).1
    refine ⟨_, hB, hBc, fun ω => ?_, fun ω hω t => ?_⟩
    · by_cases hω : ω ∈ G
      · simp only [hω, ↓reduceIte]; exact (hgood ω hω).2
      · simp [hω]
    · simp only [hω, ↓reduceIte]
  -- the exponent
  set p : ℝ := min (κ / 8) 1 with hpdef
  have hp0 : 0 < p := lt_min (by positivity) one_pos
  have hp1 : p ≤ 1 := min_le_right _ _
  have hp8 : p ≤ κ / 8 := min_le_left _ _
  have hpa : ∀ τ : ℝ, τ < 1 → p * (2 * (τ + 1) / κ) ≤ 1 / 2 := fun τ hτ => by
    have h1 : 2 * (τ + 1) / κ ≤ 4 / κ := div_le_div_of_nonneg_right (by linarith) hκ.le
    have h2 : 0 ≤ 2 * (τ + 1) / κ ∨ 2 * (τ + 1) / κ < 0 := le_or_gt 0 _
    rcases h2 with h2 | h2
    · calc p * (2 * (τ + 1) / κ) ≤ κ / 8 * (4 / κ) := mul_le_mul hp8 h1 h2 (by positivity)
        _ = 1 / 2 := by field_simp; norm_num
    · nlinarith
  obtain ⟨C₁, hC₁, hb₁⟩ := exists_inv_one_add_cosh_le_scalePowD hκ hσl hp0 hp1 (hpa σ hσr)
  obtain ⟨C₂, hC₂, hb₂⟩ := exists_inv_one_add_cosh_le_scalePowD hκ (by linarith : -1 < -σ) hp0 hp1
    (hpa (-σ) (by linarith))
  -- the two quadratic-variation bounds, for every rational `q`
  have hq₁ : ∀ q : ℚ, ∀ᵐ ω ∂P, ∃ S : ℝ, ∀ t : ℝ≥0,
      ∫ s in (0 : ℝ)..t, κ * scalePowD κ σ p (upGapProc κ σ q B s.toNNReal ω) ^ 2 ≤ S := fun q =>
    ae_bdd_integral_sq_upGapProc (φ := scalePow κ σ p) (φ' := scalePowD κ σ p)
      (φ'' := scalePowDD κ σ p) hB hBc hB0 hκ.le q
      ((contDiff_scalePow hκ hσl p).of_le (WithTop.coe_le_coe.2 le_top))
      (fun x => scalePow_nonneg κ σ p x hκ hσl) (hasDerivAt_scalePow hκ hσl p)
      (hasDerivAt_scalePowD hκ hσl p) (scalePow_gen_nonpos hκ hσl hp0.le hp1)
  have hq₂ : ∀ q : ℚ, ∀ᵐ ω ∂P, ∃ S : ℝ, ∀ t : ℝ≥0,
      ∫ s in (0 : ℝ)..t, κ * (-scalePowD κ (-σ) p (-upGapProc κ σ q B s.toNNReal ω)) ^ 2 ≤ S := fun q =>
    ae_bdd_integral_sq_upGapProc (φ := scalePowR κ σ p) (φ' := fun x => -scalePowD κ (-σ) p (-x))
      (φ'' := fun x => scalePowDD κ (-σ) p (-x)) hB hBc hB0 hκ.le q
      (contDiff_scalePowR hκ hσr p) (scalePowR_nonneg hκ hσr p) (hasDerivAt_scalePowR hκ hσr p)
      (hasDerivAt_scalePowRD hκ hσr p) (scalePowR_gen_nonpos hκ hσr hp0.le hp1)
  filter_upwards [ae_all_iff.2 hq₁, ae_all_iff.2 hq₂, (ae_iff.2 hGc : ∀ᵐ ω ∂P, ω ∈ G)] with ω h₁ h₂ hωG
  intro q
  obtain ⟨S₁, hS₁⟩ := h₁ q
  obtain ⟨S₂, hS₂⟩ := h₂ q
  refine ⟨C₁ / κ * S₁ + C₂ / κ * S₂, fun T hT X hXc hX => ?_⟩
  -- the solution is the process
  have heq := eqOn_upGapProc (κ := κ) (σ := σ) (q := q) (hBc ω) hT hXc fun t ht => by
    rw [hX t ht, hβB ω hωG]
  set Y : ℝ → ℝ := fun r => upGapProc κ σ q B r.toNNReal ω with hYdef
  have hYc : Continuous Y := (continuous_upGapProc (hBc ω)).comp continuous_real_toNNReal
  have hD₁c : Continuous (scalePowD κ σ p) :=
    continuous_iff_continuousAt.2 fun x => (hasDerivAt_scalePowD hκ hσl p x).continuousAt
  have hD₂c : Continuous (scalePowD κ (-σ) p) :=
    continuous_iff_continuousAt.2 fun x => (hasDerivAt_scalePowD hκ (by linarith) p x).continuousAt
  have hf₁ : Continuous fun r => κ * scalePowD κ σ p (Y r) ^ 2 :=
    continuous_const.mul ((hD₁c.comp hYc).pow 2)
  have hf₂ : Continuous fun r => κ * (-scalePowD κ (-σ) p (-Y r)) ^ 2 :=
    continuous_const.mul ((hD₂c.comp hYc.neg).neg.pow 2)
  have hcosh : Continuous fun r => 1 / (1 + Real.cosh (Y r)) :=
    continuous_const.div (continuous_const.add (Real.continuous_cosh.comp hYc)) fun r => by
      linarith [Real.cosh_pos (Y r)]
  -- the pointwise bound
  have hpt : ∀ x : ℝ, 1 / (1 + Real.cosh x) ≤
      C₁ / κ * (κ * scalePowD κ σ p x ^ 2) + C₂ / κ * (κ * (-scalePowD κ (-σ) p (-x)) ^ 2) := by
    intro x
    have e1 : C₁ / κ * (κ * scalePowD κ σ p x ^ 2) = C₁ * scalePowD κ σ p x ^ 2 := by
      field_simp
    have e2 : C₂ / κ * (κ * (-scalePowD κ (-σ) p (-x)) ^ 2) = C₂ * scalePowD κ (-σ) p (-x) ^ 2 := by
      rw [neg_sq]; field_simp
    rw [e1, e2]
    have n1 : 0 ≤ C₁ * scalePowD κ σ p x ^ 2 := mul_nonneg hC₁ (sq_nonneg _)
    have n2 : 0 ≤ C₂ * scalePowD κ (-σ) p (-x) ^ 2 := mul_nonneg hC₂ (sq_nonneg _)
    rcases le_total x 0 with hx | hx
    · linarith [hb₁ x hx]
    · have := hb₂ (-x) (by linarith)
      rw [Real.cosh_neg] at this
      linarith
  have hT' : ((T.toNNReal : ℝ≥0) : ℝ) = T := Real.coe_toNNReal T hT
  have hI₁ := hS₁ T.toNNReal
  have hI₂ := hS₂ T.toNNReal
  rw [hT'] at hI₁ hI₂
  calc ∫ r in (0 : ℝ)..T, 1 / (1 + Real.cosh (X r))
      = ∫ r in (0 : ℝ)..T, 1 / (1 + Real.cosh (Y r)) := by
        refine intervalIntegral.integral_congr fun r hr => ?_
        rw [uIcc_of_le hT] at hr
        simp only [hYdef, heq r hr]
    _ ≤ ∫ r in (0 : ℝ)..T, (C₁ / κ * (κ * scalePowD κ σ p (Y r) ^ 2) +
          C₂ / κ * (κ * (-scalePowD κ (-σ) p (-Y r)) ^ 2)) :=
        intervalIntegral.integral_mono_on hT (hcosh.intervalIntegrable _ _)
          (((hf₁.const_mul _).add (hf₂.const_mul _)).intervalIntegrable _ _) fun r _ => hpt (Y r)
    _ = C₁ / κ * (∫ r in (0 : ℝ)..T, κ * scalePowD κ σ p (Y r) ^ 2) +
          C₂ / κ * ∫ r in (0 : ℝ)..T, κ * (-scalePowD κ (-σ) p (-Y r)) ^ 2 := by
        rw [intervalIntegral.integral_add ((hf₁.const_mul _).intervalIntegrable _ _)
          ((hf₂.const_mul _).intervalIntegrable _ _)]
        congr 1
        · exact intervalIntegral.integral_const_mul (C₁ / κ) fun r => κ * scalePowD κ σ p (Y r) ^ 2
        · exact intervalIntegral.integral_const_mul (C₂ / κ)
            fun r => κ * (-scalePowD κ (-σ) p (-Y r)) ^ 2
    _ ≤ C₁ / κ * S₁ + C₂ / κ * S₂ := by
        have hc₁ : 0 ≤ C₁ / κ := div_nonneg hC₁ hκ.le
        have hc₂ : 0 ≤ C₂ / κ := div_nonneg hC₂ hκ.le
        exact add_le_add (mul_le_mul_of_nonneg_left hI₁ hc₁) (mul_le_mul_of_nonneg_left hI₂ hc₂)

end Zhan

end InteractingSLE
