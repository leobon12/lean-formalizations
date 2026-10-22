import HigherDimLQGContinuity.Fatou.Normalize

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd e₁)

/-- The convolution moment bounds pass to the mean-log-normalized continuum metric. -/
theorem continuum_fatou {d : ℕ} (hd : 3 ≤ d) {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (hC1 : ConvUpperMomentShape d κ) (hC2 : ConvInvCrossShape d κ)
    {b μ σ p : ℝ} (hb : 0 < b) (hμ : 0 < μ)
    (hμ1 : μ ≤ 1) (hσ : 0 < σ) (hσμ : σ < μ)
    (hp : 0 < p) (hpb : 32 * p * b ≤ Real.sqrt (2 * d)) :
    ∃ C A : ℝ, ∀ ξ : ℝ, UHyp d κ b μ ξ → ∀ D : DistRd d → ContMetric d,
      IsStrongExpMetric d ξ (distExp d ξ) D →
      Integrable (fun g => Real.log ((D g).1 (0, e₁ d))) (normLGFLaw d) ∧
      ∀ R : ℝ, 1 ≤ R → ∃ H : DistRd d → ℝ, Measurable H ∧ (∀ g, 1 ≤ H g) ∧
        (∫⁻ g, ENNReal.ofReal (H g ^ p) ∂(normLGFLaw d) ≤
          ENNReal.ofReal (C * (1 + R) ^ A)) ∧
        ∀ᵐ g ∂(normLGFLaw d), ∀ z ∈ closedBall (0 : Rd d) R,
          ∀ s ∈ Ioc (0 : ℝ) 1,
            internalDiamRd (rho D g) (ball z s) (ball z (2 * s)) ≤
              ENNReal.ofReal (H g * s ^ σ) := by
  obtain ⟨M, hlog⟩ := fatou_log_of_conv hd hκ hC1 hC2 hb hμ hμ1 hσ hσμ hp hpb
  obtain ⟨Cu, A, hupper⟩ :=
    fatou_upper_of_conv hd hκ hC1 hb hμ hμ1 hσ hσμ hp hpb
  refine ⟨Real.exp M ^ p * Cu, A, fun ξ hξ D hD => ?_⟩
  obtain ⟨D₀, hD₀, hconv⟩ := fatou_exists_canonical hd hκ hξ
  obtain ⟨hint₀, hmean⟩ := hlog ξ hξ D₀ hD₀ hconv
  have hsub := fatou_subcritical hξ
  have hae : ∀ᵐ g ∂(normLGFLaw d), rho D g = rho D₀ g :=
    rho_ae_eq_of_strong hd hsub.1 hsub.2 hD₀ hD hint₀
  have hint : Integrable (fun g => Real.log ((D g).1 (0, e₁ d)))
      (normLGFLaw d) :=
    integrable_log_of_strong hd hsub.1 hsub.2 hD₀ hD hint₀
  refine ⟨hint, fun R hR => ?_⟩
  obtain ⟨H, hHm, hH1, hHmom, hHpt⟩ := hupper ξ hξ D₀ hD₀ hconv R hR
  obtain ⟨H', hH'm, hH'1, hH'mom, hH'pt⟩ :=
    fatou_rho_upper hmean hHm hH1 hHmom hHpt
  refine ⟨H', hH'm, hH'1, hH'mom, ?_⟩
  filter_upwards [hH'pt, hae] with g hg he z hz s hs
  rw [he]
  exact hg z hz s hs

/-- Uniform inverse crossing moments for every strong assignment, after normalization. -/
theorem continuum_invCross {d : ℕ} (hd : 3 ≤ d) {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (hC1 : ConvUpperMomentShape d κ) (hC2 : ConvInvCrossShape d κ)
    {b μ : ℝ} (hb : 0 < b) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (z : Rd d) {a c q : ℝ} (ha : 0 < a) (hac : a < c) (hq : 0 < q) :
    ∃ C : ℝ, ∀ ξ : ℝ, UHyp d κ b μ ξ → ∀ D : DistRd d → ContMetric d,
      IsStrongExpMetric d ξ (distExp d ξ) D →
      ∫⁻ g, (acrossDist (rho D g) z a c)⁻¹ ^ q ∂(normLGFLaw d) ≤
        ENNReal.ofReal C := by
  let σ : ℝ := μ / 2
  let p : ℝ := Real.sqrt (2 * d) / (64 * b)
  have hsqrt : 0 < Real.sqrt (2 * d) := Real.sqrt_pos.2 (by positivity)
  have hσ : 0 < σ := by dsimp [σ]; linarith
  have hσμ : σ < μ := by dsimp [σ]; linarith
  have hp : 0 < p := by dsimp [p]; positivity
  have hpb : 32 * p * b ≤ Real.sqrt (2 * d) := by
    dsimp [p]
    have hb0 : b ≠ 0 := ne_of_gt hb
    field_simp
    nlinarith [le_of_lt hsqrt]
  obtain ⟨M, hlog⟩ := fatou_log_of_conv hd hκ hC1 hC2 hb hμ hμ1 hσ hσμ hp hpb
  obtain ⟨Ci, hcross⟩ := fatou_invCross_of_conv hd hκ hC2 hb hμ z ha hac hq
  refine ⟨Real.exp M ^ q * Ci, fun ξ hξ D hD => ?_⟩
  obtain ⟨D₀, hD₀, hconv⟩ := fatou_exists_canonical hd hκ hξ
  obtain ⟨hint₀, hmean⟩ := hlog ξ hξ D₀ hD₀ hconv
  have hsub := fatou_subcritical hξ
  have hae : ∀ᵐ g ∂(normLGFLaw d), rho D g = rho D₀ g :=
    rho_ae_eq_of_strong hd hsub.1 hsub.2 hD₀ hD hint₀
  have hbound := fatou_rho_invCross hD₀.measurable hmean hq z (hcross ξ hξ D₀ hconv)
  calc
    (∫⁻ g, (acrossDist (rho D g) z a c)⁻¹ ^ q ∂(normLGFLaw d)) =
        ∫⁻ g, (acrossDist (rho D₀ g) z a c)⁻¹ ^ q ∂(normLGFLaw d) := by
      apply lintegral_congr_ae
      filter_upwards [hae] with g hg
      rw [hg]
    _ ≤ ENNReal.ofReal (Real.exp M ^ q * Ci) := hbound

end HigherDimLQGContinuity
