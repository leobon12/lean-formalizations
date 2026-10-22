import HigherDimLQGContinuity.Continuum.LowerEnvelope

/-! Uniform continuum lower modulus from dyadic shell barriers. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

theorem l2_lower_beta_pos {d : ℕ} {b q β : ℝ}
    (hb : 0 < b) (hq : 0 < q)
    (hβ : 1 ≤ q * (β - 1 - Real.sqrt (2 * d) * b) - q ^ 2 * b ^ 2 - d) :
    0 < β := by
  have hroot : 0 ≤ Real.sqrt (2 * d) := Real.sqrt_nonneg _
  have hrootb : 0 ≤ Real.sqrt (2 * d) * b := mul_nonneg hroot hb.le
  have hqb : 0 ≤ q ^ 2 * b ^ 2 := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hd0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
  have hdiff : 0 < β - 1 - Real.sqrt (2 * d) * b := by
    by_contra hh
    have hle : β - 1 - Real.sqrt (2 * d) * b ≤ 0 := le_of_not_gt hh
    have hprod := mul_nonpos_of_nonneg_of_nonpos hq.le hle
    linarith
  linarith

/-- Raw lower-modulus envelope; its explicit moment bound is before the polynomial-in-`R`
simplification in the blueprint. -/
theorem continuum_holderLower_raw {d : ℕ} (hd : 3 ≤ d) {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (hC1 : ConvUpperMomentShape d κ) (hC2 : ConvInvCrossShape d κ)
    {b μ q β : ℝ} (hb : 0 < b) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hq : 0 < q)
    (hβ : 1 ≤ q * (β - 1 - Real.sqrt (2 * d) * b) - q ^ 2 * b ^ 2 - d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : ℝ, UHyp d κ b μ ξ →
      ∀ D : DistRd d → ContMetric d,
        IsStrongExpMetric d ξ (distExp d ξ) D →
        ∀ R : ℝ, 1 ≤ R →
          ∃ H : DistRd d → ℝ, Measurable H ∧ (∀ g, 1 ≤ H g) ∧
            (∀ p' : ℝ, 0 < p' → p' < q →
              (∫⁻ g, ENNReal.ofReal (H g ^ p') ∂(normLGFLaw d)) ≤
                ENNReal.ofReal ((16 * R) ^ (β * p') *
                  (1 + C * (16 * d * (R + 2) + 5) ^ d *
                    (R + 3) ^ (2 * q ^ 2 * b ^ 2) / 4))) ∧
            ∀ᵐ g ∂(normLGFLaw d), ∀ x ∈ closedBall (0 : Rd d) R,
              ∀ y ∈ closedBall (0 : Rd d) R,
                ‖x - y‖ ^ β / H g ≤ (rho D g).1 (x, y) := by
  obtain ⟨C, hC0, henergy⟩ := continuum_lowerEnergy_moment hd hκ hC1 hC2
    hb hμ hμ1 hq hβ
  refine ⟨C, hC0, fun ξ hξ D hD R hR => ?_⟩
  let X : DistRd d → ℝ≥0∞ := l2_lowerEnergy D R β q
  let H₀ : DistRd d → ℝ := l2_lowerEnvelope X q
  let H : DistRd d → ℝ := fun g => (16 * R) ^ β * H₀ g
  have hβpos : 0 < β := l2_lower_beta_pos hb hq hβ
  have hR16 : 1 ≤ 16 * R := by nlinarith
  have hfac : 1 ≤ (16 * R) ^ β := Real.one_le_rpow hR16 hβpos.le
  have hfac0 : 0 ≤ (16 * R) ^ β := by linarith
  have hXmeas : Measurable X := l2_measurable_lowerEnergy hD.measurable R β q
  have hH₀meas : Measurable H₀ := l2_measurable_lowerEnvelope hXmeas hq
  have hHmeas : Measurable H := measurable_const.mul hH₀meas
  have hH1 (g : DistRd d) : 1 ≤ H g := by
    have h₀ := l2_lowerEnvelope_one_le X q g
    dsimp [H, H₀]
    nlinarith
  refine ⟨H, hHmeas, hH1, ?_, ?_⟩
  · intro p' hp' hp'q
    have hX1 (g : DistRd d) : 1 ≤ X g := by
      dsimp [X, l2_lowerEnergy]
      exact le_add_of_nonneg_right bot_le
    have hpoint (g : DistRd d) :
        ENNReal.ofReal (H₀ g ^ p') ≤ X g :=
      l2_lowerEnvelope_moment_pointwise hq hp'q g (hX1 g)
    have heq (g : DistRd d) : ENNReal.ofReal (H g ^ p') =
        ENNReal.ofReal ((16 * R) ^ (β * p')) *
          ENNReal.ofReal (H₀ g ^ p') := by
      dsimp [H]
      rw [Real.mul_rpow hfac0 (by linarith [l2_lowerEnvelope_one_le X q g] : 0 ≤ H₀ g),
        ← Real.rpow_mul (by linarith : 0 ≤ 16 * R),
        ENNReal.ofReal_mul (Real.rpow_nonneg (by linarith : 0 ≤ 16 * R) _)]
    have hXmom := henergy ξ hξ D hD R hR
    calc
      (∫⁻ g, ENNReal.ofReal (H g ^ p') ∂(normLGFLaw d)) =
          ∫⁻ g, ENNReal.ofReal ((16 * R) ^ (β * p')) *
            ENNReal.ofReal (H₀ g ^ p') ∂(normLGFLaw d) := by
        simp_rw [heq]
      _ = ENNReal.ofReal ((16 * R) ^ (β * p')) *
          (∫⁻ g, ENNReal.ofReal (H₀ g ^ p') ∂(normLGFLaw d)) := by
        exact lintegral_const_mul _
          (ENNReal.measurable_ofReal.comp
            ((Real.continuous_rpow_const hp'.le).measurable.comp hH₀meas))
      _ ≤ ENNReal.ofReal ((16 * R) ^ (β * p')) *
          (∫⁻ g, X g ∂(normLGFLaw d)) := by
        gcongr
        exact hpoint _
      _ ≤ ENNReal.ofReal ((16 * R) ^ (β * p')) *
          ENNReal.ofReal (1 + C * (16 * d * (R + 2) + 5) ^ d *
            (R + 3) ^ (2 * q ^ 2 * b ^ 2) / 4) := by gcongr
      _ = ENNReal.ofReal ((16 * R) ^ (β * p') *
          (1 + C * (16 * d * (R + 2) + 5) ^ d *
            (R + 3) ^ (2 * q ^ 2 * b ^ 2) / 4)) := by
        rw [ENNReal.ofReal_mul (Real.rpow_nonneg (by linarith : 0 ≤ 16 * R) _)]
  · have hXmom := henergy ξ hξ D hD R hR
    have hfinite : ∀ᵐ g ∂(normLGFLaw d), X g ≠ ⊤ := by
      have hint : (∫⁻ g, X g ∂(normLGFLaw d)) ≠ ⊤ :=
        ne_top_of_le_ne_top ENNReal.ofReal_ne_top hXmom
      filter_upwards [ae_lt_top hXmeas hint] with g hg
      exact hg.ne
    have hlen : ∀ᵐ g ∂(normLGFLaw d), (rho D g).IsLength := by
      letI := l9b_normLGFLaw_prob (show 2 ≤ d by omega)
      filter_upwards [hD.length (normLGFLaw d) id
        (l9b_normLGFLaw_normalized (show 2 ≤ d by omega)).1.isLGFPlusCont] with g hg
      exact ContMetric.isLength_smul (Real.exp_pos _) hg
    filter_upwards [hfinite, hlen] with g hfin hlen x hx y hy
    have hHpos : 0 < H g := by linarith [hH1 g]
    have hgrid : ∀ k : ℕ, ∀ z ∈ w3bGrid d (R + 1) 1 (l2_lowerRadius k),
        ENNReal.ofReal ((l2_lowerRadius k) ^ β / H₀ g) ≤
          acrossDist (rho D g) z (l2_lowerRadius k) (2 * l2_lowerRadius k) := by
      simpa only [l2_lowerGrid, H₀, X] using
        l2_lowerEnvelope_grid_barrier (D := D) (R := R) (β := β) hq hfin
    have hdet := l2_lower_of_grid (show 1 ≤ d by omega) (rho D g) hlen
      hR hβpos (by linarith [l2_lowerEnvelope_one_le X q g] : 0 < H₀ g)
      hgrid hx hy
    have hnum : 0 ≤ ‖x - y‖ ^ β / H g := by positivity
    have hdet' : ENNReal.ofReal (‖x - y‖ ^ β / H g) ≤
        ENNReal.ofReal ((rho D g).1 (x, y)) := by
      simpa only [H] using hdet
    exact (ENNReal.ofReal_le_ofReal_iff ((rho D g).nonneg x y)).1 hdet'

/-- The continuum lower modulus with the polynomial radius moment stated in the blueprint. -/
theorem continuum_holderLower {d : ℕ} (hd : 3 ≤ d) {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (hC1 : ConvUpperMomentShape d κ) (hC2 : ConvInvCrossShape d κ)
    {b μ q β : ℝ} (hb : 0 < b) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hq : 0 < q)
    (hβ : 1 ≤ q * (β - 1 - Real.sqrt (2 * d) * b) - q ^ 2 * b ^ 2 - d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : ℝ, UHyp d κ b μ ξ →
      ∀ D : DistRd d → ContMetric d,
        IsStrongExpMetric d ξ (distExp d ξ) D →
        ∀ R : ℝ, 1 ≤ R →
          ∃ H : DistRd d → ℝ, Measurable H ∧ (∀ g, 1 ≤ H g) ∧
            (∀ p' : ℝ, 0 < p' → p' < q →
              (∫⁻ g, ENNReal.ofReal (H g ^ p') ∂(normLGFLaw d)) ≤
                ENNReal.ofReal (C * (q / (q - p')) *
                  (16 * R) ^ (p' * β) *
                    (1 + R) ^ ((d : ℝ) + 2 * q ^ 2 * b ^ 2))) ∧
            ∀ᵐ g ∂(normLGFLaw d), ∀ x ∈ closedBall (0 : Rd d) R,
              ∀ y ∈ closedBall (0 : Rd d) R,
                ‖x - y‖ ^ β / H g ≤ (rho D g).1 (x, y) := by
  obtain ⟨C₀, hC₀0, hraw⟩ := continuum_holderLower_raw hd hκ hC1 hC2
    hb hμ hμ1 hq hβ
  let B : ℝ := 32 * d + 5
  let f : ℝ := 2 * q ^ 2 * b ^ 2
  let A : ℝ := (d : ℝ) + f
  let C : ℝ := 1 + C₀ * B ^ d * 2 ^ f / 4
  have hC : 0 ≤ C := by dsimp [C, B, f]; positivity
  refine ⟨C, hC, fun ξ hξ D hD R hR => ?_⟩
  obtain ⟨H, hHm, hH1, hHmom, hHpt⟩ := hraw ξ hξ D hD R hR
  refine ⟨H, hHm, hH1, ?_, hHpt⟩
  intro p' hp' hp'q
  have hR1 : 1 ≤ 1 + R := by linarith
  have hR0 : 0 < 16 * R := by positivity
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hf0 : 0 ≤ f := by dsimp [f]; positivity
  have hA0 : 0 ≤ A := by dsimp [A]; positivity
  have hAd : (16 * d * (R + 2) + 5) ^ d ≤
      B ^ d * (1 + R) ^ d := by
    have hbase : 16 * d * (R + 2) + 5 ≤ B * (1 + R) := by
      dsimp [B]
      have hd0 : 0 ≤ (d : ℝ) := Nat.cast_nonneg _
      nlinarith [mul_nonneg hd0 (sub_nonneg.mpr (by linarith : 1 ≤ R))]
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ 16 * d * (R + 2) + 5)
      hbase d
    rw [mul_pow] at hh
    exact hh
  have hFr : (R + 3) ^ f ≤ 2 ^ f * (1 + R) ^ f := by
    have hbase : R + 3 ≤ 2 * (1 + R) := by linarith
    have hh := Real.rpow_le_rpow (by linarith : 0 ≤ R + 3) hbase hf0
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by linarith : 0 ≤ 1 + R)] at hh
    exact hh
  have hP : 1 ≤ (1 + R) ^ A := Real.one_le_rpow hR1 hA0
  have hpoly : 1 + C₀ * (16 * d * (R + 2) + 5) ^ d * (R + 3) ^ f / 4 ≤
      C * (1 + R) ^ A := by
    have hprod : (16 * d * (R + 2) + 5) ^ d * (R + 3) ^ f ≤
        (B ^ d * 2 ^ f) * (1 + R) ^ A := by
      calc
        (16 * d * (R + 2) + 5) ^ d * (R + 3) ^ f ≤
            (B ^ d * (1 + R) ^ d) * (2 ^ f * (1 + R) ^ f) := by
          exact mul_le_mul hAd hFr (Real.rpow_nonneg (by linarith : 0 ≤ R + 3) _)
            (mul_nonneg (pow_nonneg hB0 _) (pow_nonneg (by linarith : 0 ≤ 1 + R) _))
        _ = (B ^ d * 2 ^ f) * (1 + R) ^ A := by
          rw [show A = (d : ℝ) + f from rfl, Real.rpow_add (by linarith : 0 < 1 + R),
            Real.rpow_natCast]
          ring
    have hcoef : 0 ≤ C₀ / 4 := div_nonneg hC₀0 (by norm_num)
    have hterm := mul_le_mul_of_nonneg_left hprod hcoef
    have hbase : 0 ≤ C₀ * B ^ d * 2 ^ f / 4 := by positivity
    dsimp [C]
    nlinarith [mul_nonneg hbase (sub_nonneg.mpr hP)]
  have hfactor : 1 ≤ q / (q - p') := by
    have hden : 0 < q - p' := by linarith
    rw [le_div_iff₀ hden]
    linarith
  have hnum : 0 ≤ (16 * R) ^ (β * p') := Real.rpow_nonneg hR0.le _
  have hpoly' : (16 * R) ^ (β * p') *
      (1 + C₀ * (16 * d * (R + 2) + 5) ^ d * (R + 3) ^ f / 4) ≤
      C * (q / (q - p')) * (16 * R) ^ (p' * β) * (1 + R) ^ A := by
    have h1 := mul_le_mul_of_nonneg_left hpoly hnum
    have h2 : C * (1 + R) ^ A ≤ C * (q / (q - p')) * (1 + R) ^ A := by
      have hc0 : 0 ≤ C * (1 + R) ^ A := by positivity
      nlinarith [mul_nonneg hc0 (sub_nonneg.mpr hfactor)]
    calc
      (16 * R) ^ (β * p') *
          (1 + C₀ * (16 * d * (R + 2) + 5) ^ d * (R + 3) ^ f / 4) ≤
          (16 * R) ^ (β * p') * (C * (1 + R) ^ A) := h1
      _ ≤ (16 * R) ^ (β * p') * (C * (q / (q - p')) * (1 + R) ^ A) := by
        nlinarith [mul_nonneg hnum (sub_nonneg.mpr h2)]
      _ = C * (q / (q - p')) * (16 * R) ^ (p' * β) * (1 + R) ^ A := by
        rw [show β * p' = p' * β by ring]
        ring
  exact (hHmom p' hp' hp'q).trans (ENNReal.ofReal_le_ofReal (by
    simpa only [f, A] using hpoly'))

end HigherDimLQGContinuity
