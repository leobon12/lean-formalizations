import HigherDimLQGContinuity.Continuum.LowerMoment

/-! Summing weighted crossing moments over the dyadic grids. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

def l2_lowerGrid (d : ℕ) (R : ℝ) (k : ℕ) : Finset (Rd d) :=
  w3bGrid d (R + 1) 1 (l2_lowerRadius k)

def l2_lowerTerm {d : ℕ} (D : DistRd d → ContMetric d)
    (β q : ℝ) (k : ℕ) (z : Rd d) (g : DistRd d) : ℝ≥0∞ :=
  (ENNReal.ofReal ((l2_lowerRadius k) ^ β) *
    (acrossDist (rho D g) z (l2_lowerRadius k) (2 * l2_lowerRadius k))⁻¹) ^ q

def l2_lowerGridSum {d : ℕ} (D : DistRd d → ContMetric d)
    (R β q : ℝ) (k : ℕ) (g : DistRd d) : ℝ≥0∞ :=
  ∑ z ∈ l2_lowerGrid d R k, l2_lowerTerm D β q k z g

theorem l2_measurable_lowerTerm {d : ℕ} {D : DistRd d → ContMetric d}
    (hD : Measurable D) (β q : ℝ) (k : ℕ) (z : Rd d) :
    Measurable (l2_lowerTerm D β q k z) := by
  unfold l2_lowerTerm
  exact (measurable_const.mul (l2_measurable_cross hD z _ _).inv).pow_const q

theorem l2_measurable_lowerGridSum {d : ℕ} {D : DistRd d → ContMetric d}
    (hD : Measurable D) (R β q : ℝ) (k : ℕ) :
    Measurable (l2_lowerGridSum D R β q k) := by
  unfold l2_lowerGridSum
  exact Finset.measurable_sum _ fun z _ => l2_measurable_lowerTerm hD β q k z

theorem l2_rpow_div_nat {d : ℕ} {r : ℝ} (hr : 0 < r) :
    r ^ ((d : ℝ) + 1) / r ^ d = r := by
  rw [Real.rpow_add hr, Real.rpow_natCast, Real.rpow_one]
  field_simp

/-- One grid's expected weighted crossing sum is bounded by its spacing. -/
theorem continuum_gridMoment {d : ℕ} (hd : 3 ≤ d) {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (hC1 : ConvUpperMomentShape d κ) (hC2 : ConvInvCrossShape d κ)
    {b μ q β : ℝ} (hb : 0 < b) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hq : 0 < q)
    (hβ : 1 ≤ q * (β - 1 - Real.sqrt (2 * d) * b) - q ^ 2 * b ^ 2 - d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ξ : ℝ, UHyp d κ b μ ξ →
      ∀ D : DistRd d → ContMetric d,
        IsStrongExpMetric d ξ (distExp d ξ) D →
        ∀ R : ℝ, 1 ≤ R → ∀ k : ℕ,
          (∫⁻ g, l2_lowerGridSum D R β q k g ∂(normLGFLaw d)) ≤
            ENNReal.ofReal (C * (16 * d * (R + 2) + 5) ^ d *
              (R + 3) ^ (2 * q ^ 2 * b ^ 2) * l2_lowerRadius k) := by
  obtain ⟨C, hC0, hC⟩ := continuum_weightedCross_moment hd hκ hC1 hC2
    hb hμ hμ1 hq hβ
  refine ⟨C, hC0, fun ξ hξ D hD R hR k => ?_⟩
  let r : ℝ := l2_lowerRadius k
  have hr : 0 < r := l2_lowerRadius_pos k
  have hr1 : r ≤ 1 := l2_lowerRadius_le_one k
  let A : ℝ := 16 * d * (R + 2) + 5
  let F : ℝ := (R + 3) ^ (2 * q ^ 2 * b ^ 2)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hAcard : ((l2_lowerGrid d R k).card : ℝ) ≤ A ^ d / r ^ d := by
    simpa only [l2_lowerGrid, r, A, show (R + 1) + 1 = R + 2 by ring] using
      w3b_card_grid_le (d := d) (show 1 ≤ d by omega)
        (show 0 < R + 1 by linarith) one_pos hr hr1
  have hterm (z : Rd d) (hz : z ∈ l2_lowerGrid d R k) :
      (∫⁻ g, l2_lowerTerm D β q k z g ∂(normLGFLaw d)) ≤
        ENNReal.ofReal (C * F * r ^ ((d : ℝ) + 1)) := by
    have hzn : ‖z‖ ≤ R + 2 := by
      have hh := w3b_norm_lt_of_mem_grid (d := d) (show z ∈ w3bGrid d (R + 1) 1 r by
        simpa only [l2_lowerGrid, r] using hz)
      nlinarith
    simpa only [l2_lowerTerm, r, F] using
      hC ξ hξ D hD R hR z hzn r hr hr1
  have hmeas (z : Rd d) (_hz : z ∈ l2_lowerGrid d R k) :
      Measurable (l2_lowerTerm D β q k z) :=
    l2_measurable_lowerTerm hD.measurable β q k z
  calc
    (∫⁻ g, l2_lowerGridSum D R β q k g ∂(normLGFLaw d)) =
        ∑ z ∈ l2_lowerGrid d R k,
          ∫⁻ g, l2_lowerTerm D β q k z g ∂(normLGFLaw d) := by
      exact lintegral_finsetSum (l2_lowerGrid d R k) hmeas
    _ ≤ ∑ _z ∈ l2_lowerGrid d R k,
        ENNReal.ofReal (C * F * r ^ ((d : ℝ) + 1)) :=
      Finset.sum_le_sum hterm
    _ = ENNReal.ofReal ((l2_lowerGrid d R k).card *
        (C * F * r ^ ((d : ℝ) + 1))) := by
      rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg _),
        ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (C * A ^ d * F * r) := by
      apply ENNReal.ofReal_le_ofReal
      have hcoef : 0 ≤ C * F * r ^ ((d : ℝ) + 1) := by positivity
      calc
        ((l2_lowerGrid d R k).card : ℝ) * (C * F * r ^ ((d : ℝ) + 1)) ≤
            (A ^ d / r ^ d) * (C * F * r ^ ((d : ℝ) + 1)) :=
          mul_le_mul_of_nonneg_right hAcard hcoef
        _ = C * A ^ d * F * r := by
          have hrpow : 0 < r ^ d := pow_pos hr d
          rw [Real.rpow_add hr, Real.rpow_natCast, Real.rpow_one]
          field_simp
    _ = ENNReal.ofReal (C * (16 * d * (R + 2) + 5) ^ d *
      (R + 3) ^ (2 * q ^ 2 * b ^ 2) * l2_lowerRadius k) := by rfl

end HigherDimLQGContinuity
