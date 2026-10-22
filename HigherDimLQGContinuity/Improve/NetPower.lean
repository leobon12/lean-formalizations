import HigherDimLQGContinuity.Improve.NetCount

/-!
# Converting the net radius to a mesh-power pair bound
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

open HigherDimLFPP (Rd)

/-- A positive lower bound `t ≥ T Δ^γ` and one spare inverse mesh power
absorb the deterministic net prefactor. -/
theorem q11_net_pair_power {d : ℕ} (hd : 1 ≤ d)
    {t Δ T γ : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (hΔ : 0 < Δ) (hT : 0 < T)
    (htlower : T * Δ ^ γ ≤ t)
    (hconstant : (9 * Real.sqrt d / T) ^ (2 * d) ≤ Δ⁻¹)
    (N : Finset (Rd d))
    (hN : (N.card : ℝ) ≤ (8 * Real.sqrt d / t + 1) ^ d) :
    ((N.card * N.card : ℕ) : ℝ) ≤
      Δ ^ (-(2 * (d : ℝ) * γ + 1)) := by
  have hpair := q11_net_pair_count hd ht ht1 N hN
  have hΔγ : 0 < Δ ^ γ := Real.rpow_pos_of_pos hΔ _
  have hroot : 0 ≤ 9 * Real.sqrt (d : ℝ) := by positivity
  have hden : 0 < T * Δ ^ γ := mul_pos hT hΔγ
  have hstep : 9 * Real.sqrt d / t ≤
      (9 * Real.sqrt d / T) * Δ ^ (-γ) := by
    calc
      9 * Real.sqrt d / t ≤ 9 * Real.sqrt d / (T * Δ ^ γ) :=
        div_le_div_of_nonneg_left hroot hden htlower
      _ = (9 * Real.sqrt d / T) * Δ ^ (-γ) := by
        rw [Real.rpow_neg hΔ.le]
        field_simp
  have hstepPow : (9 * Real.sqrt d / t) ^ (2 * d) ≤
      ((9 * Real.sqrt d / T) * Δ ^ (-γ)) ^ (2 * d) := by
    exact pow_le_pow_left₀ (by positivity) hstep _
  have hconst0 : 0 ≤ (9 * Real.sqrt d / T) ^ (2 * d) := by positivity
  have hpow : ((9 * Real.sqrt d / T) * Δ ^ (-γ)) ^ (2 * d) =
      (9 * Real.sqrt d / T) ^ (2 * d) *
        Δ ^ (-(2 * (d : ℝ) * γ)) := by
    have hδ : (Δ ^ (-γ)) ^ (2 * d) = Δ ^ (-(2 * (d : ℝ) * γ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hΔ.le]
      congr 1
      push_cast
      ring
    rw [mul_pow, hδ]
  calc
    ((N.card * N.card : ℕ) : ℝ) ≤ (9 * Real.sqrt d / t) ^ (2 * d) := hpair
    _ ≤ ((9 * Real.sqrt d / T) * Δ ^ (-γ)) ^ (2 * d) := hstepPow
    _ = (9 * Real.sqrt d / T) ^ (2 * d) *
          Δ ^ (-(2 * (d : ℝ) * γ)) := hpow
    _ ≤ Δ⁻¹ * Δ ^ (-(2 * (d : ℝ) * γ)) :=
      mul_le_mul_of_nonneg_right hconstant (Real.rpow_nonneg hΔ.le _)
    _ = Δ ^ (-(2 * (d : ℝ) * γ + 1)) := by
      calc
        Δ⁻¹ * Δ ^ (-(2 * (d : ℝ) * γ)) =
            Δ ^ (-(1 : ℝ)) * Δ ^ (-(2 * (d : ℝ) * γ)) := by
              rw [Real.rpow_neg_one]
        _ = Δ ^ (-(1 : ℝ) + -(2 * (d : ℝ) * γ)) :=
          (Real.rpow_add hΔ _ _).symm
        _ = Δ ^ (-(2 * (d : ℝ) * γ + 1)) := by congr 1; ring

end HigherDimLQGContinuity
