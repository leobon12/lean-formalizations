import HigherDimLQGContinuity.Improve.RoundingParams
import HigherDimLQGContinuity.Improve.GainParams

/-!
# A mesh-power lower bound for the rounding net radius
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

namespace HigherDimLQGContinuity

/-- Once `Δ ≤ v cseed`, the rounding radius is at least a fixed multiple of
`Δ^((K0+1)/σ)`. -/
theorem q11_rounding_radius_power {w Cb H σ v cseed Δ K0 U0 dsep : ℝ}
    (hw : 0 < w) (hCb : 0 < Cb) (hH : 0 < H)
    (hσ : 0 < σ) (hv : 0 < v) (hcseed : 0 < cseed)
    (hΔ : 0 < Δ) (hΔ1 : Δ ≤ 1) (hΔvc : Δ ≤ v * cseed)
    (hK0 : 0 ≤ K0) (hU0 : 0 < U0) (hdsep : 0 < dsep) :
    let T := min (w / 8)
      ((7 * dsep / (128 * Cb * H * U0)) ^ (1 / σ))
    let γ := (K0 + 1) / σ
    0 < T ∧ 0 ≤ γ ∧
      T * Δ ^ γ ≤
        q11RoundingRadius w Cb H σ
          (q11GainDelta v cseed Δ K0 U0) dsep := by
  let B : ℝ := 7 * dsep / (128 * Cb * H * U0)
  let T : ℝ := min (w / 8) (B ^ (1 / σ))
  let γ : ℝ := (K0 + 1) / σ
  have hB : 0 < B := by dsimp [B]; positivity
  have hT : 0 < T := lt_min (by positivity)
    (Real.rpow_pos_of_pos hB _)
  have hγ : 0 ≤ γ := by dsimp [γ]; positivity
  have hΔpow : Δ ^ γ ≤ 1 := Real.rpow_le_one hΔ.le hΔ1 hγ
  have hTarm : T * Δ ^ γ ≤ w / 8 :=
    (mul_le_of_le_one_right hT.le hΔpow).trans (min_le_left _ _)
  have hvc : 0 < v * cseed := mul_pos hv hcseed
  have hgainLow : Δ ^ (K0 + 1) / U0 ≤
      q11GainDelta v cseed Δ K0 U0 := by
    have hpow : Δ ^ (K0 + 1) = Δ * Δ ^ K0 := by
      rw [Real.rpow_add hΔ, Real.rpow_one]
      ring
    rw [hpow]
    dsimp [q11GainDelta]
    apply div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hΔvc (Real.rpow_nonneg hΔ.le _)) hU0.le
  have hAlo : B * Δ ^ (K0 + 1) ≤
      7 * q11GainDelta v cseed Δ K0 U0 * dsep / (128 * Cb * H) := by
    have hmul := mul_le_mul_of_nonneg_left hgainLow
      (by positivity : 0 ≤ 7 * dsep / (128 * Cb * H))
    have hleft : B * Δ ^ (K0 + 1) =
        (7 * dsep / (128 * Cb * H)) * (Δ ^ (K0 + 1) / U0) := by
      dsimp [B]
      field_simp
    have hright : (7 * dsep / (128 * Cb * H)) *
        q11GainDelta v cseed Δ K0 U0 =
        7 * q11GainDelta v cseed Δ K0 U0 * dsep / (128 * Cb * H) := by
      ring
    rw [hleft, ← hright]
    exact hmul
  have hpowEq : (B * Δ ^ (K0 + 1)) ^ (1 / σ) =
      B ^ (1 / σ) * Δ ^ γ := by
    rw [Real.mul_rpow hB.le (Real.rpow_nonneg hΔ.le _)]
    rw [← Real.rpow_mul hΔ.le]
    congr 1
    dsimp [γ]
    ring_nf
  have hApos : 0 ≤ B * Δ ^ (K0 + 1) := by positivity
  have hArpow : (B * Δ ^ (K0 + 1)) ^ (1 / σ) ≤
      (7 * q11GainDelta v cseed Δ K0 U0 * dsep / (128 * Cb * H)) ^ (1 / σ) :=
    Real.rpow_le_rpow hApos hAlo (by positivity)
  have hsecond : T * Δ ^ γ ≤
      (7 * q11GainDelta v cseed Δ K0 U0 * dsep / (128 * Cb * H)) ^ (1 / σ) := by
    have h : T * Δ ^ γ ≤ B ^ (1 / σ) * Δ ^ γ :=
      mul_le_mul_of_nonneg_right (min_le_right (w / 8) (B ^ (1 / σ)))
        (Real.rpow_nonneg hΔ.le γ)
    exact h.trans (hpowEq.symm ▸ hArpow)
  change 0 < T ∧ 0 ≤ γ ∧ T * Δ ^ γ ≤
    min (w / 8)
      ((7 * q11GainDelta v cseed Δ K0 U0 * dsep /
        (128 * Cb * H)) ^ (1 / σ))
  exact ⟨hT, hγ, le_min hTarm hsecond⟩

end HigherDimLQGContinuity
