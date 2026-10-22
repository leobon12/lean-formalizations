import HigherDimLQGContinuity.Continuum.Point
import GaussianLQG.LQG.Scaling.LogMoments

/-!
# Logarithmic moments of continuum point distances

Fractional powers turn one positive and one inverse moment into moments of
every order of the logarithm.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

theorem l2_abs_log_le_fractional {x s : ℝ} (hx : 0 < x) (hs : 0 < s) :
    |Real.log x| ≤ (x ^ s + (x ^ s)⁻¹) / s := by
  have h := GaussianLQG.abs_log_le_add_inv (Real.rpow_pos_of_pos hx s)
  rw [Real.log_rpow hx s, abs_mul, abs_of_pos hs] at h
  exact (le_div_iff₀ hs).2 (by nlinarith)

theorem l2_ofReal_abs_log_rpow_le {x s m : ℝ} (hx : 0 < x)
    (hs : 0 < s) (hm : 1 ≤ m) :
    ENNReal.ofReal |Real.log x| ^ m ≤
      ENNReal.ofReal s⁻¹ ^ m * (2 : ℝ≥0∞) ^ (m - 1) *
        ((ENNReal.ofReal (x ^ s)) ^ m +
          ((ENNReal.ofReal (x ^ s))⁻¹) ^ m) := by
  have hxs : 0 < x ^ s := Real.rpow_pos_of_pos hx s
  have hsum : 0 ≤ x ^ s + (x ^ s)⁻¹ := by positivity
  have hsf : 0 ≤ s⁻¹ := inv_nonneg.mpr hs.le
  have hbase : ENNReal.ofReal |Real.log x| ≤
      ENNReal.ofReal s⁻¹ *
        (ENNReal.ofReal (x ^ s) + (ENNReal.ofReal (x ^ s))⁻¹) := by
    have hr := l2_abs_log_le_fractional hx hs
    have heq : (x ^ s + (x ^ s)⁻¹) / s =
        s⁻¹ * (x ^ s + (x ^ s)⁻¹) := by ring
    rw [heq] at hr
    calc
      ENNReal.ofReal |Real.log x| ≤
          ENNReal.ofReal (s⁻¹ * (x ^ s + (x ^ s)⁻¹)) :=
        ENNReal.ofReal_le_ofReal hr
      _ = ENNReal.ofReal s⁻¹ *
          (ENNReal.ofReal (x ^ s) + (ENNReal.ofReal (x ^ s))⁻¹) := by
        rw [ENNReal.ofReal_mul hsf, ENNReal.ofReal_add hxs.le
          (inv_nonneg.mpr hxs.le), ENNReal.ofReal_inv_of_pos hxs]
  calc
    ENNReal.ofReal |Real.log x| ^ m ≤
        (ENNReal.ofReal s⁻¹ *
          (ENNReal.ofReal (x ^ s) + (ENNReal.ofReal (x ^ s))⁻¹)) ^ m :=
      ENNReal.rpow_le_rpow hbase (by linarith)
    _ = ENNReal.ofReal s⁻¹ ^ m *
        (ENNReal.ofReal (x ^ s) + (ENNReal.ofReal (x ^ s))⁻¹) ^ m := by
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by linarith)]
    _ ≤ _ := by
      calc
        ENNReal.ofReal s⁻¹ ^ m *
            (ENNReal.ofReal (x ^ s) + (ENNReal.ofReal (x ^ s))⁻¹) ^ m ≤
            ENNReal.ofReal s⁻¹ ^ m *
              ((2 : ℝ≥0∞) ^ (m - 1) *
                ((ENNReal.ofReal (x ^ s)) ^ m +
                  ((ENNReal.ofReal (x ^ s))⁻¹) ^ m)) :=
          mul_le_mul_of_nonneg_left
            (ENNReal.rpow_add_le_mul_rpow_add_rpow _ _ hm) bot_le
        _ = _ := by rw [mul_assoc]

/-- A fixed positive moment and its inverse control any logarithmic moment. -/
theorem l2_abs_log_bound {x p m : ℝ} (hx : 0 < x)
    (hp : 0 < p) (hm : 1 ≤ m) :
    ENNReal.ofReal |Real.log x| ^ m ≤
      (ENNReal.ofReal (p / m)⁻¹ ^ m * (2 : ℝ≥0∞) ^ (m - 1)) *
        ((ENNReal.ofReal x) ^ p + ((ENNReal.ofReal x)⁻¹) ^ p) := by
  let s : ℝ := p / m
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hs : 0 < s := div_pos hp hm0
  have hsm : s * m = p := by dsimp [s]; field_simp
  have hpos : (ENNReal.ofReal (x ^ s)) ^ m = (ENNReal.ofReal x) ^ p := by
    rw [← ENNReal.ofReal_rpow_of_nonneg hx.le hs.le,
      ← ENNReal.rpow_mul, hsm]
  have hneg : ((ENNReal.ofReal (x ^ s))⁻¹) ^ m =
      ((ENNReal.ofReal x)⁻¹) ^ p := by
    rw [← ENNReal.ofReal_rpow_of_nonneg hx.le hs.le,
      ← ENNReal.inv_rpow, ← ENNReal.rpow_mul, hsm]
  have h := l2_ofReal_abs_log_rpow_le hx hs hm
  rw [hpos, hneg] at h
  simpa only [s, mul_assoc] using h

/-- Uniform logarithmic moments of every fixed pair, for every real order at least one. -/
theorem continuum_logPt {d : ℕ} (hd : 3 ≤ d) {κ : Rd d → ℝ}
    (hκ : HigherDimLFPP.IsLFPPKernel κ)
    (hC1 : ConvUpperMomentShape d κ) (hC2 : ConvInvCrossShape d κ)
    {b μ : ℝ} (hb : 0 < b) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (x y : Rd d) (hxy : x ≠ y) {m : ℝ} (hm : 1 ≤ m) :
    ∃ C : ℝ, ∀ ξ : ℝ, UHyp d κ b μ ξ →
      ∀ D : DistRd d → ContMetric d,
        IsStrongExpMetric d ξ (distExp d ξ) D →
        (∫⁻ g, ENNReal.ofReal (|Real.log ((rho D g).1 (x, y))|) ^ m
          ∂(normLGFLaw d)) ≤ ENNReal.ofReal C := by
  let p : ℝ := Real.sqrt (2 * d) / (64 * b)
  let σ : ℝ := μ / 2
  have hsqrt : 0 < Real.sqrt (2 * d) := Real.sqrt_pos.2 (by positivity)
  have hp : 0 < p := by dsimp [p]; positivity
  have hσ : 0 < σ := by dsimp [σ]; linarith
  have hσμ : σ < μ := by dsimp [σ]; linarith
  have hpb : 32 * p * b ≤ Real.sqrt (2 * d) := by
    dsimp [p]
    have hb0 : b ≠ 0 := ne_of_gt hb
    field_simp
    nlinarith [le_of_lt hsqrt]
  obtain ⟨Cu, hu⟩ := continuum_point_upper hd hκ hC1 hC2 hb hμ hμ1
    hσ hσμ hp hpb x y
  obtain ⟨Cl, hl⟩ := continuum_point_invMoment hd hκ hC1 hC2 hb hμ hμ1
    x y hxy hp
  let c : ℝ≥0∞ := ENNReal.ofReal (p / m)⁻¹ ^ m * (2 : ℝ≥0∞) ^ (m - 1)
  let C : ℝ≥0∞ := c * (ENNReal.ofReal Cu + ENNReal.ofReal Cl)
  have hCtop : C ≠ ⊤ := by
    dsimp [C, c]
    apply ENNReal.mul_ne_top
    · apply ENNReal.mul_ne_top
      · exact ENNReal.rpow_ne_top_of_nonneg (by linarith) ENNReal.ofReal_ne_top
      · exact ENNReal.rpow_ne_top_of_nonneg (by linarith) (by norm_num)
    · exact ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩
  refine ⟨C.toReal, fun ξ hξ D hD => ?_⟩
  have hM : Measurable (fun g => ENNReal.ofReal ((rho D g).1 (x, y))) :=
    ENNReal.measurable_ofReal.comp
      (p2_measurable_contMetric_apply (measurable_rho hD.measurable) (x, y))
  have hF : Measurable (fun g => ENNReal.ofReal ((rho D g).1 (x, y)) ^ p) :=
    hM.pow_const p
  have hG : Measurable (fun g => (ENNReal.ofReal ((rho D g).1 (x, y)))⁻¹ ^ p) :=
    (hM.inv).pow_const p
  have hpoint (g : DistRd d) :
      ENNReal.ofReal |Real.log ((rho D g).1 (x, y))| ^ m ≤
        c * (ENNReal.ofReal ((rho D g).1 (x, y)) ^ p +
          (ENNReal.ofReal ((rho D g).1 (x, y)))⁻¹ ^ p) :=
    l2_abs_log_bound ((rho D g).apply_pos hxy) hp hm
  calc
    (∫⁻ g, ENNReal.ofReal |Real.log ((rho D g).1 (x, y))| ^ m
        ∂(normLGFLaw d)) ≤
        ∫⁻ g, c * (ENNReal.ofReal ((rho D g).1 (x, y)) ^ p +
          (ENNReal.ofReal ((rho D g).1 (x, y)))⁻¹ ^ p)
          ∂(normLGFLaw d) := lintegral_mono hpoint
    _ = c * ((∫⁻ g, ENNReal.ofReal ((rho D g).1 (x, y)) ^ p
          ∂(normLGFLaw d)) +
        (∫⁻ g, (ENNReal.ofReal ((rho D g).1 (x, y)))⁻¹ ^ p
          ∂(normLGFLaw d))) := by
      calc
        _ = c * (∫⁻ g, ENNReal.ofReal ((rho D g).1 (x, y)) ^ p +
            (ENNReal.ofReal ((rho D g).1 (x, y)))⁻¹ ^ p
            ∂(normLGFLaw d)) := by
          simpa only [Pi.add_apply] using (lintegral_const_mul c (hF.add hG))
        _ = _ := by rw [lintegral_add_left hF]
    _ ≤ C := by
      dsimp [C]
      gcongr
      · exact hu ξ hξ D hD
      · exact hl ξ hξ D hD
    _ = ENNReal.ofReal C.toReal := (ENNReal.ofReal_toReal hCtop).symm

end HigherDimLQGContinuity
