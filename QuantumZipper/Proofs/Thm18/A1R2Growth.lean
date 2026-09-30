import QuantumZipper.Proofs.Thm18.A1R2LogD
import QuantumZipper.Proofs.Thm18.G4PushReg2Exact

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# A1R2 (growth): `A1RGrowthStmt` from the growth of `Y` at pulled-back circles

Decision D90. The smoothed witness of the unzipped field `U_t = coordChange Y f_t⁻¹ Q` at a folded
circle is its raw value (RC3 at all times, `Thm18Asm.ae_exactAll_wedgeConfig`, from the proved
wedge core statements), i.e.
`F_t(z, ρ) = evalReg Y ((f_t⁻¹)_* fc(z, ρ)) + Q ∫ log |(f_t⁻¹)'| dfc(z, ρ)`.
The second term is `O(1 + |log ρ|)` near `ℝ` (A1R2LogD.lean, Schwarz–Pick for the reverse flow),
so `A1RGrowthStmt` reduces to the same bound for the first term:

* `A1R2YGrowthStmt` (open): log growth of the regularized values of `Y` at the pulled-back folded
  circles `(f_t⁻¹)_* fc(z, ρ)`, `Im z ≤ √ρ` (Hu–Miller–Peres, Ann. Probab. 38 (2010), Prop. 2.1,
  for the measures `(f_t⁻¹)_* fc(z, ρ)`).
* **`a1rGrowthStmt_of_yGrowth : A1R2YGrowthStmt → A1RGrowthStmt`**.

Own bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace R18

open Thm18Asm

namespace A1R2

variable {W : ℝ → ℝ}

/-- **The log-derivative term near `ℝ`.** -/
theorem abs_integral_log_deriv_le (hG : G1zDrvGood W) {t : ℝ} (ht : 0 < t) (Rr : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z ∈ Hbar, ‖z‖ ≤ Rr → ∀ ρ : ℝ, 0 < ρ → ρ < 1 → z.im ≤ Real.sqrt ρ →
      |∫ u, Real.log ‖deriv (fwdMapInv W t) u‖ ∂foldedCircle z ρ| ≤ K * (1 + |Real.log ρ|) := by
  obtain ⟨C, hC⟩ := G1ZA1a.exists_bound_fwdMapInv hG ht
  have hWc := hG.1
  have hW0 := hG.2.1
  set L := |Real.log (Rr + 1 + C + 1)| with hL
  refine ⟨403 + 2 * Real.log 2 + L, by positivity, fun z hz hzR ρ hρ hρ1 hzρ => ?_⟩
  have hpt : ∀ᵐ u ∂foldedCircle z ρ,
      |Real.log ‖deriv (fwdMapInv W t) u‖| ≤ 2 * |Real.log u.im| + L := by
    filter_upwards [TwoPoint.foldedCircle_ae_mem_H z hρ,
      TwoPoint.foldedCircle_ae_norm_le z hρ.le] with u hu hun
    exact abs_log_norm_deriv_fwdMapInv_le hWc hW0 ht.le hC hu (by linarith)
  have hint : Integrable (fun u : ℂ => 2 * |Real.log u.im| + L) (foldedCircle z ρ) :=
    ((TwoPoint.integrable_log_im_foldedCircle z hρ).abs.const_mul 2).add (integrable_const _)
  have hI := integral_abs_log_im_fc_small hz hρ hρ1 hzρ
  have hl0 : 0 ≤ |Real.log ρ| := abs_nonneg _
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  calc |∫ u, Real.log ‖deriv (fwdMapInv W t) u‖ ∂foldedCircle z ρ|
      ≤ ∫ u, |Real.log ‖deriv (fwdMapInv W t) u‖| ∂foldedCircle z ρ := by
        simpa [Real.norm_eq_abs] using
          norm_integral_le_integral_norm (μ := foldedCircle z ρ)
            (fun u => Real.log ‖deriv (fwdMapInv W t) u‖)
    _ ≤ ∫ u, (2 * |Real.log u.im| + L) ∂foldedCircle z ρ :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ => abs_nonneg _) hint hpt
    _ = 2 * ∫ u, |Real.log u.im| ∂foldedCircle z ρ + L := by
        rw [integral_add ((TwoPoint.integrable_log_im_foldedCircle z hρ).abs.const_mul 2)
          (integrable_const _), integral_const_mul, integral_const]
        simp
    _ ≤ (403 + 2 * Real.log 2 + L) * (1 + |Real.log ρ|) := by
        have hL0 : 0 ≤ L := abs_nonneg _
        nlinarith [mul_nonneg hL0 hl0, mul_nonneg hlog2 hl0]

end A1R2

/-- A.s. all unzipped fields of the Theorem 1.8 configuration are exact at folded circles. -/
theorem a1r2_ae_exactAll {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {Y : Ω → FieldSample}
    (hS : Thm18Setting γ P B Y) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r →
      evalReg (unzippedField γ (wedgeConfig γ B Y ω) t) (foldedCircle d r) =
        unzippedField γ (wedgeConfig γ B Y ω) t (foldedCircle d r) := by
  have hYO := SWCore.yMergeOffTipStmt_holds
  exact ae_exactAll_wedgeConfig (LocLen.pStarShiftRegStmt_of_coreOff
    WedgeUnzip.pStarRealizeStmt_holds (LocLen.wedgeGoodOffAll_of_yMergeOffTip hYO)
    (LocLen.wedgeExactAll_of_yMergeOffTip hYO)
    (WedgeUnzip.wedgeContinuum_of_x WedgeUnzip.WDec.wedgeDecompStmt_holds
      WedgeUnzip.xContinuumStmt_holds)) hS

end R18
end QuantumZipper
