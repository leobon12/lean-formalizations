import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCUnweight
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCConditionalHolder
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCCondKernelAeMono

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.LFPP LQGMetric.WhiteNoise

theorem laneC_conditional_around_holder_of_envelope
    {Ω : Type*} {mₛ : MeasurableSpace Ω}
    [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    (Qψ : PsiParams) (ξ : ℝ) {K n : ℕ} (hKn : K ≤ n)
    (m : ℕ) (b : ℤ × ℤ) (p ζ : ℝ) (hp : 0 ≤ p) (hζ : 0 < ζ)
    (hm : mₛ = MeasurableSpace.comap
      (fun ω x => psiMN Qψ W P K n x ω)
      (inferInstance : MeasurableSpace (ℂ → ℝ)))
    {Z : Ω → ℝ≥0∞}
    (hdom : ∀ᵐ x ∂P,
      ((laneC_aemeasurable_J1WeightedAround P W hW Qψ ξ n K m b).mk
        (laneCJ1WeightedAround Qψ ξ P W hW n K m b) x) ^
        (p * ((1 + ζ) / ζ)) ≤ Z x) :
    ∀ᵐ ω ∂P,
      (∫⁻ x,
        ((lfppContMetric ξ (fun z => psiMN Qψ W P 0 n z x)
          ((isPsiVersion_psiMN hW (Nat.zero_le n)).cont x)).aroundDist
          (LaneCInputs.sourceAround K m b)
          (LaneCInputs.sourceInner K m b)
          (LaneCInputs.sourceOuter K m b)) ^ p
        ∂(condExpKernel P mₛ ω)) ≤
      (∫⁻ x, Z x ∂(condExpKernel P mₛ ω)) ^ (ζ / (1 + ζ)) *
        (ENNReal.ofReal (Real.exp (((K : ℝ) * Real.log 2) *
          (((1 + ζ) * p * ξ) ^ 2) / 2))) ^ (1 / (1 + ζ)) := by
  subst mₛ
  let κ := condExpKernel P (MeasurableSpace.comap
    (fun ω x => psiMN Qψ W P K n x ω)
    (inferInstance : MeasurableSpace (ℂ → ℝ)))
  let Y := laneCJ1WeightedAround Qψ ξ P W hW n K m b
  let hYm := laneC_aemeasurable_J1WeightedAround P W hW Qψ ξ n K m b
  let Y' := hYm.mk Y
  let G : Ω → ℝ≥0∞ := fun x => ENNReal.ofReal
    (Real.exp ((p * ξ) * phiMN W P 0 K (T20.dyCenter K b) x))
  have hY'm : Measurable Y' := hYm.measurable_mk
  have hGm : Measurable G := by
    dsimp [G]
    exact ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp
        (measurable_const.mul
          ((isPhiVersion_phiMN hW (Nat.zero_le K)).meas (T20.dyCenter K b))))
  have hDle : ∀ᵐ x ∂P,
      ((lfppContMetric ξ (fun z => psiMN Qψ W P 0 n z x)
        ((isPsiVersion_psiMN hW (Nat.zero_le n)).cont x)).aroundDist
        (LaneCInputs.sourceAround K m b)
        (LaneCInputs.sourceInner K m b)
        (LaneCInputs.sourceOuter K m b)) ^ p ≤ Y' x ^ p * G x := by
    filter_upwards [hYm.ae_eq_mk.symm] with x hx
    rw [laneC_around_rpow_eq_coarse_exp_mul_weighted Qψ ξ P W hW n K m b x p hp]
    rw [← hx]
    exact le_of_eq (mul_comm _ _)
  have hDcond := laneC_conditional_lintegral_mono_ae P (
    (measurable_pi_iff.mpr (isPsiVersion_psiMN (Q := Qψ) hW hKn).meas).comap_le)
    hDle
  have hr : 0 < (1 + ζ) / ζ := div_pos (by linarith) hζ
  have hs : 0 < 1 + ζ := by linarith
  have hq : 0 ≤ p * ((1 + ζ) / ζ) := mul_nonneg hp hr.le
  have hpower : (fun x => (Y' x ^ p) ^ ((1 + ζ) / ζ)) =
      fun x => Y' x ^ (p * ((1 + ζ) / ζ)) := by
    funext x
    exact (ENNReal.rpow_mul (Y' x) p ((1 + ζ) / ζ)).symm
  have hYcond := laneC_conditional_lintegral_mono_ae P (
    (measurable_pi_iff.mpr (isPsiVersion_psiMN (Q := Qψ) hW hKn).meas).comap_le)
    hdom
  have hGpow : (fun x => G x ^ (1 + ζ)) =
      fun x => ENNReal.ofReal
        (Real.exp (((1 + ζ) * p * ξ) *
          phiMN W P 0 K (T20.dyCenter K b) x)) := by
    funext x
    dsimp [G]
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hs.le, ← Real.exp_mul]
    congr 2
    ring
  have hMGF := laneC_conditional_coarse_phi_exp_moment P W hW Qψ hKn b
    ((1 + ζ) * p * ξ)
  filter_upwards [hDcond, hYcond, hMGF] with ω hd hy hg
  have hH := laneC_conditional_holder_at (κ ω)
    (f := fun x => Y' x ^ p) (g := G)
    (hY'm.pow_const p).aemeasurable hGm.aemeasurable hζ
  calc
    _ ≤ ∫⁻ x, Y' x ^ p * G x ∂(κ ω) := hd
    _ ≤ (∫⁻ x, (Y' x ^ p) ^ ((1 + ζ) / ζ) ∂(κ ω)) ^
        (ζ / (1 + ζ)) *
        (∫⁻ x, G x ^ (1 + ζ) ∂(κ ω)) ^
        (1 / (1 + ζ)) := hH
    _ ≤ (∫⁻ x, Z x ∂(κ ω)) ^ (ζ / (1 + ζ)) *
        (ENNReal.ofReal (Real.exp (((K : ℝ) * Real.log 2) *
          (((1 + ζ) * p * ξ) ^ 2) / 2))) ^ (1 / (1 + ζ)) := by
      rw [hpower, hGpow]
      exact mul_le_mul
        (ENNReal.rpow_le_rpow hy (by positivity))
        (ENNReal.rpow_le_rpow hg (by positivity)) bot_le bot_le

end SupercriticalLQGUniqueness.B2.DG20Conc
