import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCTripleHolder
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCConditionalAroundHolder
import SupercriticalLQGUniqueness.B2.DG20Conc.LaneCB3Rpow

 

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.DG20Conc

open LQGMetric LQGMetric.DDDF LQGMetric.LFPP LQGMetric.WhiteNoise

 

theorem laneC_conditional_source_product_of_envelope
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : WNSpace → Ω → ℝ) (hW : IsWhiteNoise P W)
    (Qψ : PsiParams) (ξ Q δ : ℝ) {K n : ℕ} (hKn : K ≤ n)
    (m : ℕ) (b : ℤ × ℤ) (p ζ : ℝ) (hp : 0 < p) (hζ : 0 < ζ)
    {Z : Ω → ℝ≥0∞}
    (hdom : ∀ᵐ x ∂P,
      ((laneC_aemeasurable_J1WeightedAround P W hW Qψ ξ n K m b).mk
        (laneCJ1WeightedAround Qψ ξ P W hW n K m b) x) ^
        (p * (2 * ((1 + ζ) / ζ))) ≤ Z x) :
    let κ := condExpKernel P (MeasurableSpace.comap
      (fun y z => psiMN Qψ W P K n z y)
      (inferInstance : MeasurableSpace (ℂ → ℝ)))
    let R : Ω → ℝ≥0∞ := fun x => ENNReal.ofReal
      (laneCB3Scale ξ Q δ P W n K /
        lenObs ξ (psiMN Qψ W P 0 n) (rectAB 1 1) x)
    let D (b : ℤ × ℤ) (x : Ω) :=
      (lfppContMetric ξ (fun z => psiMN Qψ W P 0 n z x)
        ((isPsiVersion_psiMN hW (Nat.zero_le n)).cont x)).aroundDist
        (LaneCInputs.sourceAround K m b)
        (LaneCInputs.sourceInner K m b)
        (LaneCInputs.sourceOuter K m b)
    ∀ᵐ ω ∂P,
      (∫⁻ x, R x ^ p * D b x ^ p ∂(κ ω)) ≤
        (∫⁻ x, (R x ^ p) ^ (2 * ((1 + ζ) / ζ)) ∂(κ ω)) ^
          (ζ / (2 * (1 + ζ))) *
        (∫⁻ x, Z x ∂(κ ω)) ^ (ζ / (2 * (1 + ζ))) *
        (ENNReal.ofReal (Real.exp (((K : ℝ) * Real.log 2) *
          (((1 + ζ) * p * ξ) ^ 2) / 2))) ^ (1 / (1 + ζ)) := by
  let κ := condExpKernel P (MeasurableSpace.comap
    (fun y z => psiMN Qψ W P K n z y)
    (inferInstance : MeasurableSpace (ℂ → ℝ)))
  let R : Ω → ℝ≥0∞ := fun x => ENNReal.ofReal
    (laneCB3Scale ξ Q δ P W n K /
      lenObs ξ (psiMN Qψ W P 0 n) (rectAB 1 1) x)
  let D (b : ℤ × ℤ) (x : Ω) :=
    (lfppContMetric ξ (fun z => psiMN Qψ W P 0 n z x)
      ((isPsiVersion_psiMN hW (Nat.zero_le n)).cont x)).aroundDist
      (LaneCInputs.sourceAround K m b)
      (LaneCInputs.sourceInner K m b)
      (LaneCInputs.sourceOuter K m b)
  let Y := laneCJ1WeightedAround Qψ ξ P W hW n K m b
  let hYm := laneC_aemeasurable_J1WeightedAround P W hW Qψ ξ n K m b
  let Y' := hYm.mk Y
  let G : Ω → ℝ≥0∞ := fun x => ENNReal.ofReal
    (Real.exp ((p * ξ) * phiMN W P 0 K (T20.dyCenter K b) x))
  have hLm : Measurable
      (lenObs ξ (psiMN Qψ W P 0 n) (rectAB 1 1)) :=
    measurable_lenObs ((isPsiVersion_psiMN hW (Nat.zero_le n)).cont)
      ((isPsiVersion_psiMN hW (Nat.zero_le n)).meas) _
  have hRm : Measurable R := by
    dsimp [R]
    fun_prop
  have hY'm : Measurable Y' := hYm.measurable_mk
  have hGm : Measurable G := by
    dsimp [G]
    exact ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp
        (measurable_const.mul
          ((isPhiVersion_phiMN hW (Nat.zero_le K)).meas (T20.dyCenter K b))))
  have hDle : ∀ᵐ x ∂P,
      R x ^ p * D b x ^ p ≤ (R x ^ p * Y' x ^ p) * G x := by
    filter_upwards [hYm.ae_eq_mk.symm] with x hx
    dsimp [D]
    rw [laneC_around_rpow_eq_coarse_exp_mul_weighted Qψ ξ P W hW n K m b x p hp.le,
      ← hx]
    change R x ^ p * (G x * Y' x ^ p) ≤ (R x ^ p * Y' x ^ p) * G x
    exact le_of_eq (by ac_rfl)
  have hmFine :=
    (measurable_pi_iff.mpr (isPsiVersion_psiMN (Q := Qψ) hW hKn).meas).comap_le
  have hDcond := laneC_conditional_lintegral_mono_ae P hmFine hDle
  have hYcond := laneC_conditional_lintegral_mono_ae P hmFine hdom
  have hs : 0 ≤ 1 + ζ := by linarith
  have hGpow : (fun x => G x ^ (1 + ζ)) =
      fun x => ENNReal.ofReal
        (Real.exp (((1 + ζ) * p * ξ) *
          phiMN W P 0 K (T20.dyCenter K b) x)) := by
    funext x
    dsimp [G]
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hs, ← Real.exp_mul]
    congr 2
    ring
  have hMGF := laneC_conditional_coarse_phi_exp_moment P W hW Qψ hKn b
    ((1 + ζ) * p * ξ)
  filter_upwards [hDcond, hYcond, hMGF] with ω hd hy hg
  have hH := laneC_triple_holder_at (κ ω)
    (hRm.pow_const p).aemeasurable
    (hY'm.pow_const p).aemeasurable hGm.aemeasurable hζ
  have hq : 0 ≤ 2 * ((1 + ζ) / ζ) := by positivity
  have hYpow : (fun x => (Y' x ^ p) ^ (2 * ((1 + ζ) / ζ))) =
      fun x => Y' x ^ (p * (2 * ((1 + ζ) / ζ))) := by
    funext x
    exact (ENNReal.rpow_mul (Y' x) p (2 * ((1 + ζ) / ζ))).symm
  calc
    _ ≤ ∫⁻ x, (R x ^ p * Y' x ^ p) * G x ∂(κ ω) := hd
    _ ≤ (∫⁻ x, (R x ^ p) ^ (2 * ((1 + ζ) / ζ)) ∂(κ ω)) ^
        (ζ / (2 * (1 + ζ))) *
        (∫⁻ x, (Y' x ^ p) ^ (2 * ((1 + ζ) / ζ)) ∂(κ ω)) ^
        (ζ / (2 * (1 + ζ))) *
        (∫⁻ x, G x ^ (1 + ζ) ∂(κ ω)) ^ (1 / (1 + ζ)) := hH
    _ ≤ (∫⁻ x, (R x ^ p) ^ (2 * ((1 + ζ) / ζ)) ∂(κ ω)) ^
        (ζ / (2 * (1 + ζ))) *
        (∫⁻ x, Z x ∂(κ ω)) ^ (ζ / (2 * (1 + ζ))) *
        (ENNReal.ofReal (Real.exp (((K : ℝ) * Real.log 2) *
          (((1 + ζ) * p * ξ) ^ 2) / 2))) ^ (1 / (1 + ζ)) := by
      rw [hYpow, hGpow]
      gcongr

end SupercriticalLQGUniqueness.B2.DG20Conc
