import QuantumZipper.Proofs.LQG.AreaP3bLaw
import QuantumZipper.Proofs.LQG.TwoRadiusTilt

/-!
# M4-P3(b), area version, part 5: the circle-average increment `Ω` and its moments

Continuation of `AreaP3bInner`/`AreaP3bLaw` (handoff `handoff/M4-AREA-P3B.md`, "Remaining"
item 3). For `Ω = omZ X z δ D = fcPairVal X (z, δ, z, D)`:

* `hasLaw_omZ`: `Ω` is a centred Gaussian with variance `log D − log δ` (from
  `AreaExist.hasLaw_fcPairVal'` and `fcPairCov_omZ_self`); this is the interior analogue of
  `FracMom.hasLaw_omegaAvg`, reflecting the independent increments of the circle average,
  Duplantier–Sheffield, Invent. Math. 185 (2011), §3.1.
* `lintegral_omZ_factor_rpow`: the `p`-th moment of the lognormal factor,
  `E[(e^{γΩ} δ^{γ²/2})^p] = δ^{pγ²/2} e^{(log D − log δ)(pγ)²/2}` (`3.1` with
  `δ^{-γ²/2}`-normalization), the interior analogue of `FracMom.lintegral_omega_factor_rpow`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Real
open scoped NNReal ENNReal ComplexConjugate

namespace QuantumZipper
namespace AreaP3b

open GaussTK KernelId FinArea

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → FieldSample}

/-- **Law of `Ω = Z_δ(z) − Z_D(z)`**: centred Gaussian with variance `log D − log δ`. -/
theorem hasLaw_omZ (hX : IsFreeGFFModConstH X P) {z : ℂ} {δ D : ℝ} (hδ : 0 < δ)
    (hδD : δ ≤ D) (hDz : D ≤ z.im) :
    HasLaw (omZ X z δ D) (gaussianReal 0 (log D - log δ).toNNReal) P := by
  have h := AreaExist.hasLaw_fcPairVal' hX (P := P) (good_omZ (z := z) (D := D) hδ hδD hDz)
  rwa [fcPairCov_omZ_self hδ hδD hDz] at h

/-- **The `p`-th moment of the lognormal factor** (handoff item 3): for `0 < δ ≤ D ≤ Im z` and
`p ≥ 0`, `E[(e^{γΩ} δ^{γ²/2})^p] = δ^{pγ²/2} e^{(log D − log δ)(pγ)²/2}`. -/
theorem lintegral_omZ_factor_rpow (hX : IsFreeGFFModConstH X P) (γ : ℝ) {z : ℂ} {δ D p : ℝ}
    (hδ : 0 < δ) (hδD : δ ≤ D) (hDz : D ≤ z.im) (hp : 0 ≤ p) :
    ∫⁻ ω, ENNReal.ofReal (exp (γ * omZ X z δ D ω) * δ ^ (γ ^ 2 / 2)) ^ p ∂P =
      ENNReal.ofReal (δ ^ (p * (γ ^ 2 / 2)) *
        exp ((log D - log δ) * (p * γ) ^ 2 / 2)) := by
  have hv : ((log D - log δ).toNNReal : ℝ) = log D - log δ :=
    Real.coe_toNNReal _ (sub_nonneg.mpr (log_le_log hδ hδD))
  -- push the `p`-th power onto the exponential and the deterministic factor
  have hreal : ∀ ω, exp (γ * omZ X z δ D ω) ^ p * (δ ^ (γ ^ 2 / 2)) ^ p =
      δ ^ (p * (γ ^ 2 / 2)) * exp (p * γ * omZ X z δ D ω) := by
    intro ω
    rw [← exp_mul, ← rpow_mul hδ.le]
    ring
  have hpt : ∀ ω, ENNReal.ofReal (exp (γ * omZ X z δ D ω) * δ ^ (γ ^ 2 / 2)) ^ p =
      ENNReal.ofReal (δ ^ (p * (γ ^ 2 / 2)) * exp (p * γ * omZ X z δ D ω)) := by
    intro ω
    rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hp,
      Real.mul_rpow (exp_pos _).le (rpow_pos_of_pos hδ _).le]
    exact congrArg ENNReal.ofReal (hreal ω)
  simp_rw [hpt]
  -- integrate the Gaussian factor
  have hL := hasLaw_omZ hX (P := P) hδ hδD hDz
  have hint : Integrable (fun ω => exp (0 + p * γ * omZ X z δ D ω)) P :=
    hL.integrable_comp (TwoRadius.integrable_exp_mul_add_gaussianReal _ (p * γ) 0)
  simp only [zero_add] at hint
  rw [← ofReal_integral_eq_lintegral_ofReal (hint.const_mul _)
    (ae_of_all _ fun ω => by simp only [Pi.zero_apply]; positivity), integral_const_mul]
  have h2 : ∫ x, exp (p * γ * x) ∂(gaussianReal 0 (log D - log δ).toNNReal) =
      exp (((log D - log δ).toNNReal : ℝ) * (p * γ) ^ 2 / 2) := by
    simpa only [zero_add] using
      TwoRadius.integral_exp_mul_add_gaussianReal (log D - log δ).toNNReal (p * γ) 0
  rw [show ∫ ω, exp (p * γ * omZ X z δ D ω) ∂P = exp ((log D - log δ) * (p * γ) ^ 2 / 2) by
    have hc := hL.integral_comp (f := fun x => exp (p * γ * x)) (by fun_prop)
    simp only [Function.comp_apply] at hc
    rw [hc, h2, hv]]

end AreaP3b
end QuantumZipper
