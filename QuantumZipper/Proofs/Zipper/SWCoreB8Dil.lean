import QuantumZipper.Proofs.Zipper.TipXScaleMass
import QuantumZipper.Proofs.LQG.RegularClosure
import QuantumZipper.Proofs.LQG.GoodSample

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-B8 (1): offset radii from dyadic radii by dilation

For a regular sample `y` and `a > 0`, the boundary approximation of `y` at the offset radius
`a r` is the dyadic-type approximation at radius `r` of the dilated field
`rescale y Q a = y(a ·) + Q log a` (`Q = Qc γ`), with the dilated test function:

  `∫ f d(bdryR γ y (a r)) = ∫ f(a ·) d(bdryR γ (rescale y Q a) r)`  (`integral_bdryR_dilate`),

and at `r = 2^{-k}` the right-hand side is `∫ f(a ·) d(bdryApprox γ (rescale y Q a) k)`
(`integral_bdryR_offset_eq_bdryApprox`). This is the coordinate-change rule for the dilation
`z ↦ a z` (Duplantier–Sheffield 2011, (1.3)/(5.1); `γ Q/2 = 1 + γ²/4`): the offset merging of
`YMergeOffTipStmt` is the dyadic transport for the maps `ψ ∘ (a ·)` and test functions `f(a ·)`,
so no all-radii version of the distortion core is needed (`swcn2_bdryDistFam` with the dilation
as one more parameter of the family). Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace SWCore

theorem integral_bdryR_eq_dens (γ : ℝ) {x : FieldSample} {F : ℂ × ℝ → ℝ}
    (hF : IsRegularWith x F) (r : ℝ) (hr : 0 < r) (g : ℝ → ℝ) :
    ∫ t, g t ∂bdryR γ x r = ∫ t, g t * bdryDens γ x r t := by
  have hFc : Continuous fun t : ℝ => F ((t : ℂ), r) :=
    hF.1.comp_continuous (Complex.continuous_ofReal.prodMk continuous_const)
      fun t => ⟨GaussTK.ofReal_mem_Hbar t, hr⟩
  have hE : (fun t : ℝ => evalReg x (foldedCircle (t : ℂ) r)) = fun t : ℝ => F ((t : ℂ), r) :=
    funext fun t => hF.evalReg_fc_of_mem (GaussTK.ofReal_mem_Hbar t) hr
  have hD : Measurable fun t : ℝ => ENNReal.ofReal (bdryDens γ x r t) := by
    refine ENNReal.measurable_ofReal.comp (measurable_const.mul (Real.measurable_exp.comp
      (measurable_const.mul ?_)))
    rw [hE]; exact hFc.measurable
  unfold bdryR
  rw [integral_withDensity_eq_integral_toReal_smul₀ hD.aemeasurable
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (ae_of_all _ fun t => ?_)
  have h0 : 0 ≤ bdryDens γ x r t :=
    mul_nonneg (Real.rpow_nonneg hr.le _) (Real.exp_pos _).le
  simp only [smul_eq_mul]
  rw [ENNReal.toReal_ofReal h0, mul_comm]

/-- **Offset radius = dilated field at the base radius.** -/
theorem integral_bdryR_dilate {γ : ℝ} (hγ : 0 < γ) {y : FieldSample} {F : ℂ × ℝ → ℝ}
    (hF : IsRegularWith y F) {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (f : ℝ → ℝ) :
    ∫ t, f t ∂bdryR γ y (a * r) = ∫ u, f (a * u) ∂bdryR γ (rescale y (Qc γ) a) r := by
  have hF' := hF.rescale' (Qc γ) ha
  have hE : ∀ u : ℝ, evalReg (rescale y (Qc γ) a) (foldedCircle (u : ℂ) r) =
      evalReg y (foldedCircle ((a * u : ℝ) : ℂ) (a * r)) + Qc γ * Real.log a - 0 := by
    intro u
    rw [hF'.evalReg_fc_of_mem (GaussTK.ofReal_mem_Hbar u) hr,
      hF.evalReg_fc_of_mem (GaussTK.ofReal_mem_Hbar _) (mul_pos ha hr)]
    push_cast; ring
  have hdens : ∀ u, bdryDens γ (rescale y (Qc γ) a) r u = a * bdryDens γ y (a * r) (a * u) := by
    intro u
    have := WedgeUnzip.bdryDens_scale_eq hγ ha hr (hE u)
    simpa using this
  rw [integral_bdryR_eq_dens γ hF (a * r) (mul_pos ha hr),
    integral_bdryR_eq_dens γ hF' r hr]
  simp_rw [hdens]
  have hsub := Measure.integral_comp_mul_left (fun t => f t * bdryDens γ y (a * r) t) a
  have e : ∀ u, f (a * u) * (a * bdryDens γ y (a * r) (a * u)) =
      a * (f (a * u) * bdryDens γ y (a * r) (a * u)) := fun u => by ring
  simp_rw [e]
  rw [integral_const_mul, hsub, abs_inv, abs_of_pos ha, smul_eq_mul, ← mul_assoc,
    mul_inv_cancel₀ ha.ne', one_mul]

/-- **Offset radius `a 2^{-k}` = dyadic approximation of the dilated field.** -/
theorem integral_bdryR_offset_eq_bdryApprox {γ : ℝ} (hγ : 0 < γ) {y : FieldSample}
    {F : ℂ × ℝ → ℝ} (hF : IsRegularWith y F) {a : ℝ} (ha : 0 < a) (k : ℕ) (f : ℝ → ℝ) :
    ∫ t, f t ∂bdryR γ y (a * radius k) =
      ∫ u, f (a * u) ∂bdryApprox γ (rescale y (Qc γ) a) k := by
  rw [integral_bdryR_dilate hγ hF ha (radius_pos k), ← one_mul (radius k),
    GoodSample.bdryR_radius γ (hF.rescale' (Qc γ) ha) k]

end SWCore
end QuantumZipper
