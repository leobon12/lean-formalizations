/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.RingTheory.Complex
import Mathlib.RingTheory.Norm.Transitivity
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Topology.Algebra.Module.Determinant

/-!
# Conformal invariance of the Dirichlet integral

Packet PROVE-SEC6-A (specification §6.1, proof of Aux. lemma 29, `source/spec/p145-192.md`,
p. 165): "Set `v_r = b_r ∘ f`. Conformal invariance of the Dirichlet integral gives
`∫_𝔻 |∇v_r|² = ∫_O |∇b_r|²`."

For `f` holomorphic and injective on the unit disk, the real derivative of `f` at `ζ` is
multiplication by `f'(ζ)`, with Jacobian `|f'(ζ)|²` (`det_realDeriv`); the change of variables
formula then gives `∫_𝔻 |f'|² (g ∘ f) = ∫_{f(𝔻)} g` (`lintegral_mul_comp_eq`). For `b` of class
`C¹`, `‖D(b ∘ f)(ζ)‖ ≤ ‖Db(f ζ)‖ |f'(ζ)|`, whence `∫_𝔻 ‖D(b∘f)‖² ≤ ∫_ℂ ‖Db‖²`
(`lintegral_norm_comp_sq_le`; only this inequality is used).
-/

noncomputable section

open Complex MeasureTheory Metric Set
open scoped ENNReal

namespace InteractingSLE.Sec6

/-- The real derivative of a holomorphic map with complex derivative `c`. -/
abbrev realDeriv (c : ℂ) : ℂ →L[ℝ] ℂ :=
  ((ContinuousLinearMap.smulRight (1 : ℂ →L[ℂ] ℂ) c).restrictScalars ℝ)

theorem det_realDeriv (c : ℂ) : (realDeriv c).det = ‖c‖ ^ 2 := by
  simp [realDeriv, ContinuousLinearMap.det, LinearMap.det_restrictScalars,
    Algebra.norm_complex_eq, Complex.normSq_eq_norm_sq]

theorem norm_realDeriv (c : ℂ) : ‖realDeriv c‖ = ‖c‖ := by
  rw [realDeriv, ContinuousLinearMap.norm_restrictScalars, ContinuousLinearMap.norm_smulRight_apply,
    norm_one, one_mul]

theorem hasFDerivAt_realDeriv {f : ℂ → ℂ} {ζ : ℂ} (hf : DifferentiableAt ℂ f ζ) :
    HasFDerivAt f (realDeriv (deriv f ζ)) ζ :=
  hf.hasDerivAt.hasFDerivAt.restrictScalars ℝ

/-- **Change of variables for a conformal map of the disk.** -/
theorem lintegral_mul_comp_eq {f : ℂ → ℂ} (hfd : DifferentiableOn ℂ f (ball 0 1))
    (hfi : InjOn f (ball 0 1)) (g : ℂ → ℝ≥0∞) :
    ∫⁻ ζ in ball (0 : ℂ) 1, ENNReal.ofReal (‖deriv f ζ‖ ^ 2) * g (f ζ) =
      ∫⁻ z in f '' ball 0 1, g z := by
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume measurableSet_ball
    (f' := fun ζ => realDeriv (deriv f ζ))
    (fun ζ hζ => (hasFDerivAt_realDeriv (hfd.differentiableAt (isOpen_ball.mem_nhds hζ))).hasFDerivWithinAt)
    hfi g]
  refine setLIntegral_congr_fun measurableSet_ball fun ζ _ => ?_
  rw [det_realDeriv, abs_of_nonneg (sq_nonneg _)]

/-- **Conformal invariance of the Dirichlet integral** (inequality form). -/
theorem lintegral_norm_comp_sq_le {f : ℂ → ℂ} (hfd : DifferentiableOn ℂ f (ball 0 1))
    (hfi : InjOn f (ball 0 1)) (Db : ℂ → ℂ →L[ℝ] ℝ) :
    ∫⁻ ζ in ball (0 : ℂ) 1, ENNReal.ofReal (‖(Db (f ζ)).comp (realDeriv (deriv f ζ))‖ ^ 2) ≤
      ∫⁻ z, ENNReal.ofReal (‖Db z‖ ^ 2) := by
  calc ∫⁻ ζ in ball (0 : ℂ) 1, ENNReal.ofReal (‖(Db (f ζ)).comp (realDeriv (deriv f ζ))‖ ^ 2)
      ≤ ∫⁻ ζ in ball (0 : ℂ) 1, ENNReal.ofReal (‖deriv f ζ‖ ^ 2) *
          ENNReal.ofReal (‖Db (f ζ)‖ ^ 2) := by
        refine lintegral_mono fun ζ => ?_
        rw [← ENNReal.ofReal_mul (sq_nonneg _)]
        refine ENNReal.ofReal_le_ofReal ?_
        have h := ContinuousLinearMap.opNorm_comp_le (Db (f ζ)) (realDeriv (deriv f ζ))
        rw [norm_realDeriv] at h
        calc ‖(Db (f ζ)).comp (realDeriv (deriv f ζ))‖ ^ 2 ≤ (‖Db (f ζ)‖ * ‖deriv f ζ‖) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) h 2
          _ = ‖deriv f ζ‖ ^ 2 * ‖Db (f ζ)‖ ^ 2 := by ring
    _ = ∫⁻ z in f '' ball 0 1, ENNReal.ofReal (‖Db z‖ ^ 2) :=
        lintegral_mul_comp_eq hfd hfi fun z => ENNReal.ofReal (‖Db z‖ ^ 2)
    _ ≤ ∫⁻ z, ENNReal.ofReal (‖Db z‖ ^ 2) := setLIntegral_le_lintegral _ _

end InteractingSLE.Sec6
