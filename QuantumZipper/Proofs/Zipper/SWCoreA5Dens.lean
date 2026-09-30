import QuantumZipper.Proofs.Zipper.SWCoreA5Class
import QuantumZipper.Proofs.Zipper.AreaCoordCov

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-A5 (3): the density of the pushed approximation, uniformly over a class

For `ψ` in a rational area class, the density of `areaApprox γ (x ∘ ψ + Q log|ψ'|) k` at `z ∈ K`
factorizes exactly (`γ Q = 2 + γ²/2`) as `‖ψ'(z)‖² · μ^x_{2^{-k}‖ψ'(z)‖}(ψ z) · e^{γ err}`
(`areaDensK_coordChange_eq`), and the error `err` is uniformly small over the class
(`eventually_abs_err_le`): this is the class-uniform distortion core `AreaDistClassGood`
(SW Lemmas 3.4–3.5) plus the uniform log-average estimate `areaClass_logAvg`. Own bookkeeping,
following `E6.areaDensK_unzipped_eq` (`AreaCoordCirc.lean`).
-/

noncomputable section

open MeasureTheory Filter Set Function Metric
open scoped Topology ENNReal

namespace QuantumZipper
namespace SWCore

open E6

/-- The distortion error of the pushed density at `(z, 2^{-k})`. -/
def pushErr (γ : ℝ) (x : FieldSample) (ψ : ℂ → ℂ) (k : ℕ) (z : ℂ) : ℝ :=
  avgReg (coordChange x ψ (Qc γ)) k z - Qc γ * Real.log ‖deriv ψ z‖ -
    evalReg x (foldedCircle (ψ z) (radius k * ‖deriv ψ z‖))

/-- **Exact factorization of the pushed density** (`γ Q = 2 + γ²/2`). -/
theorem areaDensK_coordChange_eq {γ : ℝ} (hγ : 0 < γ) (x : FieldSample) (ψ : ℂ → ℂ) (k : ℕ)
    {z : ℂ} (hz : deriv ψ z ≠ 0) :
    areaDensK γ (coordChange x ψ (Qc γ)) k z =
      ‖deriv ψ z‖ ^ 2 * areaDens γ x (radius k * ‖deriv ψ z‖) (ψ z) *
        Real.exp (γ * pushErr γ x ψ k z) := by
  set a := ‖deriv ψ z‖ with ha_def
  have ha : 0 < a := norm_pos_iff.2 hz
  have hr : 0 < radius k := radius_pos k
  have hQ : γ * Qc γ = 2 + γ ^ 2 / 2 := by
    unfold Qc; field_simp
  have ha2 : a ^ 2 = Real.exp (2 * Real.log a) := by
    rw [show 2 * Real.log a = Real.log a + Real.log a by ring, Real.exp_add, Real.exp_log ha]
    ring
  have hra : (radius k * a) ^ (γ ^ 2 / 2) =
      radius k ^ (γ ^ 2 / 2) * Real.exp (Real.log a * (γ ^ 2 / 2)) := by
    rw [Real.mul_rpow hr.le ha.le, Real.rpow_def_of_pos ha]
  unfold areaDensK areaDens pushErr
  rw [← ha_def, ha2, hra]
  set A := avgReg (coordChange x ψ (Qc γ)) k z
  set E := evalReg x (foldedCircle (ψ z) (radius k * a))
  have hexp : Real.exp (2 * Real.log a) * Real.exp (Real.log a * (γ ^ 2 / 2)) *
      Real.exp (γ * E) * Real.exp (γ * (A - Qc γ * Real.log a - E)) = Real.exp (γ * A) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    linear_combination (-Real.log a) * hQ
  rw [← hexp]
  ring

end SWCore
end QuantumZipper
