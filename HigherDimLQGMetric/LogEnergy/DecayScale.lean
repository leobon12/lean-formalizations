import HigherDimLQGMetric.LogEnergy.DecayUnit
set_option autoImplicit false
noncomputable section
open MeasureTheory
open HigherDimLFPP (Rd)
namespace HigherDimLQGMetric

theorem testAffinePull_inv_tsupport_ann {d : ℕ} {a b r : ℝ}
    (hr : 0 < r) (φ : TestRd d)
    (hφ : tsupport φ ⊆ ann 0 (a*r) (b*r)) :
    tsupport (testAffinePull r⁻¹ 0 φ) ⊆ ann 0 a b := by
  have heq : (testAffinePull r⁻¹ 0 φ : Rd d → ℝ) =
      φ ∘ (fun x : Rd d => r • x) := by
    funext x
    rw [testAffinePull_apply (inv_ne_zero hr.ne') 0 φ]
    simp
  rw [heq]
  intro x hx
  have hc : Continuous (fun y : Rd d => r • y) := by fun_prop
  have hmem : r • x ∈ tsupport φ :=
    tsupport_comp_subset_preimage (φ : Rd d → ℝ) hc hx
  have hscaled := hφ hmem
  have hnorm : ‖r • x‖ = r*‖x‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr]
  change a*r < ‖r • x - 0‖ ∧ ‖r • x - 0‖ < b*r at hscaled
  change a < ‖x - 0‖ ∧ ‖x - 0‖ < b
  simp only [sub_zero] at hscaled ⊢
  rw [hnorm] at hscaled
  constructor <;> nlinarith [hscaled.1, hscaled.2]

theorem testAffinePull_inv_inv {d : ℕ} {r : ℝ} (hr : 0 < r) (φ : TestRd d) :
    testAffinePull r 0 (testAffinePull r⁻¹ 0 φ) = φ := by
  rw [testAffinePull_testAffinePull]
  rw [mul_inv_cancel₀ hr.ne', smul_zero, zero_add,
    testAffinePull_one_zero, ContinuousLinearMap.id_apply]

theorem logNorm_testAffinePull_eq {d : ℕ} (φ : TestRd0 d) {r : ℝ}
    (hr : 0 < r) :
    logNorm (testAffinePull r 0 φ.1) = r^d * logNorm φ.1 := by
  rw [logNorm, logCovRd_testAffinePull φ.1 φ.1 φ.2 hr 0]
  have hpow : r^(2*d) = (r^d)^2 := by ring
  rw [hpow, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (pow_nonneg hr.le _)]
  rfl
end HigherDimLQGMetric
