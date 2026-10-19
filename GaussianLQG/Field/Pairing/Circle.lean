import GaussianLQG.Field.Pairing.Linear
import LQGDimension.LFPP.CouplingAux2

/-!
# Circle energies and circle averages of the coordinate field

* `energy_circleMeasure`: `ℰ(σ_{z,r}, σ_{z,r}) = -log r + 2 ∫ log|u|₊ dσ_{z,r}(u)` (`r > 0`), from
  the circle average `∫ log|u - v| dσ_{z,r}(u) = log r` for `|v - z| = r`
  (`LQGDimension.Coupling.lPair_self`).
* `energy_circleMeasure_zero`: `ℰ(σ_{0,R}, σ_{0,R}) = log R` for `R ≥ 1`.
* `energy_circleMeasure_le`: `ℰ(σ_{z,r}, σ_{z,r}) ≤ log⁺(1/r) + 2 log⁺(|z| + r)`, the bound of
  blueprint Lemma `lem:euclidean` Step 1.
* `hasLaw_pairing_circleMeasure_zero`, `integral_exp_mul_pairing_circleMeasure_zero`:
  `h_R(0) ∼ N(0, log R)` and `E e^{t h_R(0)} = R^{t²/2}` for `R ≥ 1`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal

namespace GaussianLQG

variable {e : ℕ → ℂ → ℝ}

theorem logEnergy_circleMeasure (z : ℂ) {r : ℝ} (hr : 0 < r) :
    logEnergy (circleMeasure z r) (circleMeasure z r) = -Real.log r := by
  rw [logEnergy_eq_integral_prod (isRegular_circleMeasure z hr) (isRegular_circleMeasure z hr),
    integral_neg, circleMeasure_eq_circMeas]
  exact congrArg Neg.neg (LQGDimension.Coupling.lPair_self z hr)

/-- `ℰ(σ_{z,r}, σ_{z,r}) = -log r + 2 ∫ log|u|₊ dσ_{z,r}(u)`. -/
theorem energy_circleMeasure (z : ℂ) {r : ℝ} (hr : 0 < r) :
    energy (circleMeasure z r) (circleMeasure z r) =
      -Real.log r + 2 * ∫ u, Real.log (max 1 ‖u‖) ∂circleMeasure z r := by
  rw [energy_eq_logEnergy_add (isRegular_circleMeasure z hr) (isRegular_circleMeasure z hr),
    logEnergy_circleMeasure z hr, probReal_univ]
  ring

theorem ae_norm_sub_circleMeasure (z : ℂ) (r : ℝ) :
    ∀ᵐ u ∂circleMeasure z r, ‖u - z‖ = |r| := by
  rw [circleMeasure_eq_circMeas]
  exact LQGDimension.Coupling.ae_circMeas z r

theorem integral_log_max_one_circleMeasure_zero {R : ℝ} (hR : 1 ≤ R) :
    ∫ u, Real.log (max 1 ‖u‖) ∂circleMeasure 0 R = Real.log R := by
  have h : ∀ᵐ u ∂circleMeasure 0 R, Real.log (max 1 ‖u‖) = Real.log R := by
    filter_upwards [ae_norm_sub_circleMeasure 0 R] with u hu
    rw [sub_zero, abs_of_nonneg (by linarith)] at hu
    rw [hu, max_eq_right hR]
  rw [integral_congr_ae h, integral_const, probReal_univ, one_smul]

/-- `ℰ(σ_{0,R}, σ_{0,R}) = log R` for `R ≥ 1`. -/
theorem energy_circleMeasure_zero {R : ℝ} (hR : 1 ≤ R) :
    energy (circleMeasure 0 R) (circleMeasure 0 R) = Real.log R := by
  rw [energy_circleMeasure 0 (by linarith), integral_log_max_one_circleMeasure_zero hR]
  ring

theorem log_max_one_le_posLog {x y : ℝ} (hxy : x ≤ y) :
    Real.log (max 1 x) ≤ Real.posLog y := by
  have hy : 0 ≤ max 1 y - 1 := by linarith [le_max_left 1 y]
  calc Real.log (max 1 x) ≤ Real.log (max 1 y) :=
        Real.log_le_log (by positivity) (max_le_max le_rfl hxy)
    _ ≤ Real.posLog y := by
        rcases le_or_gt y 1 with h | h
        · rw [max_eq_left h, Real.log_one]; exact Real.posLog_nonneg
        · rw [max_eq_right h.le]; exact le_max_right _ _

/-- The bound `ℰ(σ_{z,r}, σ_{z,r}) ≤ log⁺(1/r) + 2 log⁺(|z| + r)` (blueprint Lemma
`lem:euclidean`, Step 1). -/
theorem energy_circleMeasure_le (z : ℂ) {r : ℝ} (hr : 0 < r) :
    energy (circleMeasure z r) (circleMeasure z r) ≤
      Real.posLog r⁻¹ + 2 * Real.posLog (‖z‖ + r) := by
  rw [energy_circleMeasure z hr]
  have h1 : -Real.log r ≤ Real.posLog r⁻¹ := by
    rw [← Real.log_inv]; exact le_max_right _ _
  have h2 : ∫ u, Real.log (max 1 ‖u‖) ∂circleMeasure z r ≤ Real.posLog (‖z‖ + r) := by
    have hle : ∀ᵐ u ∂circleMeasure z r, Real.log (max 1 ‖u‖) ≤ Real.posLog (‖z‖ + r) := by
      filter_upwards [ae_norm_sub_circleMeasure z r] with u hu
      refine log_max_one_le_posLog ?_
      rw [abs_of_pos hr] at hu
      calc ‖u‖ = ‖(u - z) + z‖ := by rw [sub_add_cancel]
        _ ≤ ‖u - z‖ + ‖z‖ := norm_add_le _ _
        _ = ‖z‖ + r := by rw [hu]; ring
    calc ∫ u, Real.log (max 1 ‖u‖) ∂circleMeasure z r
        ≤ ∫ _u, Real.posLog (‖z‖ + r) ∂circleMeasure z r :=
          integral_mono_ae (isRegular_circleMeasure z hr).integrable_log_max_one_norm
            (integrable_const _) hle
      _ = Real.posLog (‖z‖ + r) := by rw [integral_const, probReal_univ, one_smul]
  linarith

/-! ## Circle averages of the coordinate field -/

/-- `h_r(z) := (h, σ_{z,r}) ∼ N(0, ℰ(σ_{z,r}, σ_{z,r}))`. -/
theorem hasLaw_pairing_circleMeasure (he : IsGFFFrame e) (z : ℂ) {r : ℝ} (hr : 0 < r) :
    HasLaw (pairing e (circleMeasure z r))
      (gaussianReal 0 (energy (circleMeasure z r) (circleMeasure z r)).toNNReal) stdP :=
  hasLaw_pairing he (isRegular_circleMeasure z hr)

/-- `h_R(0) ∼ N(0, log R)` for `R ≥ 1`. -/
theorem hasLaw_pairing_circleMeasure_zero (he : IsGFFFrame e) {R : ℝ} (hR : 1 ≤ R) :
    HasLaw (pairing e (circleMeasure 0 R)) (gaussianReal 0 (Real.log R).toNNReal) stdP := by
  have h := hasLaw_pairing_circleMeasure he 0 (r := R) (by linarith)
  rwa [energy_circleMeasure_zero hR] at h

/-- `E e^{t h_R(0)} = R^{t²/2}` for `R ≥ 1`. -/
theorem integral_exp_mul_pairing_circleMeasure_zero (he : IsGFFFrame e) {R : ℝ} (hR : 1 ≤ R)
    (t : ℝ) :
    ∫ ω, Real.exp (t * pairing e (circleMeasure 0 R) ω) ∂stdP = R ^ (t ^ 2 / 2) := by
  rw [integral_exp_mul_of_hasLaw_gaussianReal (hasLaw_pairing_circleMeasure_zero he hR),
    Real.coe_toNNReal _ (Real.log_nonneg hR), Real.rpow_def_of_pos (by linarith)]
  ring_nf

theorem integrable_exp_mul_pairing_circleMeasure (he : IsGFFFrame e) (z : ℂ) {r : ℝ}
    (hr : 0 < r) (t : ℝ) :
    Integrable (fun ω => Real.exp (t * pairing e (circleMeasure z r) ω)) stdP :=
  integrable_exp_mul_of_hasLaw_gaussianReal (hasLaw_pairing_circleMeasure he z hr) t

end GaussianLQG
