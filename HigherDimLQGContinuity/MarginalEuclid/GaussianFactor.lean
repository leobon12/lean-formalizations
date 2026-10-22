import HigherDimLQGContinuity.MarginalEuclid.PairRep
import GaussianLQG.Probability.Gaussian

/-!
# Gaussian moment generating function for the sphere-average scaling factor
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- The lower-integral moment generating function of the pinned sphere average. -/
theorem lintegral_exp_mul_pair_sphereAvg {d : ℕ} (hd : 3 ≤ d)
    {r : ℝ} (hr : 0 < r) (x : Rd d) (t : ℝ) :
    ∫⁻ g, ENNReal.ofReal (Real.exp (t * sphereAvg g r x)) ∂(normLGFLaw d) =
      ENNReal.ofReal
        (Real.exp (Var[fun g : DistRd d => sphereAvg g r x; normLGFLaw d] * t ^ 2 / 2)) := by
  let Z : DistRd d → ℝ := fun g => sphereAvg g r x
  have hG := (pair_sphereAvg_gaussian hd hr x).1
  have hmap := hG.map_eq_gaussianReal
  rw [(pair_sphereAvg_gaussian hd hr x).2] at hmap
  have hlaw : HasLaw Z (gaussianReal 0 (Var[Z; normLGFLaw d]).toNNReal) (normLGFLaw d) :=
    ⟨hG.aemeasurable, hmap⟩
  have hi : Integrable (fun g => Real.exp (t * Z g)) (normLGFLaw d) :=
    GaussianLQG.integrable_exp_mul_of_hasLaw_gaussianReal hlaw t
  have h0 : 0 ≤ᵐ[normLGFLaw d] fun g => Real.exp (t * Z g) :=
    ae_of_all _ fun g => (Real.exp_pos _).le
  rw [← ofReal_integral_eq_lintegral_ofReal hi h0]
  have h := integral_exp_mul_sphereAvg_pinLaw (by omega : 2 ≤ d)
    (s₀ := 1) one_pos hr x t
  rw [pinLaw_one (by omega : 2 ≤ d)] at h
  exact congrArg ENNReal.ofReal h

end HigherDimLQGContinuity
