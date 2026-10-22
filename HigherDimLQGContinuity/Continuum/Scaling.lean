import HigherDimLQGContinuity.Core.Interfaces
import HigherDimLQGContinuity.Norm.ScalingSets
import HigherDimLQGContinuity.Norm.PinGauss
import HigherDimLQGMetric.Shell.Defs
import GaussianLQG.Probability.Gaussian

/-!
# Scaling of continuum annular crossings

The metric and internal scaling identities are supplied by packet P2. This
module specializes them to the crossing used in the lower modulus and escape
estimates of Appendix A.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Metric
open scoped ENNReal

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- Deterministic transfer of a global sphere crossing under an affine metric scaling. -/
theorem l2_across_affine_of_pair {d : ℕ} {G G' : ContMetric d}
    {r c : ℝ} (hr : 0 < r) (hc : 0 < c) (z : Rd d)
    (h : ∀ x y : Rd d, G.1 (r • x + z, r • y + z) = c * G'.1 (x, y))
    (a b : ℝ) :
    acrossDist G z (r * a) (r * b) = ENNReal.ofReal c * acrossDist G' 0 a b := by
  have hsphere (t : ℝ) :
      sphere z (r * t) = (fun w : Rd d => r • w + z) '' sphere 0 t := by
    simpa only [smul_zero, zero_add] using (p2_image_affine_sphere hr z (0 : Rd d) t).symm
  unfold acrossDist
  rw [hsphere a, hsphere b]
  simp only [iInf_image, h, ENNReal.ofReal_mul hc.le]
  simp only [ENNReal.mul_iInf_of_ne (ENNReal.ofReal_pos.mpr hc).ne' ENNReal.ofReal_ne_top]

/-- Almost-sure scaling of the global annular crossing, under the unit pin. -/
theorem l2_across_scaling {d : ℕ} (hd : 2 ≤ d) {ξ : ℝ}
    (hξ : 0 < ξ)
    {D : DistRd d → ContMetric d}
    (hD : IsStrongExpMetric d ξ (distExp d ξ) D)
    {r : ℝ} (hr : 0 < r) (z : Rd d) (a b : ℝ) :
    ∀ᵐ g ∂(normLGFLaw d),
      acrossDist (rho D g) z (r * a) (r * b) =
        ENNReal.ofReal (scaleS d ξ 1 r z g) *
          acrossDist (rho D (recentre 1 r z g)) 0 a b := by
  have hs := rho_scaling_of hd hξ hD (s := 1) one_pos hr z
  rw [pinLaw_one hd] at hs
  filter_upwards [hs] with g hg
  exact l2_across_affine_of_pair hr (scaleS_pos d ξ 1 hr z g) z hg.1 a b

/-- The Gaussian exponential factor in the crossing scale has an exact finite moment. -/
theorem l2_lintegral_exp_sphereAvg {d : ℕ} (hd : 2 ≤ d)
    {r : ℝ} (hr : 0 < r) (z : Rd d) (t : ℝ) :
    ∫⁻ g, ENNReal.ofReal (Real.exp (t * sphereAvg g r z)) ∂(normLGFLaw d) =
      ENNReal.ofReal
        (Real.exp (Var[fun g : DistRd d => sphereAvg g r z; normLGFLaw d] * t ^ 2 / 2)) := by
  have hgauss := hasGaussianLaw_sphereAvg_pinLaw hd one_pos hr z
  rw [pinLaw_one hd] at hgauss
  let v : NNReal := (Var[fun g : DistRd d => sphereAvg g r z; normLGFLaw d]).toNNReal
  have hlaw : HasLaw (fun g : DistRd d => sphereAvg g r z) (gaussianReal 0 v)
      (normLGFLaw d) := GaussianLQG.hasLaw_of_hasGaussianLaw hgauss.1 hgauss.2
  have hint := GaussianLQG.integrable_exp_mul_of_hasLaw_gaussianReal hlaw t
  rw [← ofReal_integral_eq_lintegral_ofReal hint (ae_of_all _ fun _ => (Real.exp_pos _).le)]
  rw [GaussianLQG.integral_exp_mul_of_hasLaw_gaussianReal hlaw t]
  congr 2
  exact congrArg (fun x : ℝ => x * t ^ 2 / 2)
    (Real.coe_toNNReal _ (variance_nonneg _ _))

/-- Recentring the unit-pinned field preserves integrals of measurable nonnegative observables. -/
theorem l2_lintegral_recentre {d : ℕ} (hd : 2 ≤ d)
    {r : ℝ} (hr : 0 < r) (z : Rd d) (F : DistRd d → ℝ≥0∞)
    (hF : Measurable F) :
    (∫⁻ g, F (recentre 1 r z g) ∂(normLGFLaw d)) =
      ∫⁻ g, F g ∂(normLGFLaw d) := by
  have hmeasure := recentre_law hd one_pos one_pos hr z
  rw [pinLaw_one hd] at hmeasure
  calc
    (∫⁻ g, F (recentre 1 r z g) ∂(normLGFLaw d)) =
        ∫⁻ g, F g ∂Measure.map (recentre 1 r z) (normLGFLaw d) :=
      (lintegral_map hF (measurable_recentre 1 r z)).symm
    _ = ∫⁻ g, F g ∂(normLGFLaw d) := by rw [hmeasure]

/-- Factor the inverse power of a random metric scaling into a deterministic power and a Gaussian exponential. -/
theorem l2_scaleS_inv_rpow {d : ℕ} (ξ q : ℝ) (hξ : 0 < ξ) (hq : 0 ≤ q)
    {r : ℝ} (hr : 0 < r) (z : Rd d) (g : DistRd d) :
    (ENNReal.ofReal (scaleS d ξ 1 r z g))⁻¹ ^ q =
      (ENNReal.ofReal (r ^ (ξ * distExp d ξ)))⁻¹ ^ q *
        ENNReal.ofReal (Real.exp (-q * ξ * sphereAvg g r z)) := by
  have hpow : 0 < r ^ (ξ * distExp d ξ) := Real.rpow_pos_of_pos hr _
  have hexp : 0 < Real.exp (ξ * sphereAvg g r z) := Real.exp_pos _
  have he : (ENNReal.ofReal (Real.exp (ξ * sphereAvg g r z)))⁻¹ ^ q =
      ENNReal.ofReal (Real.exp (-q * ξ * sphereAvg g r z)) := by
    rw [← ENNReal.ofReal_inv_of_pos hexp]
    rw [ENNReal.ofReal_rpow_of_nonneg (inv_nonneg.mpr hexp.le) hq]
    congr 1
    rw [← Real.exp_neg, ← Real.exp_mul]
    congr 1
    ring
  rw [scaleS, phiXi_of_pos hξ, ENNReal.ofReal_mul hpow.le,
    ENNReal.mul_inv (Or.inl (ENNReal.ofReal_pos.mpr hpow).ne')
      (Or.inl ENNReal.ofReal_ne_top),
    ENNReal.mul_rpow_of_nonneg _ _ hq, one_mul, he]

end HigherDimLQGContinuity
