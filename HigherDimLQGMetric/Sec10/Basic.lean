import HigherDimLQGMetric.Frozen.IsStrongExpMetric
import HigherDimLQGMetric.Field.Basic
import HigherDimLQGMetric.Field.Affine
import HigherDimLQGMetric.Metric.ContMetric
import HigherDimLQGMetric.Frozen.NormalizedAtScale
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Elementary consequences of the strong exponential metric axioms

These are the algebraic parts of Lemma 10.1: translation covariance is coordinate covariance
at scale one, and the proposed sharp normalizers are positive at every positive scale.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

variable {d : ℕ} {ξ Q : ℝ} {D : DistRd d → ContMetric d}

/-- Coordinate covariance at scale one gives translation covariance. -/
theorem IsStrongExpMetric.ae_translation (hD : IsStrongExpMetric d ξ Q D)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d) (hh : IsLGFPlusCont h P) (z : Rd d) :
    ∀ᵐ ω ∂P, ∀ u v : Rd d,
      (D (affineComp 1 z (h ω))).1 (u, v) = (D (h ω)).1 (u + z, v + z) := by
  filter_upwards [hD.coord P h hh 1 one_pos z] with ω hω u v
  simpa only [one_smul, Real.log_one, mul_zero, addConst_zero] using (hω u v).symm

/-- The normalizers prescribed by exact coordinate covariance are positive. -/
theorem s8a_sharpNormalizer_pos (r : ℝ) (hr : 0 < r) : 0 < r ^ (ξ * Q) :=
  Real.rpow_pos_of_pos hr _

/-- Positive normalization and a nonzero coordinate dilation preserve the continuous metric
property. -/
theorem s8a_normalizedAtScale_isContinuousMetric
    (ξ : ℝ) (D : DistRd d → ContMetric d) (c : ℝ → ℝ)
    (g : DistRd d) {r : ℝ} (hr : 0 < r) (hc : 0 < c r) :
    IsContinuousMetric (normalizedAtScale ξ D c g r) := by
  let a : ℝ := (c r)⁻¹ * Real.exp (-ξ * sphereAvg g r 0)
  have ha : 0 < a := mul_pos (inv_pos.mpr hc) (Real.exp_pos _)
  let E : ContMetric d := ((D g).affine r hr.ne' 0).smul a ha
  have he : E.1 = normalizedAtScale ξ D c g r := by
    ext p
    simp only [E, a, ContMetric.smul_apply, ContMetric.affine_apply,
      normalizedAtScale, ContinuousMap.smul_apply, ContinuousMap.comp_apply,
      ContinuousMap.coe_mk, smul_eq_mul, add_zero]
  rw [← he]
  exact E.2

end HigherDimLQGMetric
