/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec6.Prop61Mean
import InteractingSLE.Spec.Supplement.GW2FbMean

/-! # Uniqueness of the deterministic harmonic centering of GW2's field -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory Set
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)

universe u

namespace InteractingSLE.Theorem14.GW2Sf

open WholeField

/-- Two deterministic harmonic centerings which give centered GFFs agree on
 the half plane. This lets the union mean use any supplied harmonic centering. -/
theorem eqOn_of_isZeroBoundaryGFF_centredField
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {u v : ℂ → ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u H)
    (hv : InnerProductSpace.HarmonicOnNhd v H)
    (hzu : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u) P)
    (hzv : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h v) P) :
    EqOn u v H := by
  apply Sec6.eqOn_of_integral_mul_eq QuantumZipper.isOpen_H subset_rfl hu hv
  intro φ _
  have hi := (hzu.process.gaussian.hasGaussianLaw_eval φ).memLp_two.integrable one_le_two
  have he : (fun ω => centredField h v ω φ) =
      fun ω => centredField h u ω φ +
        (SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens u φ -
          SupercriticalConformalCovariance.GM24.smoothDist upperHalfPlaneOpens v φ) := by
    funext ω
    simp only [centredField, sub_apply]
    ring
  have hz := hzv.process.centered φ
  rw [he, integral_add hi (integrable_const _), hzu.process.centered φ,
    integral_const, probReal_univ, smul_eq_mul, one_mul, zero_add] at hz
  have hc := sub_eq_zero.mp hz
  rwa [Coupling.smoothDist_apply_eq hu.continuousOn φ,
    Coupling.smoothDist_apply_eq hv.continuousOn φ] at hc

/-- The centered fields themselves are equal, with no exceptional outcomes. -/
theorem centredField_eq_of_isZeroBoundaryGFF
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {h : Ω → DistOn upperHalfPlaneOpens} {u v : ℂ → ℝ}
    (hu : InnerProductSpace.HarmonicOnNhd u H)
    (hv : InnerProductSpace.HarmonicOnNhd v H)
    (hzu : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h u) P)
    (hzv : LQGMetric.IsZeroBoundaryGFF upperHalfPlaneOpens (centredField h v) P) :
    centredField h u = centredField h v := by
  have he := WangWu.smoothDist_congr hu.continuousOn hv.continuousOn
    (eqOn_of_isZeroBoundaryGFF_centredField hu hv hzu hzv)
  exact funext fun ω => congrArg (fun d => h ω - d) he

end InteractingSLE.Theorem14.GW2Sf
