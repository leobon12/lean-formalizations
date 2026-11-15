/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC12Physical
import InteractingSLE.WangWu.ReverseContactMean

/-!
# An original pocket mean exists whenever its counterflow mean exists

PROVE-SIDE-COLLAR2. Invert the actual physical field relation, restore
the target background before reflecting, and remove the original
background afterwards. This transports the whole local-mean law.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn)

namespace InteractingSLE.Sec7.SideC15

open LocalSets WholeField WangWu SideC12
open SupercriticalConformalCovariance.GM24 (smoothDist)

/-- The inverse affine physical transport of a centered pocket mean. -/
def inversePhysicalMean (a k c : ℝ) (u₀ u₁ : ℂ → ℝ)
    (g : DistOn upperHalfPlaneOpens) : DistOn upperHalfPlaneOpens :=
  reflectField (g + smoothDist upperHalfPlaneOpens u₁) +
    smoothDist upperHalfPlaneOpens (fun y => sourceShift a k c (negInv y) - u₀ y)

/-- The inverse deterministic correction is harmonic on the original half-plane. -/
theorem inverse_sourceShift_harmonic (a k c : ℝ) :
    InnerProductSpace.HarmonicOnNhd (fun y => sourceShift a k c (negInv y)) H :=
  LQGMetric.harmonicOnNhd_comp_holo QuantumZipper.isOpen_H QuantumZipper.isOpen_H
    (sourceShift_harmonic a k c) Chart.isConformal_infinitySourceChart.1
    Chart.isConformal_infinitySourceChart.2.1

/-- The complete original local-mean law follows from any version of
its counterflow local mean and the actual field transports. -/
theorem localSetMean_inversePhysicalMean {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {B : Ω → Set ℂ} (hB : ∀ ω, B ω ⊆ H ∧ IsOpen (H \ B ω))
    {h h' h'' g : Ω → DistOn upperHalfPlaneOpens} {a k c : ℝ}
    (hT : ∀ ω, IsChartTransport infinitySourceChart (-1) a k (h ω) (h' ω))
    (hTr : ∀ ω, IsTranslateAddConst 0 c (h' ω) (h'' ω))
    {u₀ u₁ : ℂ → ℝ} (hu₀ : InnerProductSpace.HarmonicOnNhd u₀ H)
    (hu₁ : InnerProductSpace.HarmonicOnNhd u₁ H)
    (hg : IsLocalSetMean B (centredField h'' u₁) P g) :
    IsLocalSetMean (fun ω => negInv '' B ω) (centredField h u₀) P
      (fun ω => inversePhysicalMean a k c u₀ u₁ (g ω)) := by
  have hFull := localSetMean_add_dist (fun ω => (hB ω).2) hg
    (isHarmonicDistOn_smoothDist hu₁)
  have hrestore : (fun ω => centredField h'' u₁ ω + smoothDist upperHalfPlaneOpens u₁) = h'' := by
    funext ω
    exact sub_add_cancel _ _
  rw [hrestore] at hFull
  have hU : InnerProductSpace.HarmonicOnNhd
      (fun y => sourceShift a k c (negInv y) - u₀ y) H :=
    (inverse_sourceShift_harmonic a k c).sub hu₀
  have hNeg : ContinuousOn (fun y => -sourceShift a k c (negInv y)) H :=
    (inverse_sourceShift_harmonic a k c).continuousOn.neg
  have hResult := localSetMean_reflect_add hB hFull hU
  have hField : (fun ω => reflectField (h'' ω) +
      smoothDist upperHalfPlaneOpens (fun y => sourceShift a k c (negInv y) - u₀ y)) = centredField h u₀ := by
    funext ω
    rw [centredField, field_eq_reflect_add (hT ω) (hTr ω), reflectField_add,
      reflectField_reflectField, reflectField_smoothDist (sourceShift_harmonic a k c).continuousOn]
    have hs : smoothDist upperHalfPlaneOpens (fun y => -sourceShift a k c (negInv y)) +
        smoothDist upperHalfPlaneOpens (fun y => sourceShift a k c (negInv y) - u₀ y) =
        -smoothDist upperHalfPlaneOpens u₀ := by
      ext φ
      rw [add_apply, neg_apply,
        Coupling.smoothDist_apply_eq hNeg,
        Coupling.smoothDist_apply_eq hU.continuousOn, Coupling.smoothDist_apply_eq hu₀.continuousOn]
      have hI := Coupling.MartMeans2.integrable_mul_test_of_continuousOn
        (inverse_sourceShift_harmonic a k c).continuousOn φ φ.tsupport_subset
      have hI₀ := Coupling.MartMeans2.integrable_mul_test_of_continuousOn hu₀.continuousOn φ φ.tsupport_subset
      simp_rw [neg_mul, sub_mul]
      rw [integral_neg, integral_sub hI hI₀]
      ring
    rw [add_assoc, hs, sub_eq_add_neg]
  rw [hField] at hResult
  exact hResult

end InteractingSLE.Sec7.SideC15
