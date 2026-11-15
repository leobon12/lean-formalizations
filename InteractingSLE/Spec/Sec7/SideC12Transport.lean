/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC12Shift

/-!
# The physical local mean through global inversion

PROVE-SIDE-COLLAR2. Reuse Wang--Wu's inversion of local-set means and
add the deterministic harmonic correction. Both germ measurability and
the residual conditional Gaussian law are proved, as is the pointwise
identity for the chosen harmonic representatives.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open LQGMetric (DistOn TestOn)

namespace InteractingSLE.Sec7.SideC12

open LocalSets Aux119Heights
open WangWu (negInv reflectField)
open SupercriticalConformalCovariance.GM24 (smoothDist)

/-- Inversion transports the chosen representative on the entire open
domain. No choice of a representative is silently transported. -/
theorem harmRep_reflect {T : DistOn upperHalfPlaneOpens} {U : Set ℂ}
    (hUo : IsOpen U) (hUH : U ⊆ H) (hT : IsHarmonicDistOn T U) :
    EqOn (harmRep (reflectField T) (negInv '' U))
      (fun z => -harmRep T U (negInv z)) (negInv '' U) := by
  obtain ⟨hv, hrep⟩ := harmRep_spec hT
  have hTR := WangWu.isHarmonicDistOn_reflectField hUo hUH hT
  obtain ⟨hvR, hrepR⟩ := harmRep_spec hTR
  refine Sec6.eqOn_of_integral_mul_eq (WangWu.isOpen_image_negInv hUo hUH)
    (WangWu.image_negInv_subset_H hUH) hvR
    (WangWu.harmonicOnNhd_comp_negInv hUo hUH hv).neg ?_
  intro φ hφ
  have hsupp : tsupport (Chart.pushTest StripSysField.isConformal_infinityReturnChart φ) ⊆ U := by
    refine (WangWu.tsupport_pushTest_return_subset φ).trans ?_
    calc negInv '' tsupport φ ⊆ negInv '' (negInv '' U) := image_mono hφ
      _ = U := WangWu.image_negInv_image_negInv U
  rw [← hrepR φ hφ, WangWu.reflectField_apply, hrep _ hsupp,
    Chart.integral_mul_pushTest, ← integral_neg]
  simp only [neg_mul]
  rfl

/-- A physical local-set mean transports through inversion plus a smooth
harmonic correction, with the full local-mean predicate. -/
theorem localSetMean_reflect_add {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {A : Ω → Set ℂ} (hA : ∀ ω, A ω ⊆ H ∧ IsOpen (H \ A ω))
    {h g : Ω → DistOn upperHalfPlaneOpens} (hg : IsLocalSetMean A h P g)
    {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u H) :
    IsLocalSetMean (fun ω => negInv '' A ω)
      (fun ω => reflectField (h ω) + smoothDist upperHalfPlaneOpens u) P
      (fun ω => reflectField (g ω) + smoothDist upperHalfPlaneOpens u) := by
  exact localSetMean_add_dist (fun ω => (WangWu.image_negInv_relClosed (hA ω)).2)
    (WangWu.IsLocalSetMean.reflect hA hg) (WholeField.isHarmonicDistOn_smoothDist hu)

/-- The physical representatives satisfy the inversion formula on one
event, simultaneously at every point of the random complement. -/
theorem ae_harmRep_reflect_add {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {A : Ω → Set ℂ} (hA : ∀ ω, A ω ⊆ H ∧ IsOpen (H \ A ω))
    {h g : Ω → DistOn upperHalfPlaneOpens} (hg : IsLocalSetMean A h P g)
    {u : ℂ → ℝ} (hu : InnerProductSpace.HarmonicOnNhd u H) :
    ∀ᵐ ω ∂P, ∀ z ∈ H \ negInv '' A ω,
      harmRep (reflectField (g ω) + smoothDist upperHalfPlaneOpens u)
          (H \ negInv '' A ω) z =
        -harmRep (g ω) (H \ A ω) (negInv z) + u z := by
  filter_upwards [hg.2.1] with ω hω z hz
  have hR := WangWu.isHarmonicDistOn_reflectField (hA ω).2 sdiff_subset hω
  rw [WangWu.H_diff_image_negInv] at hz ⊢
  rw [harmRep_add_smoothDist (WangWu.isOpen_image_negInv (hA ω).2 sdiff_subset)
      (WangWu.image_negInv_subset_H sdiff_subset) hR hu hz]
  change harmRep (reflectField (g ω)) (negInv '' (H \ A ω)) z + u z = _
  rw [harmRep_reflect (hA ω).2 sdiff_subset hω hz]

end InteractingSLE.Sec7.SideC12
