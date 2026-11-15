/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInKernelStepPull
import InteractingSLE.WangWu.ReverseContactLocal
import InteractingSLE.GFF.LocalSets.GermMedian

/-!
# Forgetting retained marks in the global residual law

PROVE-POCKET-SIDEIN. A conditional zero-boundary field on the fixed half-plane
has the unconditional GFF law. This is a tower-property step before any
collar or visit is selected.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H zeroGFFTestCov)
open LQGMetric (DistOn TestOn IsZeroBoundaryGFF)

namespace InteractingSLE.Sec7.PocketStopSide

/-- Forgetting a record from a conditional GFF on the fixed half-plane
gives the full unconditional GFF law. -/
theorem isZeroBoundaryGFF_of_conditional_halfPlane
    {Ω : Type*} {ℋ : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] (hℋ : ℋ ≤ mΩ)
    {X : Ω → DistOn upperHalfPlaneOpens} (hX : Measurable X)
    (hLaw : IsCondZeroBoundaryGFF P ℋ (fun _ => H) X) :
    IsZeroBoundaryGFF upperHalfPlaneOpens X P := by
  have hZ := Coupling.isZeroBoundaryGFF_zbLaw (D := upperHalfPlaneOpens) subset_rfl
  have hMap : P.map X = Coupling.zbLaw upperHalfPlaneOpens := by
    refine Coupling.ext_of_integral_cexp fun φ => ?_
    rw [integral_map hX.aemeasurable
      (GFF.measurable_exp_I_mul (LQGMetric.measurable_distOn_apply φ)).aestronglyMeasurable]
    calc
      (∫ ω, Complex.exp (Complex.I * (X ω φ : ℂ)) ∂P) =
          ∫ ω, P[fun ω => Complex.exp (Complex.I * (X ω φ : ℂ)) | ℋ] ω ∂P :=
        (integral_condExp hℋ).symm
      _ = ((Real.exp (-(1 / 2) * zeroGFFTestCov H φ φ) : ℝ) : ℂ) := by
        rw [integral_congr_ae (hLaw φ), integral_const, probReal_univ, one_smul]
      _ = ∫ g, Complex.exp (Complex.I * (g φ : ℂ)) ∂Coupling.zbLaw upperHalfPlaneOpens :=
        (LocalSets.integral_exp_field hZ φ).symm
  exact WangWu.isZeroBoundaryGFF_comp_of_map_eq (g := id) (f := X) hX hMap hZ

end InteractingSLE.Sec7.PocketStopSide
