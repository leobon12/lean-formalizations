import MatedCRTHarmonic.CellScaling.JointScalingOMain
import MatedCRTHarmonic.IGLaw.OPositiveRadii

/-!
#  `ConeJointScaling` for every mating-of-trees coupling of the frozen bundle (v4)

With the frozen bundle version 2 of `MatedCRT.IsMatingOfTreesCoupling` ,proves the affine invariance of the law of
the Lebesgue-parametrized whole-plane space-filling SLE from the bundle
(`IGLaw.IsMatingOfTreesCoupling.map_affineReroot_ηL`). At `z₀ = 0`, `φ = 0` this is exactly the named
input `CurveDilationLaw P ηL` of `coneJointScaling_of_coupling`, which therefore holds for every
coupling:

* `coneJointScaling_holds D hstd hγ : ConeJointScaling (MoTInput.coneRealizationOfCoupling D hstd hγ)`;
* `coneJointScaling_forAllCouplings`: the same, quantified exactly as the final assembly input
  `hP23 : MesoModel.FinalForAllCouplings fun _ _ C => CellScaling.ConeJointScaling C` (by `exact`);
* `matedCRTProposition23GridScalingInput_holds`: the joint-scaling identity event-transfer input at the
  coupling, with no hypothesis.

This file is separate from `JointScalingOMain` because IGCO's `IGLaw/OPositiveRadii.lean` is still
being landed; the conditional theorem does not depend on it.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace MatedCRTHarmonic.CellScaling

namespace JointScalingO

section Coupling

variable {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
  {X X₀ hIG₀ : Ω → MatedCRT.Field} {B B' B₀ B₀' : ℝ≥0 → Ω → ℝ} {U : Ω → ℝ}
  {ηL η η₀ : Ω → C(ℝ, ℂ)} {bm : Ω → MatedCRT.Path2}

/-- The named input `CurveDilationLaw` holds for every coupling of the frozen bundle. -/
theorem curveDilationLaw_of_coupling
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm) :
    CurveDilationLaw P ηL :=
  fun _ hs => IGLaw.IsMatingOfTreesCoupling.map_affineReroot_ηL D 0 hs 0

/-- **the joint-scaling identity as printed** (`(h_b, η^b) =d (h, η)` for every `b > 0`) for the cone
realization of every mating-of-trees coupling (the exact `ConeJointScaling`). -/
theorem coneJointScaling_holds
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo 0 2) :
    ConeJointScaling (MoTInput.coneRealizationOfCoupling D hstd hγ) :=
  coneJointScaling_of_coupling D hstd hγ (curveDilationLaw_of_coupling D)

/-- **the joint-scaling identity event-transfer input at the coupling**, with no hypothesis. -/
theorem matedCRTProposition23GridScalingInput_holds
    (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm)
    (hstd : StandardBorelSpace Ω) (hγ : γ ∈ Ioo 0 2) :
    MesoModel.MatedCRTProposition23GridScalingInput (MoTInput.unitMesoModelOfCoupling D hstd hγ) :=
  matedCRTProposition23GridScalingInput_of_coupling D hstd hγ (curveDilationLaw_of_coupling D)

end Coupling

/-- **`ConeJointScaling` at every coupling**, in the exact quantified shape of the final assembly input
`hP23 : MesoModel.FinalForAllCouplings fun _ _ C => CellScaling.ConeJointScaling C`
(`MesoModel/FinalAssembly.lean`): close it by `exact coneJointScaling_forAllCouplings`. -/
theorem coneJointScaling_forAllCouplings :
    ∀ (γ : ℝ) (hγ : γ ∈ Ioo 0 2) (Ω : Type) (_ : MeasurableSpace Ω) (hstd : StandardBorelSpace Ω)
      (P : Measure Ω) (X X₀ hIG₀ : Ω → MatedCRT.Field) (B B' B₀ B₀' : ℝ≥0 → Ω → ℝ) (U : Ω → ℝ)
      (ηL η η₀ : Ω → C(ℝ, ℂ)) (bm : Ω → MatedCRT.Path2)
      (D : MatedCRT.IsMatingOfTreesCoupling γ P X X₀ hIG₀ B B' B₀ B₀' U ηL η η₀ bm),
      ConeJointScaling (MoTInput.coneRealizationOfCoupling D hstd hγ) :=
  fun _ hγ _ _ hstd _ _ _ _ _ _ _ _ _ _ _ _ _ D => coneJointScaling_holds D hstd hγ

end JointScalingO

end MatedCRTHarmonic.CellScaling
