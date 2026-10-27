import MatedCRTHarmonic.ConeLemmaA10.FieldLawAssembly
import MatedCRTHarmonic.ConeLemmaA10.CircleAvgFieldSupport

/-!
# Circle-average support for the rooted field-law interface

This file transfers the canonical normalized-rooting support theorem to the rooted field law
carried by `WholePlaneRootingFieldLawInputs`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Set Metric

namespace MatedCRTHarmonic.ConeLemmaA10

open MatedCRTHarmonic.GMS4.GMSA

/-- The rooted field law supplied by the A.10 input interface is concentrated on fields with
convergent mollified unit-circle averages and zero unit-circle average. -/
theorem WholePlaneRootingFieldLawInputs.rootedFieldLaw_ae_circleAvgFieldSupport
    {Ω : Type*} [MeasurableSpace Ω] (D : WholePlaneRootingFieldLawInputs Ω) :
    ∀ᵐ g ∂(D.rootedLaw.map D.field), CircleAvgFieldSupport g := by
  rw [D.rootedFieldLaw_eq_rootingMap]
  apply ae_circleAvgFieldSupport_map_normalizedRootingMap D.normalizedWPGFF D.gamma
  rw [normalizedLebesgueOnRootingDisk]
  exact Measure.ae_smul_measure (ae_restrict_mem measurableSet_ball) _

end MatedCRTHarmonic.ConeLemmaA10

