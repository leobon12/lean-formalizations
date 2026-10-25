import SupercriticalLQGUniqueness.B2.PfeWeyl.GeoAnnuli

 











set_option autoImplicit false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped ENNReal

namespace SupercriticalLQGUniqueness.B2.PfeWeyl

 


def AcrossTailInput {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Dω : Ω → LSCMetric) (r : ℝ) (hr : 0 < r) : Prop :=
  ∀ T : ℝ≥0∞, T ≠ ⊤ → ∀ η : ℝ≥0∞, 0 < η →
    ∀ᶠ R in atTop, P {ω | acrossDist (Dω ω) (outerAnnulus r hr R) ≤ T} ≤ η

 
theorem acrossTailInput_of_geoAnnulusInput {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {Dω : Ω → LSCMetric} {r : ℝ} {hr : 0 < r}
    (h : GeoAnnulusInput P Dω r hr) : AcrossTailInput P Dω r hr :=
  h.2

end SupercriticalLQGUniqueness.B2.PfeWeyl
