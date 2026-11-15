/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.SideC19Collar

/-! # Current-chart validity in the tops' relifted collar

PROVE-SIDE-COLLAR2. The walls-measurable shift supplied by C18 preserves
the pocket-chart and analytic derivative-logarithm properties.
-/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal Real

namespace InteractingSLE.Sec7.SideC19
open Wire Wire.Current PocketStopField PocketStopSide

variable {Ω : Type} [MeasurableSpace Ω] {i : BothLow} {d : WordObjects Ω} {j : SideTest Ω}

/-- The current R100 chart is still a measurable pocket chart on the
same unrefined ready test. -/
theorem isPocketChartOn_currentShift (hj : j.Ready d)
    (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ ω, Continuous (d.leftWall j.seed ω))
    {m : Ω → ℤ} (hm : Measurable[(j.target i d).walls] m) :
    PocketCoupling.IsPocketChartOn (j.target i d).walls (j.target i d).event
      (j.target i d).domain (j.target i d).chart
      (fun ω => shiftChart ((j.target i d).baseChart ω) (m ω)) :=
  isPocketChartOn_shift (j.isPocketChartOn hj hRc hLc) (j.measurableSet_domain hj hRc hLc) hm

/-- The shifted current lift retains an analytic logarithm of the
derivative on the whole physical pocket. -/
theorem isDomainChart_currentShift (hj : j.Ready d)
    (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ ω, Continuous (d.leftWall j.seed ω))
    (m : Ω → ℤ) {ω : Ω} (hω : ω ∈ (j.target i d).event) :
    IsDomainChart ((j.target i d).domain ω)
      (shiftChart ((j.target i d).baseChart ω) (m ω)) :=
  SideC16.isDomainChart_shiftChart (j.isDomainChart_baseChart hj hRc hLc hω) (m ω)

end InteractingSLE.Sec7.SideC19
