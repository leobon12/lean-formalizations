/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInSyncActual
import InteractingSLE.Spec.Sec7.PocketSideInLogTransition
import InteractingSLE.Spec.Jordan.Coupling

/-!
# Analytic lifts and nesting for the actual common-visit charts

PROVE-POCKET-SIDEIN. The canonical base chart already carries pLog.
Composition with its actual own Loewner chart retains an analytic lift.
The same original hull identifies the two current domains and proves their
inclusion from physical pocket inclusion.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 Sec7.PocketStopField Sec7.PocketStopSide Sec7.PocketCoupling
  Sec7.PocketStop Sec7.PocketTraversal Sec7.Lemma71C

variable {Ω : Type} [MeasurableSpace Ω]

/-- Ready's canonical base chart is a domain chart with its actual analytic
logarithm pLog; conformality alone would not control the inherited lift. -/
theorem isDomainChart_baseChart {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω}
    (hj : j.Ready d) (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ ω, Continuous (d.leftWall j.seed ω)) {ω : Ω}
    (hω : ω ∈ (j.target i d).event) :
    IsDomainChart ((j.target i d).domain ω) ((j.target i d).baseChart ω) := by
  have hc := (isPocketChartOn hj hRc hLc (i := i)).1 ω hω
  have hψ : ∀ ω ∈ (j.target i d).event,
      SupercriticalConformalCovariance.IsConformalBijection ((j.target i d).chart ω)
        ((j.target i d).domain ω) H := by
    intro w hw
    rcases jordan_cases hj w hw with ⟨pole, -, -, hJ⟩ | hJ
    · exact hJ.2.2.2.1
    · exact hJ.2.2.2.1
  refine ⟨hc.1, hc.1.coe_dom.symm.trans hc.2.1, pLog (j.target i d).event
    (j.target i d).domain (j.target i d).chart ω, ?_, fun z _ => rfl⟩
  exact isDerivLog_pLog (isOpen_domain hj (i := i)) hψ hω

/-- At a live original visit the actual current chart inherits an analytic
logarithm by composition with its own hydrodynamic Loewner lift. -/
theorem isDomainChart_relChart_visitCapacity {j : SideTest Ω} {i : BothLow} {d : WordObjects Ω}
    (hj : j.Ready d) (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLc : ∀ ω, Continuous (d.leftWall j.seed ω)) {ω : Ω}
    (hω : ω ∈ (j.target i d).event) {t : ℝ} (ht : 0 ≤ t)
    (hvisit : d.curve ω t ∈ (j.target i d).domain ω) :
    IsDomainChart ((j.target i d).domain ω ∩
        (H \ QuantumZipper.fwdHull (fun s : ℝ => d.driver s.toNNReal ω) t))
      (relChart (j.target i d).baseChart (j.target i d).curve
        (j.visitCapacity d ω t).toNNReal ω) := by
  have hbase := isDomainChart_baseChart hj hRc hLc hω
  obtain ⟨-, hlive, -⟩ := visitCapacity_spec hj hω ht hvisit
  obtain ⟨W, hW, hW0, q', hqq', hWeq, heq⟩ :=
    exists_relChart_eq_loewner (c := (j.target i d).baseChart)
      (isDrivenCurve_target hj ω hω) hlive
  have hcurrent := hbase.trans (isDomainChart_loewner hW hW0
    (j.visitCapacity d ω t).toNNReal.coe_nonneg)
  rw [← Chart.loewner_eq_trans, ← heq] at hcurrent
  have hdom := hcurrent.coe_dom.symm.trans (relChart_dom_visitCapacity hj hRc hLc hω ht hvisit)
  exact hdom ▸ hcurrent

/-- One inner visit synchronizes both actual current charts. Physical
pocket inclusion then gives inclusion of their current domains. -/
theorem current_domain_inclusion_at_visit {outer inner : SideTest Ω} {i : BothLow}
    {d : WordObjects Ω} (hO : outer.Ready d) (hI : inner.Ready d)
    (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLcO : ∀ ω, Continuous (d.leftWall outer.seed ω))
    (hLcI : ∀ ω, Continuous (d.leftWall inner.seed ω)) {ω : Ω}
    (hωO : ω ∈ (outer.target i d).event) (hωI : ω ∈ (inner.target i d).event)
    (hUC : (inner.target i d).domain ω ⊆ (outer.target i d).domain ω)
    {t : ℝ} (ht : 0 ≤ t) (hvisit : d.curve ω t ∈ (inner.target i d).domain ω) :
    ((relChart (inner.target i d).baseChart (inner.target i d).curve
      (inner.visitCapacity d ω t).toNNReal ω).dom : Set ℂ) ⊆
        (relChart (outer.target i d).baseChart (outer.target i d).curve
          (outer.visitCapacity d ω t).toNNReal ω).dom :=
  current_domain_inclusion_of_common_hull hUC
    (relChart_dom_visitCapacity hO hRc hLcO hωO ht (hUC hvisit))
    (relChart_dom_visitCapacity hI hRc hLcI hωI ht hvisit)

end InteractingSLE.Wire.Current.SideTest
