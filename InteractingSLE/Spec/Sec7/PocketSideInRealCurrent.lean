/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.PocketSideInRealCollars
import InteractingSLE.Spec.Sec7.PocketSideInSyncCharts

/-!
# Actual original-visit contacts come from the initial inner pocket frontier

PROVE-POCKET-SIDEIN. At a common original visit, the shared hull cut is open.
Inside that cut the current inner frontier is the initial inner frontier.
This identifies the constructed contacts in terms of the actual SideTest
pockets, rather than an unspecified closed contact set.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Set Filter Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Wire.Current.SideTest

open Sec7 Sec7.PocketStopSide Sec7.PocketStop

variable {Ω : Type} [MeasurableSpace Ω]

/-- The actual common-visit contacts are precisely the closure of the
initial inner pocket frontier still visible in the current outer domain. -/
theorem currentPocketContacts_at_original_visit {outer inner : SideTest Ω} {i : BothLow}
    {d : WordObjects Ω} (hO : outer.Ready d) (hI : inner.Ready d)
    (hRc : ∀ ω, Continuous (d.rightWall ω))
    (hLcO : ∀ ω, Continuous (d.leftWall outer.seed ω))
    (hLcI : ∀ ω, Continuous (d.leftWall inner.seed ω)) {ω : Ω}
    (hωO : ω ∈ (outer.target i d).event) (hωI : ω ∈ (inner.target i d).event)
    (hUC : (inner.target i d).domain ω ⊆ (outer.target i d).domain ω)
    {t : ℝ} (ht : 0 ≤ t) (hvisit : d.curve ω t ∈ (inner.target i d).domain ω) :
    currentPocketContacts
      (relChart (outer.target i d).baseChart (outer.target i d).curve
        (outer.visitCapacity d ω t).toNNReal ω)
      (relChart (inner.target i d).baseChart (inner.target i d).curve
        (inner.visitCapacity d ω t).toNNReal ω) =
      closure ((relChart (outer.target i d).baseChart (outer.target i d).curve
        (outer.visitCapacity d ω t).toNNReal ω).1 ''
          (frontier ((inner.target i d).domain ω) ∩
            ((relChart (outer.target i d).baseChart (outer.target i d).curve
              (outer.visitCapacity d ω t).toNNReal ω).dom : Set ℂ))) := by
  have houter := relChart_dom_visitCapacity hO hRc hLcO hωO ht (hUC hvisit)
  have hinner := relChart_dom_visitCapacity hI hRc hLcI hωI ht hvisit
  have hcut : IsOpen (H \ QuantumZipper.fwdHull (fun s : ℝ => d.driver s.toNNReal ω) t) := by
    have ho := isOpen_hull_compl hO (i := i) (outer.visitCapacity d ω t).toNNReal ω hωO
    rw [(visitCapacity_spec hO hωO ht (hUC hvisit)).2.2] at ho
    exact ho
  apply currentPocketContacts_eq_initial_frontier hcut _ hinner
  rw [houter]
  exact inter_subset_right

end InteractingSLE.Wire.Current.SideTest
