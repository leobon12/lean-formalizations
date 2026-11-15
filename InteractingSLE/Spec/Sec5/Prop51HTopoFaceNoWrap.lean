/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop51HTopoFaceAccess

/-!
# Conditional assembly of forward no-wrap from outer-face geometry

The new orientation and component arguments discharge contacted separation
from a geometric access certificate. Constructing the certificate from the
western excursion ends remains an explicit named hypothesis. This file proves
the exact original `FwdNoWrapQStatement` under that hypothesis; it asserts no
unconditional no-wrap theorem and changes no source declaration.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter Topology Bornology
open QuantumZipper (H)

namespace InteractingSLE.Sec5.Prop51HTopo

open WangWu hiding ratPt exists_ratPt_dist_lt
open Prop51G

/-- **Remaining global geometric construction, not an asserted theorem.**
For contacted paths with western excursion ends, the outer face either reaches
the original positive real boundary or admits a clockwise collar at a visible
flow segment. The collar contains no assumed physical left/right label.
The non-tip-contact assumption is automatic in a putative strict-left case.
This proposition is used only as an explicit hypothesis of the two conditional
assembly lemmas below. -/
def ContactedOuterFaceAccessStatement : Prop :=
  ∀ (η : ℝ → ℂ) (w : ℝ → ℝ) (β : ℝ → ℂ) (s : ℝ),
    IsProperArc η → Continuous w → w 0 = 0 → IsLoewnerTrace w β → 0 < s →
    (∀ v : ℝ, 0 < v → β v ≠ 0) →
    (∃ t : ℝ, 0 < t ∧ η t ∈ cfHullQ w s) →
    negInv (β s) ∉ arcRange η →
    HasWesternExcursionEnds η w s → IsBounded (chartFlowSet η w s) →
      (∃ x : ℝ, 0 < x ∧ (x : ℂ) ∈ closure (physicalOuterFace η w s)) ∨
        Nonempty (OuterFaceCollar η w s)

/-- Contacted separation now follows from an explicit geometric construction:
the conformal orientation, right-side witness and face propagation are proved
in the preceding modules. -/
theorem contactedWesternExcursionStatement_of_outerFaceAccess
    (haccess : ContactedOuterFaceAccessStatement) : ContactedWesternExcursionStatement := by
  intro η w β s hη hw hw0 hβ hs hnr hcontact hends hb hL
  have ha := haccess η w β s hη hw hw0 hβ hs hnr hcontact hL.1.2 hends hb
  exact tip_notMem_leftSideOf_of_outerFace_access hη hβ hw hw0 hs.le (hnr s hs) hb ha hL

/-- Assembly of the unchanged original forward no-wrap statement, conditional
only on the remaining collar-or-positive-boundary construction. -/
theorem fwdNoWrapQStatement_of_outerFaceAccess
    (haccess : ContactedOuterFaceAccessStatement) : FwdNoWrapQStatement :=
  fwdNoWrapQStatement_of_contactedWestern
    (contactedWesternExcursionStatement_of_outerFaceAccess haccess)

end InteractingSLE.Sec5.Prop51HTopo
