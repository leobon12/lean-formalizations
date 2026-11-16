/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.RealContact.TermHolds
import InteractingSLE.Spec.RealContact.OrdMain
import InteractingSLE.Spec.RealContact.Cross

/-!
# Theorem 1.5's critical-angle clauses at every contact, closed (ruling R124)

Orchestrator-owned composition. Clause (i) is `criticalOrderedContact_of_firstHitReal` (packet PROVE-RC-ORD) applied
to the closed core `g7GB7aFirstHitReal_holds` (packets PROVE-RC-HIT, PROVE-RC-POCKET, PROVE-RC-TERM and
PROVE-RC-TERM2). Clause (iii) is `criticalCrossingContact_of_ordered` (packet PROVE-RC-CROSS) applied to clause (i) at
universe `0`. These are the proofs of the frozen anchors `IsFlowLine.start_or_terminal_of_contact_of_critical` and
`IsFlowLine.first_or_terminal_of_contact_of_critical`.
-/

set_option autoImplicit false

universe u

namespace InteractingSLE.RealContact

/-- **Theorem 1.5 (i), critical angles, at every contact**, closed. -/
theorem criticalOrderedContact_holds : CriticalOrderedContactStatement.{u} :=
  criticalOrderedContact_of_firstHitReal g7GB7aFirstHitReal_holds

/-- **Theorem 1.5 (iii), critical angles, at every contact**, closed. -/
theorem criticalCrossingContact_holds : CriticalCrossingContactStatement.{u} :=
  criticalCrossingContact_of_ordered criticalOrderedContact_holds.{0}

end InteractingSLE.RealContact
