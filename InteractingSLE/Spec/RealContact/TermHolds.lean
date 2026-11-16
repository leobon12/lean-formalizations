/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.RealContact.TermMain
import InteractingSLE.Spec.AuditFix.BoundaryContactInputs

/-!
# The terminal retained pair, closed

Packet PROVE-RC-TERM, second run (ruling R124). The path statement `TerminalRetainedPathStatement` from
`Term.terminalRetainedPath_of_inputs` with the closed Theorem 1.3 (`AuditFix.ContactInputs.theorem13`) and the closed
Lemma 7.5 (`AuditFix.ContactInputs.lemma75`), both used inline (R48/R123: no new named constant of type
`Theorem12Statement`, `Theorem13Statement` or `Theorem12ParamStatement`), and its three consequences
`TerminalRetainedCondDetStatement` (PROVE-RC-TERM's named input), `PocketCornerStatement` (PROVE-RC-POCKET's named
input) and `G7GB7aFirstHitRealStatement` (R124's core, PROVE-RC-HIT).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace InteractingSLE.RealContact

/-- **The path identity of the first path in the chart of the completed second path**, closed. -/
theorem terminalRetainedPath_holds : TerminalRetainedPathStatement.{u} :=
  Term.terminalRetainedPath_of_inputs AuditFix.ContactInputs.theorem13 AuditFix.ContactInputs.lemma75

/-- **The terminal retained pair's conditional determination**, closed. -/
theorem terminalRetainedCondDet_holds : TerminalRetainedCondDetStatement.{u} :=
  terminalRetainedCondDet_of_path terminalRetainedPath_holds

/-- **The pocket corner**, closed. -/
theorem pocketCorner_holds : PocketCornerStatement.{u} := pocketCorner_of_path terminalRetainedPath_holds

/-- **R124's core: the G7 + GB7a first-hit exclusion at real hits**, closed. -/
theorem g7GB7aFirstHitReal_holds : G7GB7aFirstHitRealStatement.{u} :=
  g7GB7aFirstHitReal_of_path terminalRetainedPath_holds

end InteractingSLE.RealContact
