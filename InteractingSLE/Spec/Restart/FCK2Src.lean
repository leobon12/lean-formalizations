/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FCK2SrcGood
import InteractingSLE.Spec.Restart.FCK2SrcRead
import InteractingSLE.Spec.Restart.FCK2SrcAccess

/-!
# Source first-contact determination: exact remaining inputs

The source clock endpoints and the box word's terminal incident heights are
proved in the imported files. Goodness of the canonical driver code follows
from the conditional word-GFF law. None of those statements identifies the
actual continuation with that code by itself.

The source forward marked kernels and original-coordinate terminal access
remain named mathematical inputs. No stopped extension is needed by the
proved comparisons; assuming one alone would not construct those kernels.
-/
set_option autoImplicit false
noncomputable section

namespace InteractingSLE.Restart.FCPlumb
universe u

/-- Current determination theorem after discharging the source endpoint and
incident-height comparisons. Its two additional named inputs remain open;
this is a conditional helper, not a provider for an unconditional anchor. -/
theorem firstContactCanonCondDetStatement_of_source_forwardKernels_physicalTerminalAccess
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (h76 : Sec7.Lemma76Statement.{u})
    (hForward : FirstContactK2ForwardKernelsStatement.{u})
    (hAccess : FirstContactK2PhysicalTerminalAccessStatement.{u}) :
    FirstContactCanonCondDetStatement.{u} :=
  firstContactCanonCondDetStatement_of_forwardKernels_terminalAccess_thm12_thm13_lemma76
    h12 h13 h12₀ h13₀ h76 hForward
    (firstContactK2TerminalAccessStatement_of_physicalTerminalAccess
      (lemma75Statement_of_thm12_thm13 h12 h13)
      (lemma77Statement_of_thm12_thm13_lemma76 h12 h13 h76)
      firstContact_retainedRangeEntranceStatement hAccess)

end InteractingSLE.Restart.FCPlumb
