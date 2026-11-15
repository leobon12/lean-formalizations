/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentCMIConvWExit
import InteractingSLE.Spec.Restart.FlowStopIdentCMIConvWLocality

/-!
# Converse and source-form G3 after the proved clock and tilt reductions

These are conditional helpers. The three named inputs are the source exit
announcement, the reference exit announcement, and original-field terminal
hull locality. The measurable exit version, continuous adapted driver,
threshold bound, source-sequence estimates, chart shift and tilted locality
adapter have been proved in the preceding W modules.
-/
set_option autoImplicit false
noncomputable section
universe u
namespace InteractingSLE.Restart.FlowStopIdentCMI

/-- The corrected converse with only the three precise remaining inputs. -/
theorem cmiConverseVStatement_of_CMIWInputs
    (hsource : CMIWSourceAnnounceStatement.{u})
    (hreference : CMIWReferenceAnnounceStatement.{u})
    (hterminal : CMIWTerminalHullLocalityStatement.{u}) : CMIConverseVStatement.{u} :=
  cmiConverseVStatement_of_inputs
    (cmiVPositiveClockStatement_of_announcements hsource hreference)
    (cmiVTiltLocalityStatement_of_terminal hterminal)

/-- The source stopped-flow identification inherits the same three inputs. -/
theorem flowLineStopIdentCMIVStatement_of_CMIWInputs
    (hsource : CMIWSourceAnnounceStatement.{u})
    (hreference : CMIWReferenceAnnounceStatement.{u})
    (hterminal : CMIWTerminalHullLocalityStatement.{u}) : FlowLineStopIdentCMIVStatement.{u} :=
  flowLineStopIdentCMIVStatement_of_converse
    (cmiConverseVStatement_of_CMIWInputs hsource hreference hterminal)

end InteractingSLE.Restart.FlowStopIdentCMI

namespace InteractingSLE.RLC
open Restart.FlowStopIdentCMI

/-- Source-form G3: the CMI-specific remainder is exactly the three named inputs.
The WFS kernel and Theorems 1.2/1.3 retain their existing role in this G3 adapter. -/
theorem g3SourceStatement_of_CMIWInputs
    (hsource : CMIWSourceAnnounceStatement.{0})
    (hreference : CMIWReferenceAnnounceStatement.{0})
    (hterminal : CMIWTerminalHullLocalityStatement.{0})
    (hT : ∀ κ : ℝ, 0 < κ → κ < 4 → WFS.ThroughKernelStatement.{0, 0} κ)
    (h12p : Exist.Staged.Theorem12ParamStatement.{0}) (h13 : Exist.Theorem13Statement.{0}) :
    G3SourceStatement.{0} :=
  g3SourceStatement_of_CMIConverseV
    (cmiConverseVStatement_of_CMIWInputs hsource hreference hterminal) hT h12p h13

end InteractingSLE.RLC
