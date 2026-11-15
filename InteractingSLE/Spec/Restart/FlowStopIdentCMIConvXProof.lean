/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentCMIConvXLimit

/-! # The positive clock is proved; the converse has one Gaussian limit remainder -/
set_option autoImplicit false
noncomputable section
universe u
namespace InteractingSLE.Restart.FlowStopIdentCMI

/-- The positive clock, with both announcements and no residual input. -/
theorem cmiVPositiveClockStatement : CMIVPositiveClockStatement.{u} :=
  cmiVPositiveClockStatement_of_announcements cmiWSourceAnnounceStatement cmiWReferenceAnnounceStatement

/-- Tilted terminal locality from the precise remaining Gaussian hull-limit theorem. -/
theorem cmiVTiltLocalityStatement_of_hullLimit (hlimit : CMIXHullLocalityLimitStatement.{u}) :
    CMIVTiltLocalityStatement.{u} :=
  cmiVTiltLocalityStatement_of_terminal (cmiWTerminalHullLocalityStatement_of_hullLimit hlimit)

/-- The corrected converse with only the Gaussian terminal-limit remainder. -/
theorem cmiConverseVStatement_of_hullLimit (hlimit : CMIXHullLocalityLimitStatement.{u}) :
    CMIConverseVStatement.{u} :=
  cmiConverseVStatement_of_inputs cmiVPositiveClockStatement
    (cmiVTiltLocalityStatement_of_hullLimit hlimit)

/-- The stopped identification inherits exactly the same remaining input. -/
theorem flowLineStopIdentCMIVStatement_of_hullLimit (hlimit : CMIXHullLocalityLimitStatement.{u}) :
    FlowLineStopIdentCMIVStatement.{u} :=
  flowLineStopIdentCMIVStatement_of_converse (cmiConverseVStatement_of_hullLimit hlimit)

end InteractingSLE.Restart.FlowStopIdentCMI

namespace InteractingSLE.RLC
open Restart.FlowStopIdentCMI

/-- Source-form G3 with no clock or announcement input; the Gaussian hull-limit
step remains explicit, together with this adapter's existing WFS/1.2/1.3 inputs. -/
theorem g3SourceStatement_of_CMIHullLimit (hlimit : CMIXHullLocalityLimitStatement.{0})
    (hT : ∀ κ : ℝ, 0 < κ → κ < 4 → WFS.ThroughKernelStatement.{0, 0} κ)
    (h12p : Exist.Staged.Theorem12ParamStatement.{0}) (h13 : Exist.Theorem13Statement.{0}) :
    G3SourceStatement.{0} :=
  g3SourceStatement_of_CMIConverseV (cmiConverseVStatement_of_hullLimit hlimit) hT h12p h13

end InteractingSLE.RLC
