/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.FlowStopIdentCMIConvYLimit

/-! # Terminal locality and the measurable-exit converse -/
set_option autoImplicit false
noncomputable section
universe u
namespace InteractingSLE.Restart.FlowStopIdentCMI

/-- Terminal hull locality, with the Gaussian filled-hull limit discharged. -/
theorem cmiWTerminalHullLocalityStatement : CMIWTerminalHullLocalityStatement.{u} :=
  cmiWTerminalHullLocalityStatement_of_hullLimit cmiXHullLocalityLimitStatement

/-- Tilt-locality through the exit, with no residual mathematical input. -/
theorem cmiVTiltLocalityStatement : CMIVTiltLocalityStatement.{u} :=
  cmiVTiltLocalityStatement_of_terminal cmiWTerminalHullLocalityStatement

/-- The R66 measurable-exit converse, with no residual mathematical input. -/
theorem cmiConverseVStatement : CMIConverseVStatement.{u} :=
  cmiConverseVStatement_of_inputs cmiVPositiveClockStatement cmiVTiltLocalityStatement

/-- The stopped flow-line identification with an actual measurable exit version. -/
theorem flowLineStopIdentCMIVStatement : FlowLineStopIdentCMIVStatement.{u} :=
  flowLineStopIdentCMIVStatement_of_converse cmiConverseVStatement

end InteractingSLE.Restart.FlowStopIdentCMI

namespace InteractingSLE.RLC
open Restart.FlowStopIdentCMI

/-- Source-form G3: all CMI, announcement, clock and terminal-limit inputs are
discharged. This adapter retains its existing WFS and Theorems 1.2/1.3 inputs. -/
theorem g3SourceStatement_of_through_param12_thm13
    (hT : ∀ κ : ℝ, 0 < κ → κ < 4 → WFS.ThroughKernelStatement.{0, 0} κ)
    (h12p : Exist.Staged.Theorem12ParamStatement.{0}) (h13 : Exist.Theorem13Statement.{0}) :
    G3SourceStatement.{0} :=
  g3SourceStatement_of_CMIConverseV cmiConverseVStatement hT h12p h13

end InteractingSLE.RLC
