/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCG7aAssembly
import InteractingSLE.Spec.Restart.FlowStopIdentCMIConvYLimit

/-!
# G7a with the Gaussian filled-hull limit discharged

Packet PROVE-G7A-MEANIDENT. The landed Y-limit theorem supplies the exact
`CMIXHullLocalityLimitStatement`. Only the deterministic pocket mean identity
remains in the general locality step. The other hypotheses below are the
pre-existing WFS and Theorems 1.2/1.3 prerequisites of G7a.
-/

set_option autoImplicit false
noncomputable section
universe u

namespace InteractingSLE.Restart.FlowLocalityGen

/-- General flow locality from the pocket mean identity; the hull limit is proved. -/
theorem flowLineStopIdentGStatement_of_pocketMeanIdent (hM : PocketMeanIdentStatement) :
    FlowLineStopIdentGStatement.{u} :=
  flowLineStopIdentGStatement_of_kernel (shiftKernelGenStatement_of_meanIdent hM)
    FlowStopIdentCMI.cmiXHullLocalityLimitStatement

end InteractingSLE.Restart.FlowLocalityGen

namespace InteractingSLE.RLC

/-- G7a with its Gaussian hull-limit obligation discharged by the landed Y theorem. -/
theorem g7aChartStatement_of_pocketMeanIdent
    (hM : Restart.FlowLocalityGen.PocketMeanIdentStatement)
    (hT : ∀ κ : ℝ, 0 < κ → κ < 4 → WFS.ThroughKernelStatement.{0, 0} κ)
    (h12p : Exist.Staged.Theorem12ParamStatement.{0})
    (h13 : Exist.Theorem13Statement.{0}) : G7aChartStatement.{0} :=
  g7aChartStatement_of_G
    (Restart.FlowLocalityGen.flowLineStopIdentGStatement_of_pocketMeanIdent hM) hT h12p h13

end InteractingSLE.RLC
