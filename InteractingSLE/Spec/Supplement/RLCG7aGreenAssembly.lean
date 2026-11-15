/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCG7aGreenHarmonic
import InteractingSLE.Spec.Supplement.RLCG7aMeanIdent

/-!
# G7a from integration of nonnegative harmonic kernels

Packet PROVE-G7A-MEANIDENT, continuation. Bounds, boundary values, regular
Green kernels, and their integral representation are proved. The remaining
hypothesis is precisely `NonnegativeHarmonicIntegralStatement`; an
unconditional G7a theorem is not asserted.
-/

set_option autoImplicit false
noncomputable section

namespace InteractingSLE.Restart.FlowLocalityGen

/-- The original pocket mean identity from the remaining general analytic input. -/
theorem pocketMeanIdentStatement_of_nonnegativeIntegral
    (hInt : NonnegativeHarmonicIntegralStatement) : PocketMeanIdentStatement :=
  pocketMeanIdentStatement_of_greenRegularity
    (aliveGreenRegularityStatement_of_nonnegativeIntegral hInt)

end InteractingSLE.Restart.FlowLocalityGen

namespace InteractingSLE.RLC

/-- G7a with the Green-specific regularity and Gaussian hull-limit obligations
removed; the general positive harmonic-kernel integration input is explicit. -/
theorem g7aChartStatement_of_nonnegativeIntegral
    (hInt : Restart.FlowLocalityGen.NonnegativeHarmonicIntegralStatement)
    (hT : ∀ κ : ℝ, 0 < κ → κ < 4 → WFS.ThroughKernelStatement.{0, 0} κ)
    (h12p : Exist.Staged.Theorem12ParamStatement.{0})
    (h13 : Exist.Theorem13Statement.{0}) : G7aChartStatement.{0} :=
  g7aChartStatement_of_pocketMeanIdent
    (Restart.FlowLocalityGen.pocketMeanIdentStatement_of_nonnegativeIntegral hInt) hT h12p h13

end InteractingSLE.RLC
