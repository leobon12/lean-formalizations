/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.RLCG7aHarmCompletion
import InteractingSLE.Spec.Supplement.RLCG7aGreenAssembly

/-!
# Discharging the harmonic integration input of G7a

Packet PROVE-G7A-MEANIDENT. The general nonnegative harmonic integration
statement, the exact alive Green regularity statement, and the pocket mean
identity are now unconditional. G7a keeps only its existing stochastic and
flow-line inputs; no Green regularity or mean-identity hypothesis remains.
-/

set_option autoImplicit false
noncomputable section

namespace InteractingSLE.Restart.FlowLocalityGen

/-- The exact analytic input left by the Green continuation, now proved. -/
theorem nonnegativeHarmonicIntegralStatement : NonnegativeHarmonicIntegralStatement := by
  intro U hU k hk h0 hi
  exact harmonicOnNhd_integral_nonneg hU hk h0 hi

/-- The original Green regularity statement, with every analytic clause proved. -/
theorem aliveGreenRegularityStatement : AliveGreenRegularityStatement :=
  aliveGreenRegularityStatement_of_nonnegativeIntegral nonnegativeHarmonicIntegralStatement

/-- The exact pocket mean identity, with no additional mathematical input. -/
theorem pocketMeanIdentStatement : PocketMeanIdentStatement :=
  pocketMeanIdentStatement_of_nonnegativeIntegral nonnegativeHarmonicIntegralStatement

end InteractingSLE.Restart.FlowLocalityGen

namespace InteractingSLE.RLC

/-- G7a after discharging harmonic integration and all Green regularity inputs. -/
theorem g7aChartStatement_of_harmonicIntegration
    (hT : ∀ κ : ℝ, 0 < κ → κ < 4 → WFS.ThroughKernelStatement.{0, 0} κ)
    (h12p : Exist.Staged.Theorem12ParamStatement.{0})
    (h13 : Exist.Theorem13Statement.{0}) : G7aChartStatement.{0} :=
  g7aChartStatement_of_nonnegativeIntegral
    Restart.FlowLocalityGen.nonnegativeHarmonicIntegralStatement hT h12p h13

end InteractingSLE.RLC
