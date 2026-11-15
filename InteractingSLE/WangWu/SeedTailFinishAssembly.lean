/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.SeedTailFinishBarrier
import InteractingSLE.WangWu.SeedTailFinishChart
import InteractingSLE.WangWu.Shift.Main
import InteractingSLE.WangWu.ChamberClauseJoint

/-!
# Proposition 4.19 and the joint chamber statement after the stochastic closure

PROVE-WW-B27 continuation. The shifted image law (B26) and the rational-restart
right barrier are proved. The exports here therefore have only the deterministic
chart input, or its two explicit endpoint components, as hypotheses.
-/

set_option autoImplicit false
noncomputable section

universe u

namespace InteractingSLE.WangWu.SeedTail

/-- Small height gaps, with the shifted law and the killed barrier discharged. -/
theorem seedTailSmallStatement_of_tailChart (hChart : TailChartStatement.{u}) :
    SeedField.SeedTailSmallStatement.{u} :=
  seedTailSmallStatement_of_shift imageWordFiltShiftStatement killedRightBarrierStatement hChart

/-- Proposition 4.19 with only the deterministic chart translation remaining. -/
theorem prop419Statement_of_tailChart (hChart : TailChartStatement.{u}) :
    SeedField.Prop419Statement.{u} :=
  SeedField.prop419Statement_of_seedTailSmall (seedTailSmallStatement_of_tailChart hChart)

/-- The joint four-chamber statement with only the chart translation remaining. -/
theorem chamber4JointStatement_of_tailChart (hChart : TailChartStatement.{u}) :
    Chamber4.Chamber4JointStatement.{u} :=
  ChamberCond.chamber4JointStatement_of_prop419' (prop419Statement_of_tailChart hChart)

/-- The small-gap tail statement from the two precise geometric endpoint inputs. -/
theorem seedTailSmallStatement_of_landing (hSide : SlitRightLandingStatement)
    (hGap : PositiveLandingGapStatement) : SeedField.SeedTailSmallStatement.{u} :=
  seedTailSmallStatement_of_tailChart (tailChartStatement_of_landing hSide hGap)

/-- Proposition 4.19 from the two precise geometric endpoint inputs. -/
theorem prop419Statement_of_landing (hSide : SlitRightLandingStatement)
    (hGap : PositiveLandingGapStatement) : SeedField.Prop419Statement.{u} :=
  prop419Statement_of_tailChart (tailChartStatement_of_landing hSide hGap)

/-- The joint four-chamber statement from the same endpoint inputs (B28). -/
theorem chamber4JointStatement_of_landing (hSide : SlitRightLandingStatement)
    (hGap : PositiveLandingGapStatement) : Chamber4.Chamber4JointStatement.{u} :=
  ChamberCond.chamber4JointStatement_of_prop419' (prop419Statement_of_landing hSide hGap)

end InteractingSLE.WangWu.SeedTail
