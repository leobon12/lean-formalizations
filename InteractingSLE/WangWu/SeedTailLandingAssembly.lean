/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.WangWu.SeedTailLandingTransport
import InteractingSLE.WangWu.SeedTailFinishAssembly

/-!
# Proposition 4.19 and the four-chamber joint statement

PROVE-WW-B27. Both geometric landing inputs, the shifted image law, and the
killed right barrier are proved. The final results have no added hypotheses.
-/

set_option autoImplicit false
noncomputable section

universe u

namespace InteractingSLE.WangWu.SeedTail

/-- The slit landing, with its planar side transport discharged. -/
theorem slitRightLandingStatement : SlitRightLandingStatement :=
  slitRightLandingStatement_of_sideTransport reversedTailSideTransportStatement

/-- The deterministic translation from the killed right barrier to the two
original tail conditions. -/
theorem tailChartStatement : TailChartStatement.{u} :=
  tailChartStatement_of_landing slitRightLandingStatement positiveLandingGapStatement

/-- The small-height-gap tail statement of Proposition 4.19. -/
theorem seedTailSmallStatement : SeedField.SeedTailSmallStatement.{u} :=
  seedTailSmallStatement_of_tailChart tailChartStatement

/-- Proposition 4.19, with every shifted-law, barrier, and chart input discharged. -/
theorem prop419Statement : SeedField.Prop419Statement.{u} :=
  SeedField.prop419Statement_of_seedTailSmall seedTailSmallStatement

/-- The four-chamber joint statement, from Proposition 4.19 and B28. -/
theorem chamber4JointStatement : Chamber4.Chamber4JointStatement.{u} :=
  ChamberCond.chamber4JointStatement_of_prop419' prop419Statement

end InteractingSLE.WangWu.SeedTail
