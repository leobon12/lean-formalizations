/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB4InitialArc

/-!
# The regularized sewn frontier from the two explicit switch comparisons

The countable-family and closure arguments already landed in `SB4Clauses` are
reused here. Neither switch comparison is asserted proved by these adapters.
The frontier conclusion is exactly `SBFrontierRegStatement` (ruling R51).
-/

set_option autoImplicit false

universe u

namespace InteractingSLE.Theorem14.SB

/-- SB's regularized frontier statement from GW2, GW0 and the two still-open
one-piece comparisons of SB4. -/
theorem sbFrontierRegStatement_of_switch
    (hGW2 : GW2LightConeStatement.{u}) (hGW0 : GW0.GW0ForwardStatement.{u})
    (hDS : SB4DistinctSeedSwitchRegStatement.{u})
    (hIA : SB4InitialArcSwitchRegStatement.{u}) : SBFrontierRegStatement.{u} :=
  sbFrontierRegStatement_of_sb4Reg hGW2 hGW0
    (sb4DistinctSeedRegStatement_of_switch hDS) (sb4InitialArcRegStatement_of_switch hIA)

/-- Theorem 1.3 supplies GW0; the existing GW2 assembly supplies the light-cone
input from its named open inputs. The SB4 switch comparisons remain hypotheses. -/
theorem sbFrontierRegStatement_of_open_switch
    (h13 : Exist.Theorem13Statement.{u}) (h13₀ : Exist.Theorem13Statement.{0})
    (hBR6 : BR6.BR6Statement.{u})
    (hC0 : GW2Cone.GW2ScheduleContainmentStatement.{u})
    (hCv : GW2Cone.GW2ArcScheduleContainmentStatement.{u})
    (hEx : GW2Cone.GW2TipExhaustionStatement.{u})
    (hDS : SB4DistinctSeedSwitchRegStatement.{u})
    (hIA : SB4InitialArcSwitchRegStatement.{u}) : SBFrontierRegStatement.{u} :=
  sbFrontierRegStatement_of_switch
    (Wire.gw2LightConeStatement_of_open5 h13 h13₀ hBR6 hC0 hCv hEx)
    (BR3Ref.gw0ForwardStatement_of_theorem13 h13₀) hDS hIA

end InteractingSLE.Theorem14.SB
