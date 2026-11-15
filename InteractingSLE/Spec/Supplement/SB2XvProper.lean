/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2LkCurve
import InteractingSLE.Spec.Supplement.SBLyTop
import InteractingSLE.Spec.Supplement.GW1WalkExitStatement
import InteractingSLE.Spec.Supplement.GW1ParamProof

/-!
# The lower walk is a proper curve, from Theorems 1.2–1.3

Packet PROVE-T14-SB2LIFT (round 27). The almost-sure assembly of the per-stage correspondence instantiates the bundle
of `RelDriverAtT` at a proper parametrization of the lower walk. **`rightWalkProperReg_of_thms`**: GW1's
parametrization (`GW1X.rightWalkProperRegStatement_of_gw1ParamR51`) from Theorems 1.2–1.3 (GB6's restart, BW1's terminal
path, the retarget path, the walk launch clock and the walk-exit geometry), the derivation of PROVE-SB2-LCMEAN's
`Mr.rightWalkProperRegStatement_of_thms` (round 12, not landed) from landed results only.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

namespace InteractingSLE.Theorem14.SB.Mn

/-- **The lower walk is a proper curve** (Theorems 1.2–1.3). -/
theorem rightWalkProperReg_of_thms (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0}) :
    WalkCont.RightWalkProperRegStatement.{u} := by
  have hD := Supp8.GB6LMean.gb6HullDetStatement_of_thm12_thm13 h12 h13
  have h12p := Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12 h13
  have h12p₀ := Exist.Param12.theorem12ParamStatement_of_thm12_thm13 h12₀ h13₀
  have hBW1 := BW1LMean.bw1Statement_of_thm12_thm13 h12p h12 h13 h13₀
    (Restart.canonicalDriverCodeStatement_of_param h12p₀ h13₀)
  have hBR4a := BR4aIn.br4aStatement_of_thm12_thm13 h12 h13 h12₀ h13₀
  have hGB6 := Wire.gb6RestartStatement_of_hullDet_now h12₀ h13₀ hD
  have hClock := GW1Laws.walkLaunchClockStatement_of_paths hGB6 h12p h13 h13₀
    (BW1Det.terminalPathStatement_of_bw1_graph hBW1 h12p h13 h13₀)
    (GW1Det.retargetPathStatement hBR4a h12p h13 h13₀)
  have hD4 := GW1WalkExit.walkD4GeometryStatement_of_theorem13 h13 h13₀
  have hGR := (GW1WalkExit.paramEveryRegStatements_of_walkClock_and_geometry hGB6 h13 h13₀ hClock hD4).1
  exact GW1X.rightWalkProperRegStatement_of_gw1ParamR51 (GW1X.gw1ParamR51Statement_of_everyReg hGR)

end InteractingSLE.Theorem14.SB.Mn
