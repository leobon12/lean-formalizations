/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB4RTop
import InteractingSLE.Spec.Supplement.SBS3DyInst
import InteractingSLE.Spec.Supplement.SBS3DzSB4RMirrorLeaf
import InteractingSLE.Spec.Supplement.SBS3DxSBLyGen
import InteractingSLE.Spec.Supplement.SBS3DySBLyLeaf

/-!
# Successor of `SB4RTop` with the upper angle `ψ ≤ π/2` (decision D22, ruling R121)

Worker PROVE-R6-CORNER (round 8). Declarations of `SB4RTop` restated with the bound `ψ ≤ π/2` on
the upper angle (an instance argument `[Fact (ψ ≤ Real.pi / 2)]` after the angle's binder), so that
Lemma S3 enters only as `Tc.SB2EntranceNoCommonArcLeStatement` (PROVED from Theorems 1.2–1.3,
`Tc.sb2EntranceNoCommonArcLeStatement_of_thm`). The proofs are those of the original file. Names: the
original names with the suffix `Le` (statements: `…LeStatement`).

* `sb4DistinctSeedLaunchTailRStatement_of_liftLe`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

namespace InteractingSLE.Wire

open Theorem14

/-- **SB4's distinct-seed leaf `hDS` with R95's premise**, from SB2(2) (R99), its mirror and their pointwise lifts. -/
theorem sb4DistinctSeedLaunchTailRStatement_of_liftLe (hSB2 : SB.Lz.SB2LowerLaunchEntryAdmStatement.{u})
    (hLift : SB.Lf.SB2LowerTailLiftStatement.{u}) (hSB2L : SB.Lf.SB2LeftLaunchStatement.{u})
    (hLiftL : SB.Lf.SB2LeftTailLiftStatement.{u}) (hPR : WalkCont.RightWalkProperRegStatement.{u})
    (hPL : GW3SidedProof.LeftWalkProperRegStatement.{u}) (h13 : Exist.Theorem13Statement.{u}) :
    SB.Ly.SB4DistinctSeedLaunchTailRLeStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg l hl h41
  exact ⟨fun u hu hθ hL _ => SB.Lf.scheduleLaunchTailR_lower hSB2 hLift hPR h13 hκ hκ4 hb hh hcf hζ' hE hreg
      hl hu hθ hL,
    fun v hv hθ hR hH => SB.Lf.scheduleRelativeTailR_leftLe hSB2L hLiftL hPL h13 hκ hκ4 hb hh hcf hζ' hE hreg
      hl h41 hv hθ hR hH⟩

end InteractingSLE.Wire
