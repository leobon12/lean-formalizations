/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB4RSymTop
import InteractingSLE.Spec.Supplement.SBS3DyInst
import InteractingSLE.Spec.Supplement.SBS3DzSB4RMirrorLeaf
import InteractingSLE.Spec.Supplement.SBS3DzSB4RTop
import InteractingSLE.Spec.Supplement.SBS3DxSBLyGen
import InteractingSLE.Spec.Supplement.SBS3DySBLyLeaf

/-!
# Successor of `SB4RSymTop` with the upper angle `ψ ≤ π/2` (decision D22, ruling R121)

Worker PROVE-R6-CORNER (round 8). Declarations of `SB4RSymTop` restated with the bound `ψ ≤ π/2` on
the upper angle (an instance argument `[Fact (ψ ≤ Real.pi / 2)]` after the angle's binder), so that
Lemma S3 enters only as `Tc.SB2EntranceNoCommonArcLeStatement` (PROVED from Theorems 1.2–1.3,
`Tc.sb2EntranceNoCommonArcLeStatement_of_thm`). The proofs are those of the original file. Names: the
original names with the suffix `Le` (statements: `…LeStatement`).

* `sb4DistinctSeedLaunchTailRStatement_of_sb2LiftLe`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

universe u

namespace InteractingSLE.Wire

open Theorem14

/-- **SB4's distinct-seed leaf `hDS` with R95's premise from SB2(2)'s combined target** (both halves: the left one by
the reflection symmetry). -/
theorem sb4DistinctSeedLaunchTailRStatement_of_sb2LiftLe (h12 : Exist.Theorem12Statement.{u})
    (h13 : Exist.Theorem13Statement.{u}) (h13₀ : Exist.Theorem13Statement.{0})
    (hC : SB.Lh.SB2LowerLaunchLiftStatement.{u}) (hPR : WalkCont.RightWalkProperRegStatement.{u})
    (hPL : GW3SidedProof.LeftWalkProperRegStatement.{u}) : SB.Ly.SB4DistinctSeedLaunchTailRLeStatement.{u} := by
  have hCL := SB.Lf.sb2LeftLaunchLiftStatement_of_lower h12 h13 h13₀ hC
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hreg l hl h41
  exact ⟨fun u hu hθ hL _ => SB.Lf.scheduleLaunchTailR_lower_lift hC hPR h13 hκ hκ4 hb hh hcf hζ' hE hreg
      hl hu hθ hL,
    fun v hv hθ hR hH => SB.Lf.scheduleRelativeTailR_left_liftLe hCL hPL h13 hκ hκ4 hb hh hcf hζ' hE hreg
      hl h41 hv hθ hR hH⟩

end InteractingSLE.Wire
