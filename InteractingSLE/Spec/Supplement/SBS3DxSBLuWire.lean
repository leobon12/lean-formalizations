/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLuWire
import InteractingSLE.Spec.Supplement.SBS3DwBase
import InteractingSLE.Spec.Supplement.SBS3DxSBLyGen

/-!
# Successor of `SBLuWire` with the upper angle `ψ ≤ π/2` (decision D22, ruling R121)

Worker PROVE-R6-CORNER (round 8). Declarations of `SBLuWire` restated with the bound `ψ ≤ π/2` on
the upper angle (an instance argument `[Fact (ψ ≤ Real.pi / 2)]` after the angle's binder), so that
Lemma S3 enters only as `Tc.SB2EntranceNoCommonArcLeStatement` (PROVED from Theorems 1.2–1.3,
`Tc.sb2EntranceNoCommonArcLeStatement_of_thm`). The proofs are those of the original file. Names: the
original names with the suffix `Le` (statements: `…LeStatement`).

* `sb3InductionGenRStatement_of_pathLe`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H Hbar)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.LuM

open Lx Lv Lw Sec4 Exist.Staged Exist.StagedLaw

/-- **R95's amended SB3** (`Ly.SB3InductionGenRLeStatement`, the binder `hSB3` of Theorem 1.4's top) from SB2(1) in
GW1's ambient setting, Theorems 1.2–1.3, the small-gap fibre cover and the stage input (I5). -/
theorem sb3InductionGenRStatement_of_pathLe (hSB2 : Ly.SB2UpperLaunchEntryLAmbLeStatement.{u})
    (h12 : Exist.Theorem12Statement.{u}) (h13 : Exist.Theorem13Statement.{u})
    (h12₀ : Exist.Theorem12Statement.{0}) (h13₀ : Exist.Theorem13Statement.{0})
    (hDy : Sec5.Aux61Act.DyActFibreCoverOn.{u}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hDy₀ : Sec5.Aux61Act.DyActFibreCoverOn.{0}
      (fun κ θ₁ θ₂ => ¬ Sec5.Prop51G.IsLargeGap κ θ₁ θ₂) Sec5.Aux61Cov.RefWin)
    (hPath : SB3StagePathRStatement.{u}) : Ly.SB3InductionGenRLeStatement.{u} :=
  Ly.sb3InductionGenRStatement_of_inputs_dyCoverLe hSB2 h12 h13 h12₀ h13₀ hDy hDy₀
    (sb3StageInputsRStatement_of_path hPath)

end InteractingSLE.Theorem14.SB.LuM
