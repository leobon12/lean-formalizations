/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2WdFinal
import InteractingSLE.Spec.Supplement.SBS3DwBase
import InteractingSLE.Spec.Supplement.SBS3DxKAmb
import InteractingSLE.Spec.Supplement.SBS3DxKSplit
import InteractingSLE.Spec.Supplement.SBS3DxSBLyGen

/-!
# Successor of `SB2WdFinal` with the upper angle `ψ ≤ π/2` (decision D22, ruling R121)

Worker PROVE-R6-CORNER (round 8). Declarations of `SB2WdFinal` restated with the bound `ψ ≤ π/2` on
the upper angle (an instance argument `[Fact (ψ ≤ Real.pi / 2)]` after the angle's binder), so that
Lemma S3 enters only as `Tc.SB2EntranceNoCommonArcLeStatement` (PROVED from Theorems 1.2–1.3,
`Tc.sb2EntranceNoCommonArcLeStatement_of_thm`). The proofs are those of the original file. Names: the
original names with the suffix `Le` (statements: `…LeStatement`).

* `sb2UpperLaunchEntryLAmbStatement_of_driverLinkLe`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology Metric
open scoped NNReal ENNReal
open QuantumZipper (chiC H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.SB.Lv

open Exist Exist.Staged Exist.StagedLaw Restart GW1W

variable {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ}

/-- **SB2(1) in the ambient form from Theorem 1.3 and the driver link alone**
(`sb2UpperLaunchEntryLAmbStatement_of_partsLe` with the active word proved). -/
theorem sb2UpperLaunchEntryLAmbStatement_of_driverLinkLe (h13 : Exist.Theorem13Statement.{u})
    (hd : SB2DriverLinkAmbLeStatement.{u}) : Ly.SB2UpperLaunchEntryLAmbLeStatement.{u} :=
  sb2UpperLaunchEntryLAmbStatement_of_partsLe h13 sb2ActiveWordAmbStatement hd

end InteractingSLE.Theorem14.SB.Lv
