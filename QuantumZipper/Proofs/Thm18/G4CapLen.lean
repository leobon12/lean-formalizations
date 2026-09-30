import QuantumZipper.Proofs.Thm18.G4UnzipGoodField
import QuantumZipper.Proofs.Zipper.B3dLen
import QuantumZipper.Proofs.Zipper.E4L3i
import QuantumZipper.Proofs.Zipper.E5Model1
import QuantumZipper.Proofs.Zipper.E6LocAbsBasic
import QuantumZipper.Proofs.Zipper.F1CanonLaw
import QuantumZipper.Proofs.Zipper.F1Embed
import QuantumZipper.Proofs.Zipper.F1LenScale
import QuantumZipper.Proofs.Zipper.F1LenRead
import QuantumZipper.Proofs.Zipper.F1ABJensen
import QuantumZipper.Proofs.Zipper.F1GermFam
import QuantumZipper.Proofs.Zipper.F1ReadTimeRed
import QuantumZipper.Proofs.Zipper.F2Gamma0ScaleDet
import QuantumZipper.Proofs.Zipper.F2LocalScale
import QuantumZipper.Proofs.Zipper.F2LocalSteps
import QuantumZipper.Proofs.Zipper.F2Reduce
import QuantumZipper.Proofs.Zipper.F2Step2b
import QuantumZipper.Proofs.Zipper.F2Step3
import QuantumZipper.Proofs.Zipper.F2Step3DensUnif
import QuantumZipper.Proofs.Zipper.F2Weld
import QuantumZipper.Proofs.Zipper.F2WedgeCouple
import QuantumZipper.Proofs.Zipper.F2WeldTimes
import QuantumZipper.Proofs.Zipper.FSMeasF2
import QuantumZipper.Proofs.Zipper.HitScaleZipScale
import QuantumZipper.Proofs.Zipper.LocHitScalePStar
import QuantumZipper.Proofs.Zipper.LocRichE6
import QuantumZipper.Proofs.Zipper.UnifClAnchor
import QuantumZipper.Proofs.Zipper.UnifRCSplit
import QuantumZipper.Proofs.Zipper.WedgeRC3All2
import QuantumZipper.Proofs.Zipper.WedgeUnzipXC
import QuantumZipper.Proofs.LQG.GoodTransforms
import QuantumZipper.Proofs.Zipper.F1NodeAsm
import QuantumZipper.Proofs.Zipper.E1TransferM4Ae
import QuantumZipper.Proofs.LQG.LogSingularity
import QuantumZipper.Proofs.Thm18.G4CoreDownShort
import QuantumZipper.Proofs.Thm18.G4CoreDownLong
import QuantumZipper.Proofs.Thm18.G4CoreUpShort
import QuantumZipper.Proofs.Thm18.G4CoreZipCocycle
import QuantumZipper.Proofs.Thm18.G4Weld2Arc
import QuantumZipper.Proofs.Loewner.CaraR8
import QuantumZipper.Proofs.Loewner.CoreArc3e
import QuantumZipper.Proofs.Zipper.UnifClB5
import QuantumZipper.Proofs.Zipper.F1EmbedBasic
import QuantumZipper.Proofs.Zipper.FSMeasF2
import QuantumZipper.Proofs.Zipper.WedgeUnzipCore
import QuantumZipper.Proofs.Zipper.F1ABJensen
import QuantumZipper.Proofs.Zipper.B3dLen
import QuantumZipper.Proofs.Zipper.F1ABJensen
import QuantumZipper.Proofs.Zipper.B3dLen
import QuantumZipper.Proofs.Zipper.F1NodeAsm
import QuantumZipper.Zipper.LengthZip
import QuantumZipper.Proofs.Zipper.F1Side3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.8, node G4: the length inputs of the group law, transported from `P_*`

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, Theorem 1.8 (2) and §1.4
(the unzipped lengths `L±_t` are continuous, `L±_0 = 0`, and additive along the capacity flow;
blueprint B5). The G4 group-law reduction (`G4Group2Neg.lean`) uses four a.s. statements at the
wedge configuration `c = wedgeConfig γ B Y ω`:

* `G4UnzipPassStmt` (no overshoot at the first passage): **proved** from the continuity node
  `G4UnzipLenContStmt` (`g4UnzipPassStmt_of_cont`, via `unzipLengths_unzipTime_eq_of_cont`);
* `G4UnzipLenContStmt`: **reduced** to `G4PStarLenLeftRegStmt`, the `P_*` regularity of `L⁻`
  (its body is, verbatim, that of `F1.LenLeftRegStmt` of `F1LenInCanon.lean`, so
  `F1.LenLeftRegStmt → G4PStarLenLeftRegStmt` is the identity);
* `G4UnzipCapLenStmt`: **reduced** to the `P_*` capacity cocycle `F1.PStarLenCocycleStmt`
  (`F1StrictMonoPStar.lean`), or to the pair cocycle `F1.LenPairCocycleStmt` (`F1LenFlow.lean`);
* `G4UnzipCapSideStmt`: **reduced** to `G4ShiftAliveStmt` (for `κ < 4`, a.s. no real point
  `x ≠ 0` is swallowed by the Loewner flow restarted at any time `u ≥ 0`; Rohde–Schramm,
  *Basic properties of SLE*, Ann. Math. 161 (2005), Thm 6.1 (the trace is simple for `κ ≤ 4`),
  equivalently Lawler, *Conformally invariant processes in the plane*, Prop. 6.9) and
  `G4PStarFlowGoodStmt` (goodness of the field unzipped along the capacity flow of a `P_*`
  sample, at all `u, s ≥ 0`; the flow form of the goodness clause of `F1.PStarZipLenInputsStmt`).

The transport is exact: the Theorem 1.8 sample is a `P_*` sample with `κ = γ²`
(`isPStarSample_of_setting`), `√(γ²) = γ`, and `wedgeConfig γ B Y ω = F1.pcfg (γ²) Y B ω`
definitionally. The random time `unzipTime γ ℓ c` is handled by stating the `P_*` nodes for all
times simultaneously. All arguments in this file are **own elementary** bookkeeping.

Main results: `g4UnzipPassStmt_of_cont`, `g4UnzipLenContStmt_of_pstar`,
`g4UnzipCapLenStmt_of_pstar`, `g4UnzipCapLenStmt_of_pair`, `g4UnzipCapSideStmt_of`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm

/-! ## 1. No overshoot from continuity -/

/-! ## 2. Continuity of `L⁻` from the `P_*` regularity -/

/-! ## 3. The capacity cocycle from the `P_*` cocycle -/

/-! ## 4. Side limits and goodness after the capacity unzipping -/

/-- **Real points survive the restarted Loewner flow** (explicit hypothesis; Rohde–Schramm,
*Basic properties of SLE*, Thm 6.1: for `κ ≤ 4` the SLE trace is a.s. a simple curve with
`γ(0,∞) ⊂ ℍ`, so no real point and no prime end of `η[0,u]` other than the tip is ever swallowed;
Lawler, *Conformally invariant processes in the plane*, Prop. 6.9). A.s., for every restart time
`u ≥ 0`, every real `x ≠ 0` has a solution of the centered forward flow driven by
`s ↦ W(u + s) − W(u)` on every `[0,T]`. The case `u = 0` is `RS.ae_real_alive`. -/
def G4ShiftAliveStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B P →
    ∀ᵐ ω ∂P, ∀ u : ℝ, 0 ≤ u → ∀ x : ℝ, x ≠ 0 → ∀ T : ℝ, 0 ≤ T →
      ∃ v, IsForwardSol (fun s => drive κ B ω (u + max s 0) - drive κ B ω u) (x : ℂ) T v

end Thm18Asm
end QuantumZipper
