import QuantumZipper.Proofs.Thm18.G1ZA1cDet
import QuantumZipper.Proofs.Thm18.G1ZSplitWire
import QuantumZipper.Proofs.Thm18.G4
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
import QuantumZipper.Proofs.Thm18.JordanChordA1a
import QuantumZipper.Proofs.Thm18.G1FM2Final
import QuantumZipper.Proofs.Thm18.Thm18HeadlineV3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1Z-A1c: `G1RerootLenStmt` (lengths at the new root after unzipping by quantum length `ℓ`)

Source: Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, proof of Theorem 1.8
(§5.4, pp. 69–71): the configuration unzipped by quantum length `ℓ` is again a configuration of the
same law, the old root is carried to `O^∓_{t'}`, and the boundary arc between it and the new root
has quantum length `ℓ` on both sides (the left length by definition of the unzipping time, the right
one because both lengths agree, F1 = `LenEqStmt`).

Proof here:
* `t' > 0`: the unzipping times are strictly increasing in `ℓ` (`G4UnzipTimeStrictStmt`, from the
  no-overshoot node `G4UnzipPassStmt` and `G4UnzipGoodStmt`); `a > 0`: `G4UnzipGoodStmt`.
* The identified B0 transport (`G1BdryGood'`, `g1z5_bdryRepId`, from `G1Z4SideLimPathStmt`) holds
  on a measurable set of path/data pairs of full measure for the wedge configuration; since the
  configuration data of `c' = Z^LEN_{−ℓ} c` have the same law (E6), they lie in that set a.s.
  Likewise the boundary regularity `BReg` of the field of `c'` (atomless, positive on intervals)
  transfers from the wedge by E6.
* The length computation (`G1ZA1c.g1zA1c_seg`): the side measure of `c'` is the pushforward of
  `ν_{rescale x' Q a}|_half` by `Φ⁻¹`, `a Φ β = O`, and `ν_{rescale x' Q a}[u,v] = ν_{x'}[au, av]`
  (`qBoundaryMeasure_rescale_Icc`); `ν_{x'}[O^-_{t'}, 0] = ℓ` is the no-overshoot node.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G1ZA1c

/-- The path/data pair read from configuration data (the driver divided by `γ`). -/
def cfgPath (γ : ℝ) (q : ((ℕ → ℝ) × (TestFun H → ℝ)) × (ℝ≥0 → ℝ)) : G1PathData :=
  (fun t => q.2 t / γ, q.1)

theorem measurable_cfgPath (γ : ℝ) : Measurable (cfgPath γ) :=
  (measurable_pi_iff.2 fun t => ((measurable_pi_apply t).comp measurable_snd).div_const γ).prodMk
    measurable_fst

theorem pathDrive_cfgPath {γ : ℝ} (hγ : 0 < γ) {W : ℝ → ℝ} (hW : ∀ s, W s = W (max s 0))
    (d : (ℕ → ℝ) × (TestFun H → ℝ)) :
    pathDrive (γ ^ 2) (cfgPath γ (d, fun t : ℝ≥0 => W t)).1 = W := by
  funext t
  simp only [pathDrive, cfgPath]
  rw [Real.sqrt_sq hγ.le, Real.coe_toNNReal', mul_div_cancel₀ _ hγ.ne']
  exact (hW t).symm

end G1ZA1c

end Thm18Asm
end QuantumZipper
