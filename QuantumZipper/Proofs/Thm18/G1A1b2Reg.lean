import QuantumZipper.Proofs.Thm18.G1A1bMain
import QuantumZipper.Proofs.Zipper.LocLenPStarGood

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1A1b2 (reg): the regularity clause of SideRTX, from the proved all-times goodness

`R18.G1A1bSideRTXStmt` (G1A1bMain.lean) asks, a.s. for all `t > 0`, that the unzipped field
`U_t = coordChange Y f_t⁻¹ Q` be regular with a witness `F` along which the side family converges.
The regularity half is the proved all-times goodness off the tip of `P_*` samples,
`LocLen.pStarGoodOffAll_of_yMergeOffTip SWCore.yMergeOffTipStmt_holds` (D75 route; the Theorem 1.8
sample is a `P_*` sample by `Thm18Asm.isPStarSample_of_setting`). What remains is the
convergence clause, for every regularity witness (`G1A1b2SideConvStmt`).

* **`sideRTX_of_conv`**: `G1A1b2SideConvStmt → G1A1bSideRTXStmt`;
* `g1ZA1bSideExactArcStmt_of_conv`: the headline input `hA1b` from the convergence node.

Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace R18

open Thm18Asm LocLen

/-- A.s. every unzipped field of the Theorem 1.8 configuration is a regular sample. -/
theorem ae_isRegularSample_unzipped {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {Y : Ω → FieldSample}
    (hS : Thm18Setting γ P B Y) :
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
      IsRegularSample (coordChange (Y ω) (fwdMapInv (drive (γ ^ 2) B ω) t) (Qc γ)) := by
  have hs : Real.sqrt (γ ^ 2) = γ := Real.sqrt_sq hS.1.le
  filter_upwards [pStarGoodOffAll_of_yMergeOffTip SWCore.yMergeOffTipStmt_holds (γ ^ 2) P Y B
    (isPStarSample_of_setting hS)] with ω hω t ht
  have h := (hω t ht).1
  rw [hs] at h
  exact h

end R18
end QuantumZipper
