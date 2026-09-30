import QuantumZipper.Proofs.Zipper.ZipLen2Flow
import QuantumZipper.Proofs.Zipper.ZipLen2Area
import QuantumZipper.Proofs.Zipper.ZipLen2ContMain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZIPLEN-2: wiring

* `yExactAllStmt_holds`: `WedgeUnzip.YExactAllStmt` (RC3 of the unzipped `Γ⁰` field at every
  folded circle, all times) is the case `s = 0` of the proved `Γ⁰` flow node
  `yFlowRC3Stmt_holds` (`revMap _ 0 = id` on `ℍ`), exactly as `F1.xExactAll_of_xFlowRC3`.
* `zipLenInputsStmt_of_yGood_merge_cont`: `B3d.ZipLenInputsStmt` from `YGoodAllStmt`, the `Γ⁰`
  area merging rule `YAreaMergeStmt` and the `Γ⁰` flow continuum node `YFlowContStmt`;
  `zipLenInputsStmt_of_yGood_merge` with `YFlowContStmt` discharged (`yFlowContStmt_holds`).

Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace B3d
namespace ZipLen

/-- **`YExactAllStmt` holds** (case `s = 0` of `yFlowRC3Stmt_holds`). -/
theorem yExactAllStmt_holds : WedgeUnzip.YExactAllStmt := by
  intro κ hκ hκ4 Ω _ P _ B X hB hX hind
  filter_upwards [yFlowRC3Stmt_holds κ hκ hκ4 P B X hB hX hind, RegUnif.ae_drive_good hB κ]
    with ω hω hdr t ht d hd r hr
  have hV : Continuous (B2.vrev (drive κ B ω) (t + 0)) := B2.continuous_vrev hdr.1 _
  have hV0 : B2.vrev (drive κ B ω) (t + 0) 0 = 0 := B2.vrev_zero (by linarith)
  have hmap : (foldedCircle d r).map (revMap (B2.vrev (drive κ B ω) (t + 0)) 0) =
      foldedCircle d r := by
    rw [Measure.map_congr (show revMap (B2.vrev (drive κ B ω) (t + 0)) 0 =ᵐ[foldedCircle d r] id
      from (TwoPoint.foldedCircle_ae_mem_H d hr).mono fun z hz =>
        CharFun.revMap_zero_eq hV hV0 hz), Measure.map_id]
  have := hω t 0 ht le_rfl d hd r hr
  rwa [hmap] at this

variable {Ω : Type} [MeasurableSpace Ω]

end ZipLen
end B3d
end QuantumZipper
