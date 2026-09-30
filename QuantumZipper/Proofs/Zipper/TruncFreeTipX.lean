import QuantumZipper.Proofs.Zipper.TruncFreeCore
import QuantumZipper.Proofs.Zipper.TipXScaleMain

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# TRUNCFREE: TX-SC (`tipXPieceMom_of_unit`) without `TruncRescaleFreeStmt`

Task TRUNCFREE (decision in `handoff/TRUNCFREE.md`). `WedgeUnzip.tipXPieceMom_of_unit`
(`TipXScaleMain.lean`) uses `F2.TruncRescaleFreeStmt` only to know that the scaled normalized
sample `scNrm κ a X = nrm (sfTrunc (rescale X Q a))` is a free field (`scPair_props`), so that the
unit statements, the gauge regularity and `YGoodAllStmt` can be applied to it. Here the scaled
sample is replaced by `scNrmR κ a X = nrm (rawRescale X Q a)`, which is free without any
hypothesis (`F2.isFreeGFFModConstH_rawRescale`), and every conclusion is moved back to `scNrm`:
the two samples agree a.s. at all dyadic folded circles (`ae_dyAgree_scNrm`, from
`F2.ae_rawRescale_fc_dyadic`), and all quantities involved (`RegShift`, `unzY`, `pieceA`,
`pieceT`) read a field only there (`regShift_congr_dy`, `unzY_congr_dy`, `pieceA_congr_dy`,
`pieceT_congr_dy`). The remaining argument is copied verbatim from `tipXPieceMom_of_unit`.

Own elementary bookkeeping (Sheffield arXiv:1012.4797, §5.1 pp. 60–62 for the scaling rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace WedgeUnzip

/-! ## Agreement at dyadic folded circles -/

/-! ## The raw scaled sample -/

/-- The normalized raw scaled field `nrm (rawRescale x Q a)` (compare `scNrm`). -/
def scNrmR (κ a : ℝ) (x : FieldSample) : FieldSample :=
  B1Full.nrm (F2.rawRescale x (Qc (Real.sqrt κ)) a)

variable {Ω : Type} [MeasurableSpace Ω]

/-- **The raw scaled pair is an admissible normalized pair** (as `scPair_props`, without
`TruncRescaleFreeStmt`). -/
theorem scPairR_props {κ : ℝ} {P : Measure Ω} [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ}
    {X : Ω → FieldSample} (hB : IsBrownianReal B P) (hX : IsFreeGFFModConstH X P)
    (hind : IndepFun (pathOf B) X P) (k : ℕ) :
    IsBrownianReal (scB k B) P ∧ IsFreeGFFModConstH (fun ω => scNrmR κ (radius k) (X ω)) P ∧
      IndepFun (pathOf (scB k B)) (fun ω => scNrmR κ (radius k) (X ω)) P ∧
      RegUnif.IsNrmSample (fun ω => scNrmR κ (radius k) (X ω)) := by
  have hc : (radius k ^ 2).toNNReal ≠ 0 := by
    rw [Ne, Real.toNNReal_eq_zero, not_le]; exact pow_pos (radius_pos k) 2
  refine ⟨hB.smul hc, ?_, ?_, fun ω => RegUnif.nrm_nrm _⟩
  · exact RegUnif.isFreeGFFModConstH_nrmF
      (F2.isFreeGFFModConstH_rawRescale hX (Qc (Real.sqrt κ)) (radius_pos k))
  · have h1 := F2.indepFun_pathOf_bmScale (radius k) hind
    have h2 := F2.indepFun_rawRescale h1 (Qc (Real.sqrt κ)) (radius k)
    rw [← scB_eq] at h2
    exact RegUnif.indepFun_nrmF h2

end WedgeUnzip
end QuantumZipper
