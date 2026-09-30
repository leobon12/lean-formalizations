import QuantumZipper.Proofs.Thm18.G4CMeas3Gate
import QuantumZipper.Proofs.Zipper.WedgeUnzipXC
import QuantumZipper.Proofs.LQG.GoodTransforms
import QuantumZipper.Proofs.Zipper.F1NodeAsm
import QuantumZipper.Proofs.Zipper.FlowRegCfg
import QuantumZipper.Proofs.Zipper.E1TransferM4Ae
import QuantumZipper.Proofs.Zipper.WedgeUnzipAddFun

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# `PStarBCertAllStmt` from the all-times goodness of `P_*` samples

A good sample (`IsLQGGood`: regular, with offset-uniform boundary and area limits) is
`BCert`-certified: its dyadic boundary approximations have continuous densities, hence are finite
on windows, and converge vaguely (`F1.isVagueLimitR_of_hasBdryLimit`); `E1.M4.bCert_of_isVagueLimitR`
then applies. Hence `PStarBCertAllStmt` follows from the existing frontier leaf
`WedgeUnzip.PStarGoodAllStmt` (goodness of the unzipped `P_*` field at all times `t ≥ 0`).

Own elementary bookkeeping.
-/

noncomputable section

open MeasureTheory Set Filter
open scoped NNReal ENNReal

namespace QuantumZipper
namespace Thm18Asm
namespace G4Core

/-- **A good sample is boundary-certified.** -/
theorem bCert_of_isLQGGood {γ : ℝ} {x : FieldSample} (h : IsLQGGood γ x) : E1.M4.BCert γ x := by
  obtain ⟨hR, ⟨ν, hν⟩, -⟩ := h
  obtain ⟨F, hF⟩ := id hR
  refine E1.M4.bCert_of_isVagueLimitR (fun k N => ?_) (F1.isVagueLimitR_of_hasBdryLimit hR hν)
  refine E1.bdryApprox_Icc_lt_top_of_continuousOn ?_ N
  have hc : ContinuousOn (fun w : ℂ => F (w, radius k)) Hbar :=
    hF.1.comp (continuousOn_id.prodMk continuousOn_const) fun w hw => ⟨hw, radius_pos k⟩
  exact hc.congr fun w hw => WedgeUnzip.avgReg_eq_of_regularWith hF k hw

end G4Core
end Thm18Asm
end QuantumZipper
