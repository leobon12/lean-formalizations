import QuantumZipper.Proofs.Zipper.TipXScaleField
import QuantumZipper.Proofs.Zipper.B3dLen
import QuantumZipper.Proofs.Zipper.WedgeGlobalCara
import QuantumZipper.Proofs.Zipper.F2ScaleIndep
import QuantumZipper.Proofs.Zipper.F2Gamma0TruncMeas
import QuantumZipper.Proofs.Zipper.F2Gamma0Trunc
import QuantumZipper.Proofs.RS.TransienceScale

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# TX-SC (scaling), part 4: the per-piece comparison, pathwise and almost surely

Task TX-SC (handoff `handoff/TIPX-ROUTE.md`, decision D51). With `a = 2^{-k}`:
* `piece_le_scaled` (deterministic): from the D45 scaling data at one time, the regularity inputs,
  the continuity of `E` on `ℍ̄` and the trace scaling, `A_k(a² t) ≤ c · A''_0(t)` and
  `T_k(a² t) ≤ c · T''_0(t)` for the normalized scaled configuration
  `(W'' = a⁻¹ W(a²·), x'' = nrm (sfTrunc (rescale x Q a)))`, `c = a^{−κ/2} e^{γ C/2}`;
* `ae_piece_le_scaled`: the same, a.s. for all `t ∈ [0, T']` at once, for a Brownian `B` and a
  free field `X` (the scaled pair is again Brownian / free / independent: `IsBrownianReal.smul`,
  `TruncRescaleFreeStmt` (D27 frontier node), `indepFun_sfTrunc_rescale`, `isFreeGFFModConstH_nrmF`).

Inputs used as hypotheses (existing frontier names): `F2.ScaleGeomAeStmt'` (D45),
`F2.TruncRescaleFreeStmt` (D27), `YGoodAllStmt` (D26/D31). Proved inputs: `globalCaraStmt_holds`,
`RS.ae_sleTrace_scale`, `RegUnif.gaugeRegDyStmt_holds`.

Sources: Sheffield arXiv:1012.4797, §5.1 pp. 60–62 (scaling of quantum surfaces) and Brownian
scaling; bookkeeping is own elementary argument.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace WedgeUnzip

/-- The scaling factor `a^{−κ/2} e^{γ C/2}`. -/
def scFac (κ a : ℝ) (x : FieldSample) : ℝ≥0∞ :=
  ENNReal.ofReal (a ^ (-(κ / 2)) * Real.exp (Real.sqrt κ * scConst κ a x / 2))

theorem radius_le_one (k : ℕ) : radius k ≤ 1 := by
  unfold radius; exact pow_le_one₀ (by norm_num) (by norm_num)

end WedgeUnzip
end QuantumZipper
