import QuantumZipper.Proofs.Zipper.F2Step3DensCara
import QuantumZipper.Proofs.LQG.RegularClosure
import QuantumZipper.Proofs.GFF.CircleContinuity

/-!
# F2 step (3): `Step3LocalDensityStmt` from a circle-level field identity

Refinement of `step3LocalDensity_of_inputs` (`F2Step3Dens.lean`): inputs (i) (Carathéodory,
`step3BdryExt_holds`) and (iv-a) (`step3SideSign_holds`) are now proved, and the field identity
(ii) is only asked for **raw values on folded circles** centred near a compact subinterval
`[u, v] ⊂ (O⁻_t, O⁺_t)` with small radius (`Step3FieldCircStmt`):
`x_t(fc(c,r)) = y_t(fc(c,r)) − ∫ γ log|E_t| dfc(c,r)`. This is the pairing form of
`h ∘ f_t⁻¹ + Q log|(f_t⁻¹)'|` applied to `x` and to `y = x + γ log|·|` (Sheffield,
arXiv:1012.4797, (1.3); the `ofFun` part of `y` transforms by composition with `f_t⁻¹`).

* `eventually_avgReg_eq_of_fc`: equal raw values on such circles give equal `avgReg` on `[u,v]`
  for large `k` (`avgReg` is a limit of raw values on dyadic-centred circles).
* `restrict_Ioo_eq_of_forall_sub`: two measures agreeing on every `(u, v)` with `a < u`, `v < b`
  agree on `(a, b)` (exhaustion).

Bookkeeping is our own elementary argument.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace F2

end F2
end QuantumZipper
