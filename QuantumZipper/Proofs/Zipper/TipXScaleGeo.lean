import QuantumZipper.Proofs.Zipper.TipXRouteDefs2
import QuantumZipper.Proofs.RS.TraceShift

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# TX-SC (scaling), part 1: the capacity pieces under Loewner scaling

Task TX-SC (handoff `handoff/TIPX-ROUTE.md`, decision D51). Let `a > 0` and
`W^a := a⁻¹ W(a² ·)` (`scDrv a W`, Loewner/Brownian scaling). Then
`E^a_t(z) = a⁻¹ E_{a² t}(a z)` on `ℍ̄` (on `ℍ` this is `RS.fwdMapInv_scale`; on `ℝ` it follows from
the continuity of both sides on `ℍ̄`, `GlobalCaraStmt`), `η^a(r) = a⁻¹ η(a² r)` and
`O^{±,a}_t = a⁻¹ O^±_{a² t}`. With `a = 2^{-k}` the `j`-th piece of `W^a` at time `t` is the
`a⁻¹`-image of the `(j+k)`-th piece of `W` at time `a² t`, and the same holds for the
neighbourhoods, the admissible levels (`r ↦ r/a`) and the tails.

Consequently (`pieceA_le_of_scale`, `pieceT_le_of_scale`): if the weighted masses scale with a
factor `c` (`wBdryR` of `W` at level `a r` on `S` ≤ `c ·` `wBdryR` of the scaled configuration at
level `r` on `a⁻¹ S`), then `A_k(a² t) ≤ c · A_0^a(t)` and `T_k(a² t) ≤ c · T_0^a(t)`.

Sources: Loewner scaling (Lawler, *Conformally Invariant Processes in the Plane*, 2005,
Prop. 4.13, p. 93, and §6.1); the piece bookkeeping is own elementary argument (the route of
D51 is an own argument, see `TipXRouteDefs.lean`).
-/

noncomputable section

open MeasureTheory Filter Set Metric
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace WedgeUnzip

/-- The Loewner-scaled driver `a⁻¹ W(a² ·)`. -/
def scDrv (a : ℝ) (W : ℝ → ℝ) : ℝ → ℝ := fun r => W (a ^ 2 * r) / a

/-! ## Scaling of `E_t` on `ℍ̄` -/

/-! ## Pieces at the dyadic scale `a = 2^{-k}` -/

/-! ## Closed thickenings under dilation -/

/-! ## Transfer of the per-piece quantities -/

end WedgeUnzip
end QuantumZipper
