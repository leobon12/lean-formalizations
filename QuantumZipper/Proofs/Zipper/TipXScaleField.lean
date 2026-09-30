import QuantumZipper.Proofs.Zipper.TipXScaleMass
import QuantumZipper.Proofs.Zipper.ScaleGeomFix
import QuantumZipper.Proofs.Zipper.ScaleGeomInBasic
import QuantumZipper.Proofs.Zipper.RegShiftUnif
import QuantumZipper.Proofs.Zipper.FSMeasBasic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# TX-SC (scaling), part 3: the deterministic per-time comparison

Task TX-SC (handoff `handoff/TIPX-ROUTE.md`, decision D51). Fix `a ∈ (0, 1]`, a driver `W` and a
field `x`, and let `x' = sfTrunc (rescale x Q a)` (the D27 measurable version of
`x(a·) + Q log a`), `x'' = nrm x'` (gauge-normalized, D37), `W' = a⁻¹ W(a² ·)`. Given, at the time
`a² t` resp. `t`,
* the D45 scaling identity (`F2.ScaleGeomAeStmt'`'s `RegEq` conjunct and its regularity and
  side-limit conjuncts),
* the `RegShift` regularity of `h⁰ + x''` along the pushed dyadic circles (`GaugeRegDyStmt`),
* the regularity of the unzipped field of `x''` (`YGoodAllStmt`),
* continuity of `E_{a² t}` and `E'_t` on `ℍ̄` (`GlobalCaraStmt`) and the trace scaling,
we get `A_k(a² t) ≤ c · A''_0(t)` and `T_k(a² t) ≤ c · T''_0(t)` with
`c = a^{−κ/2} e^{γ C/2}`, `C = (2/γ) log a + x'(fc(0,1))` (`piece_le_scaled`).

Sources: Sheffield arXiv:1012.4797, §5.1, pp. 60–62 (`h ↦ h(a·) + Q log a`, constants multiply
lengths by `e^{γC/2}`); the bookkeeping is own elementary argument.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace WedgeUnzip

/-- The total additive constant between the D45-scaled field and the normalized scaled field. -/
def scConst (κ a : ℝ) (x : FieldSample) : ℝ :=
  2 / Real.sqrt κ * Real.log a +
    FSMeas.sfTrunc (rescale x (Qc (Real.sqrt κ)) a) (foldedCircle 0 1)

end WedgeUnzip
end QuantumZipper
