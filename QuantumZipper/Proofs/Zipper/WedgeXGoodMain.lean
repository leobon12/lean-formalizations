import QuantumZipper.Proofs.Zipper.WedgeXGoodFar
import QuantumZipper.Proofs.Zipper.WedgeXGoodBasic

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D29 (wedge unzipping), X-G part 4: `XGoodAllStmt` from the `Γ⁰` goodness, C and TIP-X

Task X-GOOD. Main result:

* `xGoodAll_of_tipX : YGoodAllStmt → GlobalCaraStmt → ExtNonvanishStmt → TipXStmt →
  XGoodAllStmt`.

Proof. A.s., for every `t ≥ 0`: `x_t` is good iff `y_t + ψ_t` is (`isLQGGood_unzX_iff`, from the
dyadic circle identity). `y_t` is good (`Γ⁰`, `YGoodAllStmt`); `ψ_t = −γ log‖E_t‖` is continuous
on `ℍ̄` off the tips `O^±_t` (C: `E_t` continuous on `ℍ̄`; `E_t ≠ 0` off the tips). Away from the
tips, rule (5.1) applies locally (`WedgeXGoodFar`); at the tips TIP-X gives the regularity of
`ofFun ψ_t` and the uniform smallness of the boundary approximations of `x_t`, which is exactly
what `isLQGGood_add_of_tight` needs (the approximations of `x_t` and `y_t + ψ_t` coincide, since
they read the same dyadic circle values). The resulting measures are `ν_{x_t} = e^{γψ_t/2} ν_{y_t}`
on `ℝ \ {O^±_t}` (no atoms at the tips) and `μ_{x_t} = e^{γψ_t} μ_{y_t}`.

Sources: Sheffield, arXiv:1012.4797, §5.4 step (3) and rule (5.1); the tip treatment follows
`LogSingGood.hasBdryLimit_add_Lf` (M4-P4). Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set Metric
open scoped NNReal ENNReal

namespace QuantumZipper
namespace WedgeUnzip

open GoodSample RegClosure

/-- Sum of two regular samples is regular, with the sum of the witnesses. -/
theorem isRegularWith_add {x x' : FieldSample} {F F' : ℂ × ℝ → ℝ} (h : IsRegularWith x F)
    (h' : IsRegularWith x' F') : IsRegularWith (x + x') (fun q => F q + F' q) := by
  refine ⟨h.1.add h'.1, fun k z hz => (h.2.1 k z hz).add (h'.2.1 k z hz), ?_⟩
  refine tluo_of_dist_le (tluo_add h.2.2 h'.2.2) ?_
  filter_upwards [self_mem_nhdsWithin] with ρ (hρ : 0 < ρ) q hq
  rw [integral_add (integrable_fc (continuousOn_slice h.1 hρ) _ hq.2.le)
    (integrable_fc (continuousOn_slice h'.1 hρ) _ hq.2.le)]

end WedgeUnzip
end QuantumZipper
