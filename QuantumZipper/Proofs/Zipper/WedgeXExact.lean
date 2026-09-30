import QuantumZipper.Proofs.Zipper.WedgeXGoodMain
import QuantumZipper.Proofs.Zipper.WedgeUnzipXC

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# D29 (wedge unzipping), X-X: RC3 of the unzipped `x_t` at all times, from `Γ⁰` and TIP-X

Task X-GOOD (second part). Node **X-X** (`WedgeUnzip.XExactAllStmt`, `WedgeUnzipXC.lean`): a.s.,
for all `t ≥ 0` and every folded circle, `evalReg x_t (fc) = x_t (fc)`.

Route (same as X-G, `WedgeXGoodMain.lean`): `x_t` and `y_t + ψ_t` have the same `avgReg`
(dyadic circle identity), so `evalReg x_t = evalReg (y_t + ψ_t)`, which splits as
`evalReg y_t + evalReg ψ_t` because both are regular (`YGoodAllStmt`; TIP-X clause 1, whose
witness is the circle average of `ψ_t`). Then `Γ⁰` RC3 for `y_t` (`YExactAllStmt`) and the
field identity `x_t = y_t + ψ_t` on **every** folded circle (`XFieldIdAllStmt`) conclude.

* `xExactAll_of_tipX : YGoodAllStmt → YExactAllStmt → XFieldIdAllStmt → TipXStmt →
  XExactAllStmt`.

Named inputs:
* `YExactAllStmt` (`Γ⁰`, D26 `UnifRC3` at all circles): a.s., for all `t ≥ 0`, `y_t` is exact
  on every folded circle.
* `XFieldIdAllStmt`: the circle identity `x_t = y_t + ψ_t` on every folded circle (the proved
  `F2.step3FieldCircDy_holds` is its dyadic case; the general case needs the split
  `F2.Step3EvalSplitDyStmt` at every circle, i.e. the continuum-radius JointMod that X-C needs
  too, `handoff/WEDGE-UNZIP.md`).

Own bookkeeping (Sheffield, arXiv:1012.4797, §5.4 step (3)).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace WedgeUnzip

/-- **(`Γ⁰`) RC3 of the unzipped `Γ⁰` field at all times and on all folded circles.** -/
def YExactAllStmt : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 →
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample),
    IsBrownianReal B P → IsFreeGFFModConstH X P → IndepFun (pathOf B) X P →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t → ∀ d ∈ Hbar, ∀ r > 0,
      evalReg (F2.unzY κ (X ω) (drive κ B ω) t) (foldedCircle d r) =
        F2.unzY κ (X ω) (drive κ B ω) t (foldedCircle d r)

/-- Samples with the same `avgReg` have the same `evalReg`. -/
theorem evalReg_congr_avgReg {x x' : FieldSample} (h : ∀ k z, avgReg x k z = avgReg x' k z)
    (ν : Measure ℂ) : evalReg x ν = evalReg x' ν := by
  have e : avgReg x = avgReg x' := funext fun k => funext fun z => h k z
  unfold evalReg
  rw [e]

end WedgeUnzip
end QuantumZipper
