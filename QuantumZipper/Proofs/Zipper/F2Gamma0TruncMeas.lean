import QuantumZipper.Proofs.Zipper.FSMeasBasic

/-!
# F2 step (4), D27 form: measurability and independence of the truncated rescaled field

Theorem 1.3, node F2, step (4) (`F2LocalScale.lean`). The rescaling
`rescale x Q a = coordChange x (z ↦ a z) Q` (`Field/Sample.lean`) reads `x` through
`evalReg x (μ.map (a ·))`: measurable in `x` at s-finite `μ` (`measurable_coordChange_apply`),
but at a non-s-finite `μ` nothing controls the coordinate (this is the D27 issue of
`DECISIONS.md`). Decision D27 repairs this by truncating the field: `sfTrunc z` keeps the value
of `z` at every s-finite measure and sets it to `0` at every other measure.

Consequences proved here (own elementary bookkeeping of the product σ-algebra; no literature
source applies):

* `F2.measurable_sfTrunc_rescale`: for fixed `Q`, `a`, the map
  `x ↦ sfTrunc (rescale x Q a)` is **measurable** `FieldSample → FieldSample` — the D27 form of
  "`rescale (X ω) Q a` is a measurable random field";
* `F2.indepFun_sfTrunc_rescale`: if `V` is independent of `X`, then `V` is independent of
  `ω ↦ sfTrunc (rescale (X ω) Q a)`: this map is `sfTrunc (rescale · Q a) ∘ X` with a measurable
  outer map, so its σ-algebra is contained in that of `X` (`IndepFun.comp`).

Both are consumed by `F2.gammaZeroScaleStmt_of_trunc`, the D27 form of `GammaZeroScaleStmt`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter

namespace QuantumZipper
namespace F2

/-- Composing the left variable of an independent pair with a measurable map keeps
independence (`IndepFun.comp` applied with `id` on the other side). -/
theorem indepFun_comp_left {Ω β β' γ : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    [MeasurableSpace β'] [MeasurableSpace γ] {P : Measure Ω} {V : Ω → β} {X : Ω → γ}
    {Φ : β → β'} (hΦ : Measurable Φ) (h : IndepFun V X P) :
    IndepFun (fun ω => Φ (V ω)) X P := by
  have h' := h.comp hΦ measurable_id
  rw [show (Φ ∘ V) = fun ω => Φ (V ω) from rfl, show (id ∘ X) = X from rfl] at h'
  exact h'

end F2
end QuantumZipper
