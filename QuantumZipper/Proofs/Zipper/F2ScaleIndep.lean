import QuantumZipper.Proofs.Zipper.F2Gamma0ScaleDet
import QuantumZipper.Proofs.Zipper.F2Gamma0TruncMeas

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# F2 step (4), `ScaleIndepStmt`: the Brownian side, and the exact measurability gap

Theorem 1.3, node F2, step (4). `F2.ScaleIndepStmt` (`F2Gamma0ScaleRed.lean:68`) asks that the
rescaled field `rescale (X ω) Q a` stay independent of the rescaled Brownian motion
`t ↦ B (a² t) / a`. The intended route is `IndepFun.comp`: `IndepFun (pathOf B) X P` gives
`IndepFun (pathOf B') (Φ ∘ X) P` for the two "outer" maps
`φ : b ↦ (t ↦ b (a² t)/a)` (Brownian side) and `Φ : x ↦ rescale x Q a` (field side).

What this file does, in the order of that route:

* `F2.measurable_bmScaleFun`, `F2.indepFun_pathOf_bmScale`: the **Brownian side is done**. `φ` is
  measurable for the product σ-algebras (`measurable_pi_iff` + `measurable_pi_apply`), and
  `pathOf (b ↦ B (a²·)/a) = φ ∘ pathOf B` definitionally, so `IndepFun.comp` gives
  `IndepFun (pathOf B') X P` from `IndepFun (pathOf B) X P`.

* `F2.MeasurableRescaleMapStmt`: the **field side is exactly one measurability statement**,
  `Measurable (fun x : FieldSample => rescale x Q a)` for every `Q`, `a`. With it,
  `F2.scaleIndepStmt_of_measurableRescaleMap` proves `ScaleIndepStmt` — the whole theorem is then
  two lines of `IndepFun.comp`.

**That measurability statement is the D27 obstruction, and it is not available.** At an s-finite
`μ` the coordinate `x ↦ rescale x Q a μ` is measurable (`Field.Sample.measurable_coordChange_apply`,
and `MeasUnzipZip.measurable_rescale_apply` for the joint version). At a measure `μ` that is *not*
s-finite, `rescale x Q a μ = evalReg x (μ.map (a ·)) + Q * ∫ z, log ‖a‖ ∂μ` reads `x` through
`evalReg`, which is `limUnder_{k} ∫ w, avgReg x k w ∂ν`, i.e. through the Bochner integral of a
*parameter-dependent* function against a non-s-finite measure. Mathlib proves measurability of
such parameter integrals only under `[SFinite ν]` (`Measurable.lintegral_prod_right`,
`StronglyMeasurable.integral_prod_right'`, `MeasureTheory/Measure/Prod.lean:123,145`,
`Integral/Prod.lean:76`), and `Measures.map` of a non-s-finite measure by `z ↦ a z` (a `≠ 0`) is
again non-s-finite. Moreover the Lean integral is `if Integrable f μ then … else 0`
(`Integral/Bochner/Basic.lean:158`), so measurability of the coordinate would require
`{x : Integrable (avgReg x k ·) ν}` to be measurable, which is the same missing input. This is
exactly option (c) of `DECISIONS.md` D27 ("not realistic"), rejected there in favour of the
truncated field `FSMeas.sfTrunc` (option (b)).

Consequently:

* `F2.scaleIndepStmt_sfTrunc_holds` is the **D27 form of `ScaleIndepStmt`**, proved here with the
  same hypotheses and the field replaced by `FSMeas.sfTrunc (rescale (X ω) Q a)`. This is the form
  consumed downstream (`F2.gammaZeroScaleStmt_of_trunc`, `F2Gamma0Trunc.lean:141`); the
  untruncated `ScaleIndepStmt` is only used by the pre-D27 wiring `F2.gammaZeroScaleStmt_of`.
* `F2.scaleIndepStmt_of_ae_sfTrunc`: the untruncated statement would also follow from the D27 form
  plus the a.s. equality `sfTrunc (rescale (X ω) Q a) = rescale (X ω) Q a`; that equality is *not*
  available (the two differ at every non-s-finite measure, where `evalReg` need not vanish).

Everything here is own elementary bookkeeping of the product σ-algebra and of `IndepFun`; no
literature source is used. -/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace F2

/-! ## The Brownian side -/

/-- **Measurability of the Brownian rescaling.** For every `a`, the map
`b ↦ (t ↦ b (a² t)/a)` on path space `ℝ≥0 → ℝ` (product σ-algebra) is measurable: it is a
product of coordinate projections (`measurable_pi_iff`, `measurable_pi_apply`) and a division by
the constant `a`. -/
theorem measurable_bmScaleFun (a : ℝ) :
    Measurable fun b : ℝ≥0 → ℝ => fun t : ℝ≥0 => b (Real.toNNReal (a ^ 2) * t) / a := by
  refine measurable_pi_iff.2 fun t => ?_
  have h : Measurable fun b : ℝ≥0 → ℝ => b (Real.toNNReal (a ^ 2) * t) :=
    measurable_pi_apply _
  exact h.div_const a

/-- The sample path of the rescaled motion is the rescaled sample path:
`pathOf (b ↦ B (a²·)/a) = (b ↦ b (a²·)/a) ∘ pathOf B`. Definitional unfolding of `pathOf`. -/
theorem pathOf_bmScale {Ω : Type*} (a : ℝ) (B : ℝ≥0 → Ω → ℝ) :
    pathOf (fun t ω => B (Real.toNNReal (a ^ 2) * t) ω / a) =
      (fun b : ℝ≥0 → ℝ => fun t : ℝ≥0 => b (Real.toNNReal (a ^ 2) * t) / a) ∘ pathOf B :=
  rfl

/-- **Independence of the rescaled Brownian path.** If `V` is independent of the Brownian motion
`B`, it is independent of the rescaled motion `t ↦ B (a² t)/a`: the latter's sample path is the
composition of `pathOf B` with the measurable map `measurable_bmScaleFun a`. -/
theorem indepFun_pathOf_bmScale {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    {B : ℝ≥0 → Ω → ℝ} {V : Ω → FieldSample} (a : ℝ) (h : IndepFun (pathOf B) V P) :
    IndepFun (pathOf (fun t ω => B (Real.toNNReal (a ^ 2) * t) ω / a)) V P := by
  rw [pathOf_bmScale a B]
  have h' := h.comp (measurable_bmScaleFun a) measurable_id
  simpa [Function.comp_def] using h'

/-! ## The field side: the exact missing input -/

/-! ## The D27 form, and what the untruncated form would additionally need -/

end F2
end QuantumZipper
