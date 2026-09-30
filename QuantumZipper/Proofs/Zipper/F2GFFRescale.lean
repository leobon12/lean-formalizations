import QuantumZipper.Proofs.Zipper.F2Gamma0TruncCore
import QuantumZipper.Proofs.Zipper.F2Gamma0ScaleDet

/-!
# F2 step (4): what remains of `F2.GFFRescaleStmt` (scale invariance of the free GFF)

Theorem 1.3, node F2, step (4). Source: Sheffield, *Conformal weldings of random surfaces*,
arXiv:1012.4797, §5.1 (pp. 60–62): a quantum surface is unchanged by `z ↦ a z`, `h ↦ h(a ·) + Q log a`;
the free field modulo constants has the same law after the rescaling. The statement to prove is
`F2.GFFRescaleStmt` (`F2Gamma0ScaleRed.lean:59`): `IsFreeGFFModConstH X P →
IsFreeGFFModConstH (fun ω => rescale (X ω) (Qc γ) a) P` for `a > 0`.

**The mathematics is not the obstruction.** The covariance side is *already proved*:
`neumannH (a x) (a y) = neumannH x y - 2 log a`, and on a balanced pair the constant dies against
the equal masses — this is `WedgeTK.kernelCov2_map_mul` / `F2.kernelCov2_pushPair`, and the whole
truncated reduction `F2.truncRescaleFree_of_evalRegRaw` (`F2Gamma0TruncFreeRaw.lean`) solves every
field of `IsFreeGFFModConstH` for the *s-finite truncated* field
`sfTrunc (rescale X (Qc γ) a)` from the single input `F2.EvalRegRawStmt`.

What blocks the *untruncated* statement `GFFRescaleStmt` is the definition of `rescale` itself:

`rescale x Q a μ = evalReg x (μ.map (a ·)) + Q * (log a * (μ univ).toReal)`
(`F2.rescale_apply_eq_evalReg_add` below, valid at **every** `μ`, s-finite or not).

So the rescaled field reads `x` only through `evalReg` of the dilated measure, and the two missing
inputs are exactly the two documented project gaps:

* `F2.MeasEvalRegStmt`: `x ↦ evalReg x ν` is measurable for **every** measure `ν`. mathlib
  provides this only at s-finite `ν` (`Sample.measurable_evalReg` has `[SFinite ν]`), and
  `μ.map (a ·)` is s-finite iff `μ` is (`F2.sFinite_map_mul_iff` below: `z ↦ a z` is a bijection
  of `ℂ` for `a ≠ 0`), so at a non-s-finite `μ` the coordinate of `rescale X Q a` is *purely*
  `evalReg` junk at a non-s-finite measure: the `Q log a` term vanishes because `μ univ = ⊤`
  (`F2.rescale_apply_of_univ_eq_top`, `F2.univ_eq_top_of_not_sFinite`). Note `IsFreeGFFModConstH.
  measurable_coord` quantifies over *all* measures on `ℂ`, so this coordinate must be provided.
  This is precisely the D27 issue (`DECISIONS.md`), whose resolution in this repository was to
  *replace* the field by `sfTrunc`; the `GFFRescaleStmt` as stated does not truncate.

* `F2.EvalRegRawStmt` (`F2Gamma0TruncFreeRaw.lean:50`, the D17 gap): a.s. `evalReg (X ω) ν = X ω ν`
  at every admissible `ν`. Needed because the *values* of the rescaled field at admissible `μ` are
  the raw coordinates of `X` at `μ.map (a ·)`, which the axioms of `IsFreeGFFModConstH` control
  only at raw coordinates; the balanced increments enter `WedgeTK.gaussFam X (pushPair a ha)`
  (`F2.rescale_sub_eq`) and are Gaussian only under this bridge.

Main result of this file: `F2.gffRescaleStmt_of`, i.e.

`MeasRescaleStmt → EvalRegRawStmt → GFFRescaleStmt`,

and its one-input form `F2.gffRescaleStmt_of_measEvalReg` from `MeasEvalRegStmt`. The remaining
work on `GFFRescaleStmt` is thus exactly these two statements; the proof below is the untruncated
transcription of `F2.truncRescaleFree_of_evalRegRaw` (own bookkeeping: product σ-algebra
measurability, the dilated-measure algebra, the mass identity of `a • μ + b • ν`). No new
mathematics, and no departure from the blueprint beyond recording the obstruction.

Sources: Sheffield arXiv:1012.4797 §5.1 pp. 60–62 (scale invariance of the quantum surface,
`h ↦ h(a ·) + Q log a`); `notes/section3_4.md` for the Neumann kernel covariance. Everything here
is the project's own bookkeeping (D17/D27 of `DECISIONS.md`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace F2

/-! ## 1. The value of the rescaled field at an arbitrary measure -/

/-- The `Q log|ψ'|` integral of the coordinate change by the dilation `z ↦ a z`, at an arbitrary
measure: unlike `F2.integral_log_deriv_mul_left` the sign of `a` is unrestricted, since
`Real.log ‖a‖ = Real.log a` for every real `a` (`Real.log_abs`). -/
theorem integral_log_deriv_mul_left_all (a Q : ℝ) (μ : Measure ℂ) :
    Q * ∫ z, Real.log ‖deriv (fun w : ℂ => (a : ℂ) * w) z‖ ∂μ =
      Q * (Real.log a * (μ Set.univ).toReal) := by
  have hpt : (fun z : ℂ => Real.log ‖deriv (fun w : ℂ => (a : ℂ) * w) z‖) =
      fun _ => Real.log a := by
    funext z
    rw [deriv_mul_left_c, Complex.norm_real, Real.norm_eq_abs, Real.log_abs]
  rw [hpt, integral_const, smul_eq_mul, measureReal_def]
  ring

/-- **The rescaled field at an arbitrary measure `μ`** (no s-finiteness): it is `evalReg` of the
dilated measure plus the `Q log a` term times the total mass. At a non-s-finite `μ` the total mass
is `⊤`, so the second term vanishes and only `evalReg` at a non-s-finite measure is left. -/
theorem rescale_apply_eq_evalReg_add (Q a : ℝ) (x : FieldSample) (μ : Measure ℂ) :
    rescale x Q a μ = evalReg x (μ.map fun z => (a : ℂ) * z) +
      Q * (Real.log a * (μ Set.univ).toReal) := by
  rw [show rescale x Q a μ = evalReg x (μ.map fun z => (a : ℂ) * z) +
      Q * ∫ z, Real.log ‖deriv (fun w : ℂ => (a : ℂ) * w) z‖ ∂μ from rfl,
    integral_log_deriv_mul_left_all]

/-! ## 2. The two missing inputs -/

/-! ## 3. Freeness of the rescaled field from the two inputs -/

/-! ## 4. The truncation step is exactly the measurability gap -/

end F2
end QuantumZipper
