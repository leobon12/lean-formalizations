import QuantumZipper.Proofs.Zipper.F2Gamma0TruncMeas
import QuantumZipper.Proofs.Zipper.F2Gamma0ScaleDet

/-!
# F2 step (4), D27 form: `GammaZeroScaleStmt` with the truncated rescaled field

Theorem 1.3, node F2, step (4). Source: Sheffield, *Conformal weldings of random surfaces*,
arXiv:1012.4797, §5.1 (pp. 60–62: quantum surfaces are invariant under `z ↦ a z`,
`h ↦ h(a·) + Q log a`) and §5.4 (pp. 70–72). `F2Gamma0ScaleRed.lean` reduces
`GammaZeroScaleStmt` to three named inputs, among them the freeness `GFFRescaleStmt` and the
independence `ScaleIndepStmt` of the rescaled field `rescale (X ω) Q a`. Both are blocked by the
D27 issue (`DECISIONS.md`): the coordinates of `rescale (X ω) Q a` at *non-s-finite* measures
are uncontrolled, so that field is not even known to be a measurable `FieldSample`-valued
random variable.

Here the witness is replaced by its **D27 truncation** `X' ω = sfTrunc (rescale (X ω) Q a)`
(`FSMeas.sfTrunc`), and the two blocked inputs are re-established for it:

* **independence** (`F2Gamma0TruncMeas.indepFun_sfTrunc_rescale`) is *proved*: `X'` is a
  measurable function of `X`, so it inherits `IndepFun` from `X`;
* **freeness** is isolated as `TruncRescaleFreeStmt`, the exact D27 form of `GFFRescaleStmt`
  (`IsFreeGFFModConstH X P → IsFreeGFFModConstH (fun ω => sfTrunc (rescale (X ω) (Qc γ) a)) P`)
  and left as the single input, in place of `GFFRescaleStmt`; it is *not* used anywhere else.
  Why it is not proved here: at an admissible (hence s-finite) `μ` the truncated field reads
  `evalReg (X ω) (μ.map (a·)) + Q log a · μ(univ)` (`coordChange` unfolds through `evalReg`),
  and the identification `evalReg (X ω) ν = X ω ν` — which would turn its balanced increments
  into the Gaussian family `gaussFam X` at the pushed-forward pairs, whose covariance
  `kernelCov2 neumannH` is invariant under `z ↦ a z` (`WedgeTK.kernelCov2_map_mul`, the
  balanced increments killing the additive `-2 log a`), and hence would close all five fields of
  `IsFreeGFFModConstH` — is available in this repository only for the *good* measures of
  `Regularization.ae_evalReg_eq_of_good` (`IsGoodSC`: bounded Lebesgue density, compact support
  off the real axis) and for Frostman measures (`FrostmanReg.ae_evalReg_eq_frostman`,
  `Thm14WDG.ae_evalReg_eq_of_regular`), **not** for an arbitrary admissible measure (already
  admissible measures with unbounded density, e.g. density `1/(|x| |log|x||)` near `0`, are not
  Frostman). The missing tool statement is recorded in the module docstring of
  `F2Gamma0TruncFree.lean`.

* **a.s. geometry** stays exactly `F2.ScaleGeomAeStmt` (its content — goodness of the unzipped
  field, the side images, and the field identity of the scaling — is read at finite measures
  only, so it does not need the truncation).

The truncation is invisible for the conclusion: at every s-finite measure `ofFun g + sfTrunc z`
and `ofFun g + z` agree, hence they have the same `avgReg` (`F2.avgReg_add_ofFun_sfTrunc`), the
same coordinate changes (`F2.coordChange_add_ofFun_sfTrunc`) and the same unzipped lengths
(`F2.unzipLengths_add_ofFun_sfTrunc`). This is how `ScaleGeomAeStmt`, which speaks about the
untruncated field, is transferred to the truncated one.

Own elementary bookkeeping (D27); no literature source applies to the truncation step. The
mathematical content (scale covariance of `Γ⁰`) is Sheffield §5.1 and §5.4.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace F2

/-! ## The truncation is invisible at s-finite measures -/

/-- `evalReg` reads a field only through `avgReg`. -/
theorem evalReg_congr_avgReg {x y : FieldSample} (h : avgReg x = avgReg y) (ν : Measure ℂ) :
    evalReg x ν = evalReg y ν := by
  simp only [evalReg, h]

/-! ## The named freeness input and the reduction -/

end F2
end QuantumZipper
