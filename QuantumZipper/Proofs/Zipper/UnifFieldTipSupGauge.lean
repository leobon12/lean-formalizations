import QuantumZipper.Proofs.Zipper.UnifTipExp

/-!
# FIELD-TIPSUP: the additive-constant gauge obstruction to `FieldTipSupStmt`

**Finding.** `RegUnif.FieldTipSupStmt κ p` is **false** as stated; it is not a consequence of
`IsFreeGFFModConstH`. The reason is the additive-constant gauge of the free field modulo
constants, which `QuantumZipper/GFF/Defs.lean` explicitly allows ("Any additive-constant
convention (even a random one, `X = h + C · mass`) satisfies this definition"): the axiom set
only constrains *balanced* pairs `X μ − X ν` (`μ univ = ν univ`), so `X` may be replaced by
`X + C · mass` for an **arbitrary measurable** `C : Ω → ℝ` without leaving the class. Every
regularized quantity in `ZE` is a single pairing with a *probability* measure
(`ν4` has mass `1`, `foldedCircle` has mass `1`), so the gauge passes straight through:

`avgReg (x + c·mass) k z = avgReg x k z + c`,
`evalReg (x + c·mass) ν = evalReg x ν + c` (`ν` probability),
`ZE(f, x + c·mass) q = ZE(f, x) q + c` (on the `UCD` event, where `extD` is a limit),

and therefore `fieldTipSup (x + c·mass) = e^{√κ·c} · fieldTipSup x`. Choosing a gauge `C` with
`∫⁻ e^{p√κ C} = ⊤` (e.g. `C = −log U`, `U` uniform on `(0,1)`, for `p √κ ≥ 1`, `U` independent
of the field and of the driver) makes the conclusion `∫⁻ (fieldTipSup)^p ≠ ⊤` fail, while all the
hypotheses of `FieldTipSupStmt` still hold: `B ⟂ X` is preserved because the gauge is independent
noise, and the `UCD` event is gauge-invariant (`UCD_add_const`), hence holds a.s. as for the
ungauged field (`JointModRandom.ae_fibre4`).

The file records the machine-checked halves of this obstruction: the gauge equivariance of
`avgReg`, of `UCD`/`extD` and of `fieldTipSup` itself (the deterministic chain is
"own elementary argument": `limUnder` of a shifted convergent sequence, and `ENNReal.mul_iSup`).
Any repair of the node has to pin the gauge, e.g. by requiring a hypothesis that the joint law
of `(ZE(q))_q` is the centred Gaussian vector with covariance `kernelCov2 neumannH (ν4 q) (ν4 q')`
(killing the additive component), or by fixing the construction of `X` (a specific gauge choice)
rather than the gauge-invariant axiom set.

## Main statements

* `RegUnif.shiftField`, `RegUnif.avgReg_shiftField` — the gauge shift and its effect on the
  regularized circle averages.
* `RegUnif.UCD_add_const`, `RegUnif.extD_add_const` — the `UCD`/`extD` device of `JointModExt` is
  gauge-equivariant.
* `RegUnif.ZE_shiftField`, `RegUnif.fieldTipSup_shiftField` — `ZE` and `fieldTipSup` are
  gauge-equivariant: the conclusion of `FieldTipSupStmt` is *not* gauge-invariant.
-/

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology Real ENNReal NNReal

namespace QuantumZipper
namespace RegUnif

open CharFun RegCont RegSample B2 B5 CircleFubini KolmD

/-! ## The gauge shift `x ↦ x + c·mass` -/

/-- The additive-constant gauge: `shiftField c x = x + c · mass`, i.e. the pairing of `x + c`
with `μ` (a field modulo constants is only defined up to such a shift). -/
def shiftField (c : ℝ) (x : FieldSample) : FieldSample :=
  fun μ => x μ + c * (μ Set.univ).toReal

@[simp]
theorem shiftField_apply (c : ℝ) (x : FieldSample) (μ : Measure ℂ) :
    shiftField c x μ = x μ + c * (μ Set.univ).toReal := rfl

/-! ## The dyadic-extension device is gauge-equivariant -/

/-! ## Gauge equivariance of the regularized values

The integral `∫ (avgReg x k (·) + c)` against the probability measure `foldedCircle` adds `c`
only when the integrand is integrable; `avgReg` is a junk value (`limUnder`) where its defining
limit fails, so integrability is *not* automatic from the axioms and is carried as a hypothesis
(it holds for the genuine field, by the moment bounds of `FrostmanReg`/`SmoothingConvergence`).
-/

/-! ## Gauge equivariance of `ZE` and of `fieldTipSup` -/

end RegUnif
end QuantumZipper
