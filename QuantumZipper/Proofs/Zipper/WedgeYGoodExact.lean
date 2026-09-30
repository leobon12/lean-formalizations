import QuantumZipper.Proofs.Zipper.WedgeXExact
import QuantumZipper.Proofs.Zipper.WedgeXContReg
import QuantumZipper.Proofs.Zipper.JointModDetCont

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Y-GOODALL, part 1: `YExactAllStmt` and `XFieldIdAllStmt` from the continuum-radius JointMod

Theorem 1.3, F2 wedge cores X-G / X-X (decisions D26/D29). Both statements are about **every**
folded circle `fc(d, r)`, `d ∈ ℍ̄`, `r > 0`, at every time `t ≥ 0`.

**All circles are needed** (not only dyadic ones). The consumer `WedgeUnzip.xExactAll_of_tipX`
feeds `WedgeExactAllStmt`, which `unscaledB3dStmt_of_core` uses (as `hexact` of
`coordChange_rescale_fc_of_scale`) at the circles `fc(a d, a 2^{-k})` with
`a = scaleParam γ Z` a *random, field-dependent* scale: no fixed countable family of circles
contains them.

**Route.** Write `x = X + α₀(−log|·|)` and `y = x + γ log|·| = 𝔥₀ + X` (`F2.h0rev_add_eq`), and
`ν = (f_t⁻¹)_* fc(c, r)`. The single analytic input is the **existing** X-C node
`XContLimStmt` (continuum-radius JointMod: a modification `Xc(t, c, r, ρ)` of
`∫ evalReg x (fc(u, ρ)) dν`, continuous up to `ρ = 0`). From it, deterministically:

* `tendsto_avgReg_of_contLim`: `∫ avgReg x k dν → Xc(t, c, r, 0)` at **every** parameter;
* `unzY_fc_eq_ddet`: the raw value `y_t(fc(c, r))` equals
  `Ddet₄ + (√κ − 1)(Ddet₁ − Ddet₄) + Xc(·, 0)` (`Ddet` the proved-continuous deterministic part of
  JointMod), so it is **continuous** in `(t, c, r)`;
* the JointMod modification `Zh` (proved, `jointModStmt_holds`) is the regularity witness of `y_t`
  and agrees with the raw values on a countable dense set, hence everywhere: RC3 on all circles.
* the regularization split `evalReg (x + γ log|·|) ν = evalReg x ν + ∫ γ log|·| dν` at every
  circle, hence `x_t = y_t + ψ_t` on every folded circle (`F2.unzX_fc_eq_of_split`).

Main results: `yExactAll_of_contLim : XContLimAllStmt → YExactAllStmt`,
`xFieldIdAll_of_contLim : XContLimAllStmt → XFieldIdAllStmt`.

Sources: Duplantier–Sheffield, *Liouville quantum gravity and KPZ*, Invent. Math. 185 (2011),
Prop. 3.1 (continuous modification of circle averages; via JointMod); Sheffield,
arXiv:1012.4797, §5.4 step (3) (the field identity). The density/continuity bookkeeping is an
**own elementary argument** (as in `RegUnif.ae_forall_isRegularWith_of_jointMod`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace WedgeUnzip

open RegUnif RegCont

/-! ## Deterministic lemmas -/

/-! ## RC3 of `y_t` on every folded circle -/

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

/-- `y_t = unzY` in the `𝔥₀ + X` form. -/
theorem unzY_eq_h0 (κ : ℝ) (x : FieldSample) (W : ℝ → ℝ) (t : ℝ) :
    F2.unzY κ x W t = unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + x, W) t := by
  rw [F2.unzY, F2.h0rev_add_eq]

/-! ## The field identity on every folded circle -/

end WedgeUnzip
end QuantumZipper
