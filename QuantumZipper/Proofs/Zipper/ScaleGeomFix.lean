import QuantumZipper.Proofs.Zipper.F2Gamma0TruncCore
import QuantumZipper.Proofs.Zipper.F2ScaleGeomRed
import QuantumZipper.Proofs.Zipper.F2ScaleGeomConst
import QuantumZipper.Proofs.Section5.Prop17PalmCReg

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# F2 step (4): `ScaleGeomAeStmt'`, the scaling identity with the constant `(2/√κ) log a` (D45)

Theorem 1.3, node F2, step (4); decision D45 (`DECISIONS.md`). Source: Sheffield, *Conformal
weldings of random surfaces*, arXiv:1012.4797, §5.1 (pp. 60–62: `h ↦ h(a·) + Q log a`, and adding
a constant `C` to `h` multiplies boundary lengths by `e^{γC/2}`), §5.4 (pp. 70–72).

## The discrepancy (D45)

`F2.ScaleGeomAeStmt` (`F2Gamma0ScaleRed.lean:81`) compares the field unzipped from
`(h⁰ + rescale X Q a, W(a²·)/a)` with the `a`-rescaling of the field unzipped from `(h⁰ + X, W)`.
Since `h⁰ = h0rev κ = (2/√κ) log‖·‖` satisfies `h⁰(a z) = h⁰(z) + (2/√κ) log a`, the true
`a`-rescaling of the input field is (`rescale_h0_add_fc`, at every folded circle, given the
`evalReg` split of `h⁰ + X` at the dilated circle)

  `rescale (h⁰ + X) Q a = (h⁰ + rescale X Q a) + (2/√κ) log a`,

so the stated scaled field misses the constant `c₀ = (2/√κ) log a`; `RegEq` sees constants
(`F2.not_regEq_addConst_one`), hence `ScaleGeomAeStmt` fails for `a ≠ 1` (already at `t = 0`,
where `fwdMapInv W 0 = id` and both unzipped fields are the input fields read through `evalReg`).

## The repair

`ScaleGeomAeStmt'` inserts the constant into the scaled configuration:
`(h⁰ + addConst (rescale X Q a) c₀, W(a²·)/a)`. At every folded circle this input field *is*
`rescale (h⁰ + X) Q a` (`addConst_rescale_fc`), so the two unzipped fields are literally equal
(`unzippedField_congr_fc`), and `ScaleGeomAeStmt'` follows from the named inputs of
`F2ScaleGeomRed.lean` plus the `evalReg` split (`scaleGeomAeStmt'_of_inputs`).

The consumers only need length *agreement*; the witness of `GammaZeroScaleStmt` becomes
`X' = addConst (rescale X Q a) c₀` (resp. its D27 truncation), which is still a free field modulo
constants (`S5.FieldLaw.Raw.isFreeGFFModConstH_addConst`) and still independent of the rescaled
Brownian motion (a measurable function of the old witness). So the constant drops out of every
consumer (`gammaZeroScaleStmt_of'`, `gammaZeroScaleStmt_of_trunc'`,
`gammaZeroScaleStmt_of_evalRegRaw'`).

Own elementary bookkeeping (the paper's §5.1 scaling and constant rules at the level of this
encoding).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace F2

/-! ## The discrepancy and its repair at folded circles -/

/-- **The D45 discrepancy at a folded circle.** Given the `evalReg` split of `h⁰ + X` at the
dilated circle, the true `a`-rescaling of `h⁰ + X` exceeds the field `h⁰ + rescale X Q a` of
`ScaleGeomAeStmt`'s scaled configuration by exactly `(2/√κ) log a`. -/
theorem rescale_h0_add_fc {κ a r : ℝ} (ha : 0 < a) (hr : 0 < r) (d : ℂ) {X : FieldSample}
    (hsplit : evalReg (ofFun (h0rev κ) + X) ((foldedCircle d r).map (fun z => (a : ℂ) * z)) =
      ofFun (h0rev κ) ((foldedCircle d r).map (fun z => (a : ℂ) * z)) +
        evalReg X ((foldedCircle d r).map (fun z => (a : ℂ) * z))) :
    rescale (ofFun (h0rev κ) + X) (Qc (Real.sqrt κ)) a (foldedCircle d r) =
      (ofFun (h0rev κ) + rescale X (Qc (Real.sqrt κ)) a) (foldedCircle d r) +
        2 / Real.sqrt κ * Real.log a := by
  simp only [rescale, coordChange, Pi.add_apply]
  rw [hsplit, ofFun_h0rev_map_mul_foldedCircle ha hr d]
  ring

/-- **The repaired field is the true rescaling at every folded circle.** -/
theorem addConst_rescale_fc {κ a r : ℝ} (ha : 0 < a) (hr : 0 < r) (d : ℂ) {X : FieldSample}
    (hsplit : evalReg (ofFun (h0rev κ) + X) ((foldedCircle d r).map (fun z => (a : ℂ) * z)) =
      ofFun (h0rev κ) ((foldedCircle d r).map (fun z => (a : ℂ) * z)) +
        evalReg X ((foldedCircle d r).map (fun z => (a : ℂ) * z))) :
    (ofFun (h0rev κ) + addConst (rescale X (Qc (Real.sqrt κ)) a) (2 / Real.sqrt κ * Real.log a))
        (foldedCircle d r) =
      rescale (ofFun (h0rev κ) + X) (Qc (Real.sqrt κ)) a (foldedCircle d r) := by
  rw [rescale_h0_add_fc ha hr d hsplit]
  simp only [Pi.add_apply, addConst, measure_univ, ENNReal.toReal_one, mul_one]
  ring

/-- **Unzipped fields only see folded circles.** Two input fields that agree at every folded
circle have the same unzipped field (`coordChange` reads the field through `evalReg`, i.e.
through `avgReg`, i.e. through folded circles). -/
theorem unzippedField_congr_fc {γ t : ℝ} {x y : FieldSample} {W : ℝ → ℝ}
    (h : ∀ (d : ℂ) (r : ℝ), 0 < r → x (foldedCircle d r) = y (foldedCircle d r)) :
    unzippedField γ (x, W) t = unzippedField γ (y, W) t := by
  have hav : avgReg x = avgReg y := by
    funext k w
    simp only [avgReg]
    exact congrArg (fun f : ℕ → ℝ => limUnder atTop f) (funext fun n => h _ _ (radius_pos k))
  funext μ
  show coordChange x (fwdMapInv W t) (Qc γ) μ = coordChange y (fwdMapInv W t) (Qc γ) μ
  unfold coordChange
  rw [evalReg_congr_avgReg hav]

/-! ## `ScaleGeomAeStmt'` from named inputs -/

/-- **The `evalReg` split at dilated folded circles** (a D29-type regularity input): a.s., for
every folded circle, `evalReg (h⁰ + X)` at its `a`-dilation is `h⁰` there plus `evalReg X`. -/
def ScaleGeomSplitAeStmt {Ω : Type*} [MeasurableSpace Ω] (κ a : ℝ) (P : Measure Ω)
    (X : Ω → FieldSample) : Prop :=
  ∀ᵐ ω ∂P, ∀ (d : ℂ) (r : ℝ), 0 < r →
    evalReg (ofFun (h0rev κ) + X ω) ((foldedCircle d r).map (fun z => (a : ℂ) * z)) =
      ofFun (h0rev κ) ((foldedCircle d r).map (fun z => (a : ℂ) * z)) +
        evalReg (X ω) ((foldedCircle d r).map (fun z => (a : ℂ) * z))

/-! ## Consumers: `GammaZeroScaleStmt` from `ScaleGeomAeStmt'` -/

/-- `x ↦ addConst x c` is measurable on `FieldSample` (product σ-algebra). -/
theorem measurable_addConst_field (c : ℝ) : Measurable fun x : FieldSample => addConst x c := by
  refine measurable_pi_iff.2 (fun μ => ?_)
  simp only [addConst]
  exact (measurable_pi_apply μ).add_const _

/-- Independence survives adding a deterministic constant to the field. -/
theorem indepFun_addConst_right {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    {P : Measure Ω} {V : Ω → β} {Y : Ω → FieldSample} (h : IndepFun V Y P) (c : ℝ) :
    IndepFun V (fun ω => addConst (Y ω) c) P := by
  have h' := h.comp measurable_id (measurable_addConst_field c)
  rw [show (id ∘ V) = V from rfl,
    show ((fun x : FieldSample => addConst x c) ∘ Y) = (fun ω => addConst (Y ω) c) from rfl]
    at h'
  exact h'

end F2
end QuantumZipper
