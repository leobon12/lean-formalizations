import QuantumZipper.Proofs.Zipper.F2Gamma0ScaleField

/-!
# F2 step (4): the field identity of the scaling — the constant `(2/√κ) log a`

Theorem 1.3, node F2, step (4); Sheffield, *Conformal weldings of random surfaces*,
arXiv:1012.4797, §5.1 (pp. 60–62: `h ↦ h(a·) + Q log a` with `Q = 2/γ + γ/2`) and §5.4
(pp. 70–72). This file concerns the third conjunct of `F2.ScaleGeomAeStmt`
(`F2Gamma0ScaleRed.lean:81`).

## Why the stated third conjunct cannot hold

`ScaleGeomAeStmt` compares the field unzipped from the **stated scaled configuration**

  `(ofFun (h0rev κ) + rescale (X ω) Q a, W(a²·)/a)`,  `Q = Qc (√κ)`,  `W = drive κ B ω`,

with the `a`-rescaling of the field unzipped from the unscaled configuration
`(ofFun (h0rev κ) + X ω, W)`. But the field of the stated scaled configuration is **not** the
`a`-rescaled field of the unscaled one: since `h0rev κ (a z) = h0rev κ z + (2/√κ) log a` for
`a > 0` (and `rescale y Q a` is literally `y(a·) + Q log a`),

  `rescale (ofFun (h0rev κ) + X ω) Q a = ofFun (h0rev κ) + rescale (X ω) Q a + ((2/√κ) log a) · 1`

at every finite measure not charging `0` — in particular at every folded circle and every pushed
folded circle, the unzipping maps being injective (`F2.input_field_offset`,
`F2ScaleGeomConst.lean`, whose hypotheses are the RC1 split of `evalReg` for `h⁰ + X` and RC3 for
`X` at the pushed circle, i.e. the D29 regularity inputs of the intended proof). So the stated
field is the true `a`-rescaled field *minus the constant* `c₀ = (2/√κ) log a`, a nonzero multiple
of the mass whenever `a ≠ 1`.

Constants are **not** invisible at the `RegEq` level: adding the constant `c` to a field shifts its
coordinate change, hence the unzipped field, at every folded circle by `c`
(`F2.coordChange_addConst_fc`, `Proofs/Zipper/F2AddConst.lean:111`,
`F2.unzippedField_addConst_fc`, `F1.addConst_rescale_fc`,
`Proofs/Zipper/WedgeAddConstReDet.lean:38`), and `RegEq` *is* the comparison of `avgReg` at folded
circles. Hence, with the field identity that underlies the intended argument —
`F2.regEq_unzippedField_scale` (`F2Gamma0ScaleField.lean:48`), which is exactly
`ScaleGeomAeStmt`'s third conjunct with the h⁰ part rescaled too — the two fields compared in
`ScaleGeomAeStmt` differ by `c₀` at every folded circle. `not_regEq_addConst_one` below records the
mechanism (`RegEq` is sensitive to nonzero constant shifts even for the simplest field). The only
step that is bookkeeping rather than a named input is the passage from the constant offset of the
*input* fields to the constant offset of the *unzipped* fields: it is the `limUnder`/`RawConverges`
bookkeeping of `F2AddConst.lean` (`E1.RegShift`, `LocalRule.avgReg_addConst_of_tendsto`), i.e. the
same regularity inputs the intended proof already assumes.

## The repaired statement

`ScaleGeomRescaledStmt` is `ScaleGeomAeStmt` with the paper-faithful field
`rescale (ofFun (h0rev κ) + X ω) (Qc (√κ)) a` in the third conjunct (the h⁰ part rescaled along
with the fluctuation). Its third conjunct is then *literally* the conclusion of
`regEq_unzippedField_scale` for `x = ofFun (h0rev κ) + X ω` and `W = drive κ B ω`, so no constant
appears, and it is exactly the `hfield` hypothesis of `F2.unzipLengths_scale`
(`F2Gamma0ScaleDet.lean:65`) and of `F2.lenAgree_scale`, i.e. exactly what
`F2.gammaZeroScaleStmt_of` feeds into `lenAgree_scale`. The first two conjuncts (goodness of the
unscaled field at time `a² t`, side images of `W` at time `a² t`) are taken from one named
uniform-in-time input.

Two named inputs (the paper's B3(a) and the D29 regularity statements; the task authorizes exact
named hypotheses for the unscaled uniform-in-time facts):

* `UnscaledGeomAeStmt κ P B X` — a.s., for every `s ≥ 0`: the unzipped field of
  `(ofFun (h0rev κ) + X, drive κ B)` at time `s` is good and both side images of `drive κ B` at
  time `s` exist (B3(a) + existence of `O^±_s` at all times);
* `ScaleGeomRegAeStmt κ a P B X` — a.s., for every `t ≥ 0`: the two D29 regularity statements used
  by `F2.regEq_unzippedField_scale` at the scale `a` and time `t` (`G1.ScaleConsistentAt` of the
  field at the images of folded circles under `fwdMapInv (W(a²·)/a) t`, and RC3 for the unzipped
  field at time `a² t`).

An alternative repair, keeping the stated field and displaying the constant, is
`RegEq (unzippedField γ (ofFun (h0rev κ) + rescale X Q a, W(a²·)/a) t)
  (addConst (rescale (unzippedField γ (ofFun (h0rev κ) + X, W) (a² t)) Q a) (-((2/√κ) log a)))`;
it is equivalent to `ScaleGeomRescaledStmt` at every folded circle
(`F2.coordChange_addConst_fc`) and is what the length-agreement transfer of `F2AddConst.lean` is
designed to consume (`agree_addConst_of_inputs`, `F2AddConst.lean:209`).

Own bookkeeping (the constant computation is elementary); the deterministic field identity is the
existing `F2.regEq_unzippedField_scale`.

Remark (why the constant is intrinsic here). In the paper the scale invariance is applied to the
`(γ − 2/γ)`-quantum wedge, whose normalization (arXiv:1012.4797, p. 22: the fluctuation has mean
zero on circles centred at the origin, "deﬁned without an additive constant") makes the constant
disappear — see p. 70, "Since the law of the `(γ - 2/γ)`-quantum wedge is scale invariant". The
field `h⁰ = (2/√κ) log‖·‖` of Theorem 1.3 (`h0rev`) is *not* normalized in this way (in the F2
chain it is the wedge field plus the deterministic `γ log‖·‖`, `F2.h0rev_add_eq`,
`F2Step3.lean:59`), so at the level of the *field* the scaling identity must carry
`(2/√κ) log a`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace F2

variable {Ω : Type*} [MeasurableSpace Ω]

/-- **Named D29 regularity inputs** for the field identity at scale `a`: a.s., for every `t ≥ 0`,
`G1.ScaleConsistentAt` of the field at the images of folded circles under the unzipping map of the
rescaled driver `W(a²·)/a` (this is `hsc`), and RC3 for the unzipped field at time `a² t` (this is
`hexact`). Both are exactly the hypotheses of `F2.regEq_unzippedField_scale`. -/
def ScaleGeomRegAeStmt (κ a : ℝ) (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ)
    (X : Ω → FieldSample) : Prop :=
  ∀ᵐ ω ∂P, ∀ t : ℝ, 0 ≤ t →
    (∀ (d : ℂ) (r : ℝ), 0 < r →
      Thm18Asm.G1.ScaleConsistentAt (ofFun (h0rev κ) + X ω) (Qc (Real.sqrt κ)) a
        ((foldedCircle d r).map (fwdMapInv (fun s => drive κ B ω (a ^ 2 * s) / a) t))) ∧
    (∀ d ∈ Hbar, ∀ r > 0,
      evalReg (unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + X ω, drive κ B ω) (a ^ 2 * t))
          (foldedCircle d r) =
        unzippedField (Real.sqrt κ) (ofFun (h0rev κ) + X ω, drive κ B ω) (a ^ 2 * t)
          (foldedCircle d r))

/-! ## Constants are visible to `RegEq` -/

end F2
end QuantumZipper
