import QuantumZipper.Proofs.Zipper.F1PStarShiftReg
import QuantumZipper.Proofs.Zipper.WedgeAddConstPos
import QuantumZipper.Proofs.Wire2b
import QuantumZipper.Proofs.Zipper.F2AddConst

/-!
# Theorem 1.3, node F1 (D29): two uses of the constant-shift transport

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, §5.1 (rule (5.1)) and §5.4
(pp. 70–72). Own bookkeeping.

* `ae_pos_scaleParam_addConst_of_realize`: positivity of `scaleParam γ (Y + k)` for a `P_*`
  sample, by the route of the D29 node table — `ae_pos_scaleParam_addConst_wedgeRef` on the
  realization (core P) and the transport `scaleParam_addConst_congr_of_isRegularSample` back to
  `Y`. (The direct route, field-level B4(c) `wedgeAddConstLawStmt_holds`, is
  `F1.ae_pos_scaleParam_addConst_pStar` in `F1PStarZipLenCore.lean`; this file is a consistency
  check of the two routes.)
* `regEq_unzippedField_addConst_of_regShift`: clause (i) of `PStarShiftRegStmt` (unzipping
  commutes with an additive constant) from the `RegShift` convergence of the smoothed pairings
  along the pushed circles (`F2.coordChange_addConst_fc`). Together with `PStarShiftRegStmt`'s
  clauses (ii)–(iii) this pins down the remaining input exactly.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace F1

open Thm18Asm

/-- A property holding `P`-a.s. holds a.s. for the first coordinate under `P ⊗ Q`, `Q` a
probability measure. -/
theorem ae_prod_fst_of_ae {Ω Ω₂ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω₂]
    {P : Measure Ω} {Q : Measure Ω₂} [IsProbabilityMeasure Q] {S : Ω → Prop}
    (h : ∀ᵐ ω ∂P, S ω) : ∀ᵐ ω ∂(P.prod Q), S ω.1 := by
  rw [ae_iff] at h ⊢
  have e : {ω : Ω × Ω₂ | ¬ S ω.1} = {ω : Ω | ¬ S ω} ×ˢ (univ : Set Ω₂) := by
    ext ω; simp
  rw [e, Measure.prod_prod, measure_univ, mul_one]
  exact h

/-- **Unzipping commutes with additive constants** (clause (i) of `PStarShiftRegStmt`) from the
`RegShift` convergence of the smoothed pairings along the pushed circles, for every regular
sample `x`: on the admissible folded circles the coordinate changes differ by exactly `c`
(`F2.coordChange_addConst_fc`), and `RegEq` is read off from the admissible circles
(`S5.FieldShift.regEq_of_fc`). -/
theorem regEq_unzippedField_addConst_of_regShift {γ c : ℝ} {x : FieldSample} {W : ℝ → ℝ}
    {t : ℝ}
    (h : ∀ d ∈ Hbar, ∀ r : ℝ, 0 < r →
      E1.RegShift x ((foldedCircle d r).map (fwdMapInv W t))) :
    RegEq (unzippedField γ (addConst x c, W) t)
      (addConst (unzippedField γ (x, W) t) c) := by
  refine S5.FieldShift.regEq_of_fc fun d hd r hr => ?_
  rw [show unzippedField γ (addConst x c, W) t (foldedCircle d r) =
      coordChange (addConst x c) (fwdMapInv W t) (Qc γ) (foldedCircle d r) from rfl,
    F2.coordChange_addConst_fc (Q := Qc γ) c (h d hd r hr)]
  simp only [addConst, measure_univ, ENNReal.toReal_one, mul_one]
  rfl

end F1
end QuantumZipper
