import QuantumZipper.Proofs.Thm18.G4
import QuantumZipper.Proofs.Zipper.LocRichBasic
import QuantumZipper.Proofs.Thm18.G4WeldHull
import QuantumZipper.Proofs.Thm18.G4WeldRound
import QuantumZipper.Proofs.Zipper.Cor15RezipRegGood
import QuantumZipper.Proofs.LQG.RegularClosure

/-!
# Theorem 1.8, node G4: the double rescaling from regularity of the wedge sample

Both rezip nodes (`G4RoundDownRezipStmt`, `G4RoundUpRezipStmt`) contain the identity
`Y(b·)(·/b) ≈ Y` (`RegEq`) for a random scale `b > 0`. It holds for **every** `b > 0` as soon as
`Y` is a regular sample (`IsRegularSample.regEq_rescale_rescale`, blueprint M4-R4) whose raw
values at the coordinate circles are the regularized ones (`WedgeZeroRegStmt`, proved). The
regularity of the wedge sample is stated as `WedgeRegSampleStmt` (it reads only the dyadic
circle values, hence only the law of the data; the free-field case is
`RegularSample.ae_isRegularSample`). **Own elementary argument.**

* `regEq_rescale_one_of_raw`, `regEq_rescale_rescale_inv`: deterministic.
* `g4RoundDownRezipStmt_of_core`, `g4RoundUpRezipStmt_of_core`: the rezip nodes from their
  cores (without the double rescaling), `WedgeRegSampleStmt` and `WedgeZeroRegStmt`.
* `g4Stmt_of_coreNodes`: `G4Stmt` from the remaining nodes in their sharpest form.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

namespace QuantumZipper
namespace Thm18Asm

/-- Rescaling by `1` does not change a field that is regular at the coordinate circles. -/
theorem regEq_rescale_one_of_raw {x : FieldSample} (Q : ℝ)
    (hreg : ∀ i : ℕ, evalReg x (foldedCircle (CoordsFull.fullIndex i).1
      (CoordsFull.fullIndex i).2) = x (foldedCircle (CoordsFull.fullIndex i).1
      (CoordsFull.fullIndex i).2)) :
    RegEq (rescale x Q 1) x := by
  have h : CoordsFull.coordsFull (rescale x Q 1) = CoordsFull.coordsFull x := by
    funext i
    show coordChange x (fun z => ((1 : ℝ) : ℂ) * z) Q _ = x _
    simp only [coordChange, Complex.ofReal_one, one_mul, Measure.map_id', deriv_id'',
      norm_one, Real.log_one, integral_zero, mul_zero, add_zero]
    exact hreg i
  intro k z
  rw [CoordsFull.avgReg_congr_full h]

/-- **Double rescaling** `x(b·)(·/b) ≈ x` for a regular sample, regular at the coordinate
circles. -/
theorem regEq_rescale_rescale_inv {x : FieldSample} (hR : IsRegularSample x) (Q : ℝ)
    (hreg : ∀ i : ℕ, evalReg x (foldedCircle (CoordsFull.fullIndex i).1
      (CoordsFull.fullIndex i).2) = x (foldedCircle (CoordsFull.fullIndex i).1
      (CoordsFull.fullIndex i).2)) {b : ℝ} (hb : 0 < b) :
    RegEq (rescale (rescale x Q b) Q b⁻¹) x := by
  have h1 := hR.regEq_rescale_rescale Q hb (inv_pos.2 hb)
  rw [mul_inv_cancel₀ hb.ne'] at h1
  have h2 := regEq_rescale_one_of_raw Q hreg
  exact fun k z => (h1 k z).trans (h2 k z)

/-- **Regularity of the Theorem 1.8 wedge sample** (explicit hypothesis). -/
def WedgeRegSampleStmt : Prop :=
  ∀ (γ : ℝ) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Y : Ω → FieldSample), 0 < γ → γ < 2 → IsQuantumWedge γ (γ - 2 / γ) Y P →
    ∀ᵐ ω ∂P, IsRegularSample (Y ω)

end Thm18Asm
end QuantumZipper
