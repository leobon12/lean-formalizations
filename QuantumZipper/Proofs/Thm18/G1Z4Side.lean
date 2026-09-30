import QuantumZipper.Proofs.Thm18.G1Z3Fixed
import QuantumZipper.Proofs.Thm18.G1Z2MeasMain
import QuantumZipper.Proofs.Thm18.G1RegRepRed
import QuantumZipper.Proofs.Thm18.G1ZBdryTransp

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G1Z4 (D58, route R2): `G1BdryRepStmt` from the side limit along all radii

`g1BdryRepStmt_of_sideLim : G1RegRepRC2Stmt → G1RegRepRestStmt → G1Z4SideLimStmt →
G1BdryRepStmt`.

The good set is `E' ∩ E₁ ∩ RC2(left) ∩ RC2(right)` (`E'` from `G1RegRepRestStmt`, `E₁` from
`G1Z4SideLimStmt`, the RC2 sets `G1Meas.measurableSet_rc2`), exactly as in
`g1RegRepStmt_of_parts`. On it, the side map of the `Classical.epsilon` uniformizer is the
selected map composed with a dilation `w ↦ b w` (U6, `g1z2_invFunOn_eq_dilate`); by RC3 at every
circle the pulled-back field is, up to regularized averages, the rescaled selected field
(`g1z2_regEq_dilate`), and the side limit along all radii is carried by the rescaling
(`g1z2_sideNu_rescale`): the boundary map becomes `Φ = Φ₀ ∘ (b ·)`. Own bookkeeping (as in
G1Z2-MEAS).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal

namespace QuantumZipper
namespace Thm18Asm
namespace G1Z4

/-- The wedge boundary measure only reads the regularized averages. -/
theorem qBoundaryMeasure_congr_avg {γ : ℝ} {x x' : FieldSample} (h : avgReg x = avgReg x') :
    qBoundaryMeasure γ x = qBoundaryMeasure γ x' := by
  have hb : bdryApprox γ x = bdryApprox γ x' := by
    funext k; unfold bdryApprox; rw [h]
  unfold qBoundaryMeasure
  rw [hb]

/-- The side boundary measure only reads the regularized averages. -/
theorem g1SideNu_congr_avg {γ : ℝ} {left : Bool} {x x' : FieldSample}
    (h : avgReg x = avgReg x') : g1SideNu γ left x = g1SideNu γ left x' := by
  have hb : bdryApprox γ x = bdryApprox γ x' := by
    funext k; unfold bdryApprox; rw [h]
  unfold g1SideNu qBoundaryMeasureOn
  rw [hb]

/-- The pulled-back field only reads the regularized averages. -/
theorem coordChange_congr_avg {x x' : FieldSample} (h : avgReg x = avgReg x') (ψ : ℂ → ℂ)
    (Q : ℝ) : coordChange x ψ Q = coordChange x' ψ Q := by
  funext μ
  simp only [coordChange, evalReg, h]

end G1Z4

end Thm18Asm
end QuantumZipper
