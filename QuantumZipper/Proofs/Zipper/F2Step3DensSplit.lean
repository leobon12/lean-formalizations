import QuantumZipper.Proofs.Zipper.F2Step3DensUnif
import QuantumZipper.Proofs.Zipper.RegContDet
import QuantumZipper.Proofs.Loewner.TwoPoint

/-!
# F2 step (3): the circle-level field identity from the regularization split

`Step3FieldCircStmt` (`F2Step3DensField.lean`) reduced to the split of the regularized evaluation
(`Step3EvalSplitStmt`): for `ν = f_t⁻¹_* fc(c, r)` (a folded circle near `[u,v] ⊂ (O⁻_t, O⁺_t)`),
`evalReg (x + γ log|·|) ν = evalReg x ν + ∫ γ log|·| dν`. This is the statement that the
regularization of the deterministic, locally bounded part `γ log|·|` converges to its integral and
that the regularization of `x` converges at `ν` (for a fixed deterministic `ν`, the analogue is
`CoordReg.ae_evalReg_h0rev_eq_frostman'`, RC1); here it is needed at all times at once.

The remaining bookkeeping is proved (`unzX_fc_eq_of_split`): by definition of `coordChange`,
`x_t(fc) = evalReg x ν + Q ∫ log|(f_t⁻¹)'| dfc` and likewise for `y_t`; `∫ γ log|·| dν =
∫ γ log|f_t⁻¹| dfc` (change of variables, `RegCont.aemeasurable_fwdMapInv`), and `f_t⁻¹ = E_t`
`fc`-a.e. since `fc(c,r)` charges only `ℍ` (`TwoPoint.foldedCircle_ae_mem_H`). Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace F2

/-- The coordinate-change bookkeeping at one folded circle. -/
theorem unzX_fc_eq_of_split {κ : ℝ} {x : FieldSample} {W : ℝ → ℝ} (hW : Continuous W)
    (hW0 : W 0 = 0) {t : ℝ} (ht : 0 ≤ t) {c : ℂ} {r : ℝ} (hr : 0 < r)
    (hsplit : evalReg (x + gammaLog κ) ((foldedCircle c r).map (fwdMapInv W t)) =
      evalReg x ((foldedCircle c r).map (fwdMapInv W t)) +
        ∫ z, Real.sqrt κ * Real.log ‖z‖ ∂(foldedCircle c r).map (fwdMapInv W t)) :
    unzippedField (Real.sqrt κ) (x, W) t (foldedCircle c r) =
      unzippedField (Real.sqrt κ) (x + gammaLog κ, W) t (foldedCircle c r) +
        ∫ z, -(Real.sqrt κ * Real.log ‖extInv W t z‖) ∂foldedCircle c r := by
  have hm : Measurable fun z : ℂ => Real.sqrt κ * Real.log ‖z‖ :=
    (Real.measurable_log.comp measurable_norm).const_mul _
  have hmap : ∫ z, Real.sqrt κ * Real.log ‖z‖ ∂(foldedCircle c r).map (fwdMapInv W t) =
      ∫ z, Real.sqrt κ * Real.log ‖extInv W t z‖ ∂foldedCircle c r := by
    rw [integral_map (RegCont.aemeasurable_fwdMapInv hW hW0 ht c hr) hm.aestronglyMeasurable]
    refine integral_congr_ae ?_
    filter_upwards [TwoPoint.foldedCircle_ae_mem_H c hr] with z hz
    simp only [extInv, show 0 < z.im from hz, ↓reduceIte]
  simp only [unzippedField, coordChange]
  rw [hsplit, hmap, integral_neg]
  ring

end F2
end QuantumZipper
