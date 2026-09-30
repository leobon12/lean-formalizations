import QuantumZipper.Proofs.Zipper.AreaCoordCov
import QuantumZipper.Proofs.Zipper.WedgeUnzipScale
import QuantumZipper.Proofs.LQG.IndepParams

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# W-A-var (1): the variable-scale node in the original coordinates

Task W-A-var (Theorem 1.3, E6 area node). Target: `E6.WedgeAreaVarStmt` (`AreaCoordFix.lean`).

Source: S. Sheffield, M. Wang, *Field-measure correspondence in Liouville quantum gravity almost
surely commutes with all conformal maps simultaneously*, arXiv:1605.06171
(literature/1605.06171.pdf), Corollary 3.2, p. 11, used exactly as in the proof of Theorem 1.4,
p. 11–12 (there with `g = 1/|φ'|`).

The change of variables `w = ψ(z)` (`ψ = f̂_t = fwdMapInv W t`, Jacobian `‖ψ'‖²`, the same
computation as `integral_transTest_areaApprox`) turns the unzipped-coordinate integral
`∫_ℍ varDens · g` into the original-coordinate integral

  `∫_ℍ (2^{-k} s(w))^{γ²/2} e^{γ h_{2^{-k} s(w)}(w)} · transTest g (w) dw`,  `s(w) = |ψ'(f_t w)|`

(`integral_varDens_eq_varScaleDens`): an area approximation of the field `x₀` itself at the
**spatially varying** radius `2^{-k} s(w)`, with `s` continuous and positive on `ℍ \ K_t`. So
`WedgeAreaVarStmt` follows (`wedgeAreaVarStmt_of_varScale`) from the field-only node

* **`WedgeVarScaleStmt`** (SW Cor. 3.2 in circle-average, half-plane form, for the unscaled wedge
  field): a.s., for **every** open `U ⊆ ℍ`, every continuous `s : U → (0,∞)` and every
  continuous `φ` with compact support in `U`, the variable-scale approximations
  `∫ φ (ε s)^{γ²/2} e^{γ h_{ε s}}` and the fixed-scale approximations `∫ φ dμ_ε`, `ε = 2^{-k}`,
  merge.

The driver disappears: the node is a statement about the field alone, simultaneous over the
scale functions (so no Fubini/independence step over the driver is needed). SW state Cor. 3.2
for one fixed smooth `g`; their proof (sandwiching between the sup/inf window measures of the
proof of Thm 1.1, p. 9) is pathwise in `g` and gives all continuous `g` at once — see
`AreaVarSand.lean`. Own bookkeeping otherwise.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped Topology NNReal ENNReal

namespace QuantumZipper.E6

open D3Plus MeasUnzip

variable {W : ℝ → ℝ} {t : ℝ}

/-- The scale function `s(w) = ‖ψ'(f_t w)‖` in the original coordinates. -/
def unzipScale (W : ℝ → ℝ) (t : ℝ) (w : ℂ) : ℝ :=
  ‖deriv (fwdMapInv W t) (fwdMap W t w)‖

end QuantumZipper.E6
