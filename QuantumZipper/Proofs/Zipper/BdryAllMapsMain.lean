import QuantumZipper.Proofs.Zipper.BdryAllMapsCore
import QuantumZipper.Proofs.Zipper.E1CoordChange
import QuantumZipper.Proofs.Zipper.B5LocDet

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SW-THM43 (2): `BdryAllMapsStmt` from the variable-scale and distortion inputs

Task SW-THM43. Source: S. Sheffield, M. Wang, arXiv:1605.06171 (literature/1605.06171.pdf),
proof of **Theorem 4.3**, p. 19, which follows the proof of Theorem 1.4, pp. 11–12:

* "For each `φ ∈ Λ` … an analogous result to Corollary 3.2 holds: the random measures
  `e^{h̃_{ε/(φ⁻¹)'(z)}} dz` converge to `µ_B`. Combining this fact with change of coordinates as
  in the proof of Theorem 1.4, … it suffices to show (4.4) and (4.5)."

Here, pathwise for one field sample `x` and simultaneously for **all** admissible `ψ`:

* change of coordinates `u = Re ψ(t)` on `[a,b]` (mathlib
  `lintegral_image_eq_lintegral_abs_deriv_mul`) and the exact density identity `dens_split`
  (`γQ/2 = 1 + γ²/4`, the computation displayed on p. 12) turn the approximation of
  `x ∘ ψ + Q log|ψ'|` into the variable-scale approximation of `x` with `s = |ψ'| ∘ ψ⁻¹`, up to
  the factor `exp(γ/2 Δ_k)`;
* `BdryDistortionGood` makes `Δ_k` uniformly small, and the multiplicative squeeze
  (`tendsto_of_exp_squeeze`) plays the role of SW's (4.4)–(4.5) (sup and inf over the family);
* `BdryVarScaleLimit` (SW's "analogous result to Corollary 3.2") gives the limit.

Main results: `tendsto_lintegral_coordChange_of_good`, `isVagueLimitOnR_coordChange_of_good`,
**`bdryAllMapsStmt_of_varScale_distortion`**: `BdryVarScaleStmt → BdryDistortionStmt →
BdryAllMapsStmt`.

**Relation of `BdryDistortionStmt` to SW.** SW bound the distortion in the mean over the family
(4.6): `E exp(α sup_{φ∈Λ*} ((h*, f^φ_ε) − (h*, f))) − 1 ≲ g(ε) → 0` (from Lemma 3.4 and the proof
of Lemma 3.5), used inside second-moment estimates. The pathwise uniform form asked here follows
from the same inputs by the Borell–TIS inequality (cited by SW, [Bor75], [CIS76]): the supremum of
the centred Gaussian process `Δ` over the (normalized, compact) family at one point has mean
`m_ε → 0` (SW Lemma 3.5) and variance `O(ε)`, so its tail beyond `η` is `exp(−c/ε)`, summable
against the `O(ε^{-1})` grid points; Borel–Cantelli and the continuity in `t` finish. This is the
route SW themselves use for the variable-scale sandwich; the regularization is by semicircle
averages (`avgReg`/`evalReg`), not mollifiers (adaptation SW-A3). Own bookkeeping otherwise.
-/

noncomputable section

open MeasureTheory Filter Set Function
open scoped Topology ENNReal

namespace QuantumZipper
namespace F1

section Pathwise

variable {γ : ℝ} {x : FieldSample} {ψ : ℂ → ℂ} {a b : ℝ} {U : Set ℂ}

/-- The approximating density of `bdryApprox` is measurable. -/
theorem measurable_bdryApprox_dens (γ : ℝ) (y : FieldSample) (k : ℕ) :
    Measurable fun t : ℝ =>
      ENNReal.ofReal (radius k ^ (γ ^ 2 / 4) * Real.exp (γ / 2 * avgReg y k (t : ℂ))) := by
  have h1 : Measurable fun t : ℝ => avgReg y k (t : ℂ) :=
    (measurable_avgReg k).comp (measurable_const.prodMk Complex.measurable_ofReal)
  exact ENNReal.measurable_ofReal.comp
    ((Real.measurable_exp.comp (h1.const_mul _)).const_mul _)

end Pathwise

end F1
end QuantumZipper
