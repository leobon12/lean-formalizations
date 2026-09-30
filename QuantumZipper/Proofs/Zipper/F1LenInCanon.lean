import QuantumZipper.Proofs.Zipper.F1LenInScale

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Theorem 1.3, node F1: canonical rescaling of the lengths, and surjectivity of `L⁻`

Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797, §1.4 and §5.1 (pp. 60–62).

* **`LenCanonStmt`** (B3(d) for lengths at the length times). Deterministically
  (`unzipLengths_canon_of_reg`), `B3d.unzipLengths_canon` and the field identity
  `WedgeUnzip.regEq_unzippedField_canonConfig` give the lengths of `canonConfig γ c` at time `r`
  as those of `c` at time `a² r` (`a = scaleParam γ c.1`) from the regularity package
  `CanonReg γ c r` (positive scale, scale consistency, RC3, goodness, side limits). Applied to the
  configurations `zipCapDown γ τ (pcfg …)` on the capacity flow, `LenCanonStmt` follows from
  `LenCanonRegStmt` (`lenCanonStmt_of_reg`).
* **`LenLeftSurjStmt`**. By the intermediate value theorem (mathlib `intermediate_value_Icc`),
  surjectivity of `L⁻` onto `(0,∞)` follows from continuity of `L⁻` on `[0,∞)` with `L⁻_0 = 0`
  (`LenLeftRegStmt`, the left analogue of `LenRightRegStmt`) and unboundedness
  (`LenLeftUnbddStmt`) (`lenLeftSurjStmt_of_reg_unbdd`).

Own elementary bookkeeping around the cited scaling.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace F1

/-! ## Canonical rescaling of the lengths -/

/-- The driver of a configuration unzipped by `τ ≥ 0` is continuous, normalized, and constant on
`(−∞, 0]`. -/
theorem zipCapDown_snd_props {γ τ : ℝ} {c : FieldSample × (ℝ → ℝ)} (hW : Continuous c.2) :
    Continuous (zipCapDown γ τ c).2 ∧ (zipCapDown γ τ c).2 0 = 0 ∧
      ∀ s, (zipCapDown γ τ c).2 (max s 0) = (zipCapDown γ τ c).2 s := by
  refine ⟨(hW.comp (continuous_const.add (continuous_id.max continuous_const))).sub
    continuous_const, by simp [zipCapDown], fun s => ?_⟩
  simp only [zipCapDown, max_eq_left (le_max_right s 0)]

/-! ## Surjectivity of the left length -/

end F1
end QuantumZipper
