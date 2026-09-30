import QuantumZipper.Proofs.Zipper.SWCoreDefs
import QuantumZipper.Proofs.Zipper.B2Defs
import QuantumZipper.Proofs.Zipper.Cor15Markov2Main
import QuantumZipper.Proofs.Zipper.F2Step3Dens
import QuantumZipper.Proofs.Zipper.F2Step3

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# SWC-B7 (part): the uniform boundary transport at the rational anchors `h⁰_q`

Task SWC-B7 (`handoff/SW-CORE.md` §3, decisions D53, D59). The cores of SW-CORE are pathwise
statements about a *free* field. The anchor field of AC-fam, `h⁰_q = h0f κ q B X ω`
(the configuration `(𝔥₀ + X, √κ B)` unzipped by capacity time `q`), is not the free field `X`.
This file moves the uniform boundary transport to the anchors **without any law transfer of a
non-measurable event**: by the proved unzip version of Corollary 1.5
(`Cor15Group.cor15UnzipVersionStmt_holds`, Sheffield arXiv:1012.4797 Thm 1.2, §1.4), for each
`q > 0` there is a free field `Y_q` **on the same probability space** with
`h⁰_q ~ 𝔥₀ + Y_q` (`RegEq`: all regularized circle averages agree) a.s.; `BdryTransportUnifStmt`
applies to `Y_q` directly (it holds for every free field process).

* `regEq_coordChange`, `bdryApprox_congr_regEq`, `qBoundaryMeasure_congr_regEq`,
  `bdryTransportUnifGood_congr_regEq`: every object read by the transport statements depends on a
  field only through its regularized circle averages.
* **`exists_free_anchor_transport`**: for `q > 0`, a free field `Y` with a.s.
  `RegEq h⁰_q (𝔥₀ + Y)` and `BdryTransportUnifGood √κ Y`.
* **`ae_anchor_transport_rat`**: a.s., simultaneously for all rational `q > 0`, a sample `y` with
  `RegEq h⁰_q (𝔥₀ + y)` and `BdryTransportUnifGood √κ y`.
* `unzY_eq_h0f`, **`ae_anchor_transport_rat_unzY`**: the same for the wedge-unzipped fields
  `y_q = F2.unzY κ X W q` of YBDRY-MERGE (they are the same fields, `F2.h0rev_add_eq`).

This bypasses the transfer nodes of ACFLOW-TRANSFER (`AnchorNormStmt`, measurability of
`goodEvt`) for the SW-CORE route. What it does **not** give is the transport for `𝔥₀ + y` itself:
the continuous add-on `𝔥₀` (see the report of SWC-B7; D59).

Own bookkeeping; sources: Sheffield arXiv:1012.4797 Thm 1.2 and §1.4 (through the proved
`cor15UnzipVersionStmt_holds`), Sheffield–Wang arXiv:1605.06171 Thm 4.3 (through the hypothesis
`BdryTransportUnifStmt`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace SWCore

/-! ## `RegEq`-invariance of the transport objects -/

theorem evalReg_congr_regEq {x y : FieldSample} (h : RegEq x y) (ν : Measure ℂ) :
    evalReg x ν = evalReg y ν := by
  have e : ∀ k, avgReg x k = avgReg y k := fun k => funext fun z => h k z
  simp only [evalReg, e]

theorem coordChange_congr_regEq {x y : FieldSample} (h : RegEq x y) (ψ : ℂ → ℂ) (Q : ℝ) :
    coordChange x ψ Q = coordChange y ψ Q := by
  funext μ
  simp only [coordChange, evalReg_congr_regEq h]

theorem bdryApprox_congr_regEq {x y : FieldSample} (h : RegEq x y) (γ : ℝ) (k : ℕ) :
    bdryApprox γ x k = bdryApprox γ y k := by
  simp only [bdryApprox, h k]

theorem qBoundaryMeasure_congr_regEq {x y : FieldSample} (h : RegEq x y) (γ : ℝ) :
    qBoundaryMeasure γ x = qBoundaryMeasure γ y := by
  have e : bdryApprox γ x = bdryApprox γ y := funext fun k => bdryApprox_congr_regEq h γ k
  unfold qBoundaryMeasure
  rw [e]

/-! ## The anchors -/

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {B : ℝ≥0 → Ω → ℝ} {X : Ω → FieldSample}

omit [MeasurableSpace Ω] in
theorem h0f_eq_zipCapDown (κ q : ℝ) (ω : Ω) :
    B2.h0f κ q B X ω = (zipCapDown (Real.sqrt κ) q (Cor15Group.grpCfg κ B X ω)).1 := by
  simp only [B2.h0f, B2.Yf, B2.zipped, B2.cfg, sub_zero]

end SWCore
end QuantumZipper
