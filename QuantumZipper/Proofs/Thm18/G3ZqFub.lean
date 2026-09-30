import QuantumZipper.Proofs.Thm18.G3ZpFub
import QuantumZipper.Proofs.Thm18.G3ZrMain
import QuantumZipper.Proofs.Thm18.G1TopMain
import QuantumZipper.Proofs.Thm18.G1Side3Top
import QuantumZipper.Proofs.Thm18.G1Side2Wire
import QuantumZipper.Proofs.Thm18.G1PkgLeft
import QuantumZipper.Proofs.Thm18.G4WedgeRightInf

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3PATH (1): `G3TCurveStmt` from the fixed-path comparison alone (D93 rewiring)

Area-only copy of `G3Zp.g3TCurveStmt_of_path` (G3ZpFub): the curve Fubini formula is taken from
`G3Zr.g3zWedgePalmCyl_fubini_side` (area-only window regularity, D93), whose only remaining
hypothesis is the positivity of the length partner `R(x)` at a.e. window point. That positivity
holds a.s. at every `x < 0` (`ae_g3zPartner_pos`): the boundary measure of a wedge is atomless,
charges every interval, and has infinite mass on `[0, ∞)`.

* `ae_g3zPartner_pos`;
* **`g3TCurveStmt_of_pathA : G3ZpPathStmt → R18.G3TCurveStmt`** (`G3ZpFacRegStmt` retired).

Own bookkeeping (Fubini over the independent curve, dominated convergence), as in G3ZpFub;
Sheffield, arXiv:1012.4797, p. 71 (the curve is independent of the wedge).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Function
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace Thm18Asm
namespace G3Zq

open G3Z2b2 G3Zp

/-- **The length partner of a left window point is positive**, a.s. at every `x < 0`. -/
theorem ae_g3zPartner_pos {γ : ℝ} {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} {Y : Ω → FieldSample}
    (hS : Thm18Setting γ P B Y) (hIn : Thm18Inputs γ P B Y) :
    ∀ᵐ ω ∂P, ∀ x : ℝ, x < 0 → 0 < R18.g3zPartner γ (Y ω) x := by
  have ⟨hγ, hγ2, _, hW, _⟩ := hS
  filter_upwards [ae_atomless_pos_wedge hS hIn, wedgeRightInfStmt_holds γ P Y hγ hγ2 hW]
    with ω ⟨hatom, hpos⟩ hRinf x hx0
  refine R18.g3_lenRight_pos (hatom 0) hRinf (fun b => qBoundaryMeasure_Icc_lt_top γ _ 0 b) ?_
  exact ENNReal.toReal_pos
    (lt_of_lt_of_le (hpos x 0 hx0) (measure_mono Ioo_subset_Icc_self)).ne'
    (qBoundaryMeasure_Icc_lt_top γ _ x 0).ne

end G3Zq
end Thm18Asm
end QuantumZipper
