import QuantumZipper.Proofs.Thm18.G3Pl4Exp
import QuantumZipper.Proofs.Thm18.G3Pl4Win
import QuantumZipper.Proofs.Thm18.G3Pl2Meas
import QuantumZipper.Proofs.Thm18.G3Pl4Bdry

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# R18-G3 step 5T, (G-b), part (b): averaged locality for a coupled pair of fields

For two random fields `Y₁`, `Y₂` on one probability space that are a.s. good, agree a.s. on every
folded circle inside the unit disc, and whose translates have positive area on half-balls, the
expected capped Palm functionals at large level differ by at most the Palm mass `U` times the
probability of the event where the window/partner separation conditions fail, plus `ε`
(`g3pl4_expect_cap_le`). This is the averaged form of the locality of the canonical zooms
(Sheffield, arXiv:1012.4797, pp. 71–72, Remark 5.7). Own bookkeeping on `g3pl4_phiCap_le_of_agree`,
`g3pl4_restrict_eq_of_agree`, `g3pl4_expect_le` (AGENT_GUIDE cost rule).
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped NNReal ENNReal Topology

namespace QuantumZipper
namespace R18

open Thm18Asm Prop16Area.G

/-- The separation conditions of the pathwise locality lemma. -/
def g3pl4Sep (γ δ : ℝ) (y : FieldSample) : Prop :=
  qBoundaryMeasure γ y (Icc (-δ) 0) < qBoundaryMeasure γ y (Icc (-(1 / 2)) 0) ∧
    qBoundaryMeasure γ y (Icc (-δ) 0) ≤ qBoundaryMeasure γ y (Icc 0 (1 / 4))

end R18
end QuantumZipper
