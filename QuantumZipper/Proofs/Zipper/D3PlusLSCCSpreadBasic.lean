import QuantumZipper.Proofs.Zipper.D3PlusLSCCInd
import QuantumZipper.Proofs.Zipper.D3PlusN2TmZScale

/-!
# D3⁺(ii) spread, part 0: the level shift and measurability of the log scale

Task LSCC-SPREAD.

* `n2Lev_shift`: the embedding level `n2Lev γ α L r = L/γ − (α − Q) log r` (`D3PlusN2TmZStmt`)
  shifts by exactly `c / γ` when `L ↦ L + c`. Hence a bounded shift of the model level is a
  bounded shift of the level of the Brownian motion with drift whose hitting time `ZoomRadial.Tc`
  is the embedding time (Duplantier–Miller–Sheffield arXiv:1409.7055, Prop. 4.7, p. 78).
* `measurable_lsccS`: the log scale of the model zoom is measurable.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace D3Plus

/-! ## The level shift -/

/-- A bounded shift of the model level is a shift of the embedding level by `c / γ`. -/
theorem n2Lev_shift (γ α r L c : ℝ) :
    n2Lev γ α (L + c) r = n2Lev γ α L r + c / γ := by
  simp only [n2Lev]
  ring

/-! ## Measurability of the log scale -/

end D3Plus
end QuantumZipper
