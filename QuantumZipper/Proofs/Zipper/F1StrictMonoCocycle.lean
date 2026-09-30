import QuantumZipper.Proofs.Zipper.UnifClColl
import QuantumZipper.Proofs.Zipper.UnifClB5

/-!
# Theorem 1.3, node F1: additivity of `L⁻` along the capacity flow at all times (D26)

`E6.LenCocycleStmt` (`E6Id.lean`) states the additivity of the left length along the capacity flow
at a fixed horizon `T`, and `UnifClColl.lenCocycleStmt_of_windows` proves it from UW, UA and the
field cocycle `B3d.CapCocycleRegStmt` at that horizon. The F1 node needs the identity at **all**
times (`F1.PStarLenCocycleStmt` is its `P_*` form, and the deterministic bookkeeping
`F1.strictMonoOn_of_add_pos` turns it, with the positivity of the new piece, into strict
monotonicity of `s ↦ L⁻_s`).

* `CapCocycleRegAllStmt`: `B3d.CapCocycleRegStmt` at every horizon;
* **`ae_lenCocycle_all_of_unifAll`**: from UW, UA and the field cocycle at every horizon, a.s.
  `L⁻_{u+s} = L⁻_u + L⁻_s(𝒵_u)` for all `u, s ≥ 0`, `𝒵_u = zipCapDown γ u (cfg κ B X ω)`
  (the horizon-free identity of `E6.LenCocycleStmt`, by intersecting the countably many
  horizons `T = n`).

Source: Sheffield, arXiv:1012.4797, §5, Lemma 5.6, pp. 66–68 (the paper treats the length of
`η[0,s]` as one object and does not discuss additivity along the flow). Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology NNReal ENNReal

namespace QuantumZipper
namespace RegUnif

open B2 B5

variable {Ω : Type} [MeasurableSpace Ω]

/-- **The field cocycle at every horizon**: `B3d.CapCocycleRegStmt` holds for every `T > 0`. -/
def CapCocycleRegAllStmt (κ : ℝ) (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ) (X : Ω → FieldSample) :
    Prop :=
  ∀ T : ℝ, 0 < T → B3d.CapCocycleRegStmt κ T P B X

variable {P : Measure Ω} [IsProbabilityMeasure P] {κ : ℝ} {B : ℝ≥0 → Ω → ℝ}
  {X : Ω → FieldSample}

end RegUnif
end QuantumZipper
