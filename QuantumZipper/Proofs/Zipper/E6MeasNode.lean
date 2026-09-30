import QuantumZipper.Proofs.Zipper.E6NodeMain
import QuantumZipper.Proofs.Zipper.E6MeasCore
import QuantumZipper.Proofs.Zipper.E1Normalizer
import QuantumZipper.Proofs.NonVacuityFinal

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# E6 without Palm-side measurability (3): the E6 node without `E6PalmMeasStmt`

Theorem 1.3, node E6 (Sheffield, *Conformal weldings of random surfaces*, arXiv:1012.4797,
§5.4, proof of Thm 1.8, pp. 70–72; the paper does not discuss measurability). Task E6-AEMEAS.

* `e6_concrete_rich_nm`: `E6.e6_concrete_rich_ae` (`E6NodeMain.lean`) without the Palm-side
  measurability inputs `hHm` (collided set) and `hzcm` (zoomed local data); same proof, through
  `e6_core_rel_nm` (`E6MeasCore.lean`).
* `exists_e6PalmSetup`: an auxiliary Palm setup `E5.Setup κ (4/(4−κ)) P B X ϖ` exists for every
  `κ ∈ (0,4)` (Brownian motion independent of a free-boundary GFF,
  `NonVacuity.exists_BM_indep_freeGFF_uncond`; normalizer `foldedCircle (3i) 1`,
  `E1.isNormalizer_foldedCircle`).
* `e6NodeStmtRich_of_nodes_nm`: `E6.e6NodeStmtRich_of_nodes` **without** the input
  `E6PalmMeasStmt`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology

namespace QuantumZipper.E6

open B2 E1 D3Plus

variable {Ω : Type} [MeasurableSpace Ω] {Ω' : Type} [MeasurableSpace Ω']

/-- **An auxiliary Palm setup exists** for every `κ ∈ (0,4)`, at horizon `T = 4/(4−κ)`. -/
theorem exists_e6PalmSetup {κ : ℝ} (hκ : 0 < κ) (hκ4 : κ < 4) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (B : ℝ≥0 → Ω → ℝ)
      (X : Ω → FieldSample), IsProbabilityMeasure P ∧
      E5.Setup κ (4 / (4 - κ)) P B X (foldedCircle (3 * Complex.I) 1) := by
  obtain ⟨Ω, _, P, B, X, hPp, hB, hX, hind⟩ := NonVacuity.exists_BM_indep_freeGFF_uncond
  exact ⟨Ω, inferInstance, P, B, X, hPp, hκ, hκ4, div_pos (by norm_num) (by linarith), hB, hX,
    hind, isNormalizer_foldedCircle⟩

end QuantumZipper.E6
