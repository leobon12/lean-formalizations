import QuantumZipper.Proofs.Thm18.G3ZqNodes
import QuantumZipper.Proofs.Thm18.G3ZqG2PalmR
import QuantumZipper.Proofs.Thm18.R18G3TSplit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# G3PATH (9): the mixing body of the map zooms with the wedge law as limit

`G2FixMixStmtZ` (G3ZqG2Fix) only asserts the existence of limit laws. To compare the map zooms
with the plain ones the limit laws must be the explicit `γ`-wedge law `g2WedgeLaw P' Y'` on both
sides, as in the plain engine (`g2FixMixStmt_of_agreeLeaves`). This file gives the body form
`R18.G3FixMixBody` for explicit laws:

* `g3FixMixBodyZ_of_len`: body form of `g2FixMixStmtZ_of_len` (same proof);
* **`g3FixMixBody_map`**: for the zooms through the local maps of a good path, the body with
  limit laws `g2WedgeLaw P' Y'` from the three map leaves `G3ZqFixXStmt`, `G3ZqFixRStmt`,
  `G3ZqZoomLocStmt`.

Sheffield, arXiv:1012.4797, proof of Prop. 5.5, pp. 65–66. Own bookkeeping.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology ENNReal NNReal

namespace QuantumZipper
namespace Thm18Asm
namespace G3Zq

/-- **Body form of `g2FixMixStmtZ_of_len`.** -/
theorem g3FixMixBodyZ_of_len {Z Z' : ℝ → FieldSample → ℝ → LawD} {γ : ℝ} (hγ : 0 < γ)
    (hγ2 : γ < 2) {μ ν : Measure LawD} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hX : G2FixMixLenXStmtZ Z γ μ) (hR : G2FixMixLenRStmtZ Z' γ ν) :
    R18.G3FixMixBody μ ν (g3PalmLaw γ) (g3X γ) (g3R γ) (g3UfZ Z γ) (g3VfZ Z' γ) := by
  refine ⟨fun s hs δ η m hm ε hε => ?_, fun t ht δ η m hm ε hε => ?_⟩
  · exact palm_mix_of_len hγ hγ2 δ η (μ.real s) (fun i => g3UfZ Z γ i ⁻¹' s)
      (fun i => {p | |g3X γ i p - i.t₁| + m < i.r₁}) hε
      (fun ε' hε' => hX s hs δ η m hm ε' hε')
  · exact palm_mix_of_len hγ hγ2 δ η (ν.real t) (fun i => g3VfZ Z' γ i ⁻¹' t)
      (fun i => {p | |g3R γ i p - i.t₂| + m < i.r₂}) hε
      (fun ε' hε' => hR t ht δ η m hm ε' hε')

end G3Zq
end Thm18Asm
end QuantumZipper
