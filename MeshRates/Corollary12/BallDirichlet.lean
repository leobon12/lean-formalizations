import MeshOnly.MeshOnlyConvergence
import BouRabeeGwynne.TheoremBStatement

/-! The Dirichlet-approximation input consumed by the BRG Section 4 chain
(Lean form of BRG Assumption D (4.2) as actually used), derived from the mesh
hypothesis alone via the mesh-only Theorem 1.1 (`MeshOnly`). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace BouRabeeGwynne.MeshRates

/-- Exactly the conclusion of the call `theoremB_part_a … hreg hh` at
`BouRabeeGwynne/Section4BallHarmonicMeasure.lean:86`, quantified over the data
used there: every bounded domain with an ambient collar and every function
harmonic near its closure. -/
def BallDirichletInput {d : ℕ} (G : TilingSequence d) : Prop :=
  ∀ (U : Set (Euc d)) (h : Euc d → ℝ), IsDomain U → Bornology.IsBounded U →
    HasAmbientCollar U G.domain → HarmonicNearClosure h U →
      DirichletApproximationTarget G U h (fun n v => h ((G.tiling n).pos v))

/-- The mesh hypothesis alone supplies `BallDirichletInput` for `d ≥ 2`. -/
theorem ballDirichletInput_of_meshConverges {d : ℕ} (hd : 2 ≤ d) {G : TilingSequence d}
    (hmesh : G.MeshConverges) : BallDirichletInput G := by
  intro U h _ hUb hUD hh
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  exact dirichletApproximation_of_uniformMeshOnly (by omega) G U hUb hUD hmesh
    (G.uniformMeshOnlyDirichlet hd hmesh hUb hUD) h hh

end BouRabeeGwynne.MeshRates
