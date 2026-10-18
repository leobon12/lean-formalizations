import MeshRates.Statement.Theorem11Rate
import MeshOnly.MeshOnlyConvergence

/-! MR Theorem 1.1, equation (9): qualitative mesh-only convergence, assembled from the
`MeshOnly` library (`uniformMeshOnlyDirichlet` + `dirichletApproximation_of_uniformMeshOnly`). -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace BouRabeeGwynne.MeshRates

theorem theorem11_qualitative : MeshRatesTheorem11QualitativeStatement := by
  intro d hd G U hU hUD hmesh h hh
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  exact dirichletApproximation_of_uniformMeshOnly (by omega) G U hU hUD hmesh
    (G.uniformMeshOnlyDirichlet hd hmesh hU hUD) h hh

end BouRabeeGwynne.MeshRates
