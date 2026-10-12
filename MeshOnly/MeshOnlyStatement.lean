import MeshOnly.MeshOnlyLocalization

/-!
# Theorem 1.1 of the volume-notation mesh-only draft

The source is `mesh_only_orthogonal_tilings_vol_notation.pdf`, page 2.
This file specifies the target; it does not claim that convergence is proved.
There is no regularity alternative, nearest-vertex datum, connectedness
assumption, or quantitative rate in this target.
-/

open scoped Topology

namespace BouRabeeGwynne

/-- A common C² bound, using the value and the operator norms of the first two
Fréchet derivatives. Bounding these three quantities separately is equivalent
to boundedness of the usual C² norm, and does not select a particular function
from the family. Harmonicity and C² regularity are imposed separately. -/
def C2BoundOn {d : ℕ} (h : Euc d → ℝ) (W : Set (Euc d)) (M : ℝ) : Prop :=
  ∀ x ∈ W, |h x| ≤ M ∧ ‖fderiv ℝ h x‖ ≤ M ∧
    ‖fderiv ℝ (fderiv ℝ h) x‖ ≤ M

/-- Uniformity in the final sentence of Theorem 1.1: the eventual index may
depend on the fixed neighborhood, its C² bound and the tolerance, but is chosen
before the harmonic function and before its discrete Dirichlet solution. -/
def UniformMeshOnlyDirichletTarget {d : ℕ} (G : TilingSequence d)
    (U : Set (Euc d)) : Prop :=
  ∀ (W : Set (Euc d)), IsOpen W → closure U ⊆ W →
    ∀ M : ℝ, 0 ≤ M → ∀ η : ℝ, 0 < η → ∀ᶠ n in Filter.atTop,
      ∀ h : Euc d → ℝ, IsHarmonicOn h W → C2BoundOn h W M →
        ∀ hD : (G.tiling n).V → ℝ,
          (G.tiling n).SolvesDirichlet U (fun v => h ((G.tiling n).pos v)) hD →
            (G.tiling n).DirichletError U h hD η

/-- The complete requested Theorem 1.1, including uniformity over bounded C²
families. `IsOpen G.domain` makes `closure U ⊆ G.domain` exactly the compact
containment condition in the source, since U is bounded in finite-dimensional
Euclidean space. Eventual well-posedness is included to make the solution
quantifiers nonvacuous; no behavior of unrelated ambient vertices is fixed. -/
def MeshOnlyTheorem11Statement : Prop :=
  ∀ (d : ℕ) (G : TilingSequence d) (U : Set (Euc d)),
    2 ≤ d → IsOpen G.domain → IsOpen U → Bornology.IsBounded U →
    closure U ⊆ G.domain → G.MeshConverges →
      (∀ h : Euc d → ℝ, HarmonicNearClosure h U →
        DirichletApproximationTarget G U h (fun n v => h ((G.tiling n).pos v))) ∧
      UniformMeshOnlyDirichletTarget G U

end BouRabeeGwynne
