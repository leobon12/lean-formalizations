import HigherDimLQGContinuity.Core.Interfaces
import HigherDimLQGContinuity.Norm.Pin

/-!
# Inspected radius and centre grids (packet P4)

The pairs inspected in Lemma 2.2 have radii `λ ^ (-k)` above `exp (-n)` and
centres in the lattice of mesh `κ r` inside the closed ball of radius `W`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGContinuity

open HigherDimLQGMetric
open HigherDimLFPP (Rd)

/-- The inspected grid of Part A, Definition `a:def-grid`. -/
def gridPairs (d : ℕ) (lam κ : ℝ) (n : ℕ) (W : ℝ) : Set (ℝ × Rd d) :=
  {p | ∃ k : ℕ, p.1 = lam ^ (-(k : ℝ)) ∧ Real.exp (-(n : ℝ)) ≤ p.1 ∧
    ∃ j : Fin d → ℤ, p.2 = HigherDimLFPP.DGZ.latPt (κ * p.1) j ∧ ‖p.2‖ ≤ W}

end HigherDimLQGContinuity
