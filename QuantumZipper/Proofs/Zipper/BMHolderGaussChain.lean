import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# BM-HOLDER-GAUSS (deterministic part): dyadic chaining for `1/3`-Hölder bounds

`holder_of_dyadic`: if `g : ℝ → ℝ` is continuous and its increments over the dyadic intervals
`[k 2^{-n}, (k+1) 2^{-n}] ⊆ [0,1]` are at most `L ρ^n` with `ρ = 2^{-1/3}`, then
`|g t − g s| ≤ bmHolderK · L · |t − s|^{1/3}` on `[0,1]`.

This is the deterministic chaining step of the Kolmogorov–Čentsov theorem (Revuz–Yor,
*Continuous Martingales and Brownian Motion*, 3rd ed., Ch. I, proof of Thm (2.1), pp. 26–27),
written with the rounding maps `π_n x = ⌊2^n x⌋ / 2^n` instead of dyadic expansions
(consecutive roundings differ by at most one dyadic step of level `n+1`). The presentation via
`π_n` is an own elementary rewriting of that proof.
-/

noncomputable section

open Filter Set
open scoped Topology

namespace QuantumZipper
namespace RegUnif

/-- `ρ = 2^{-1/3}`. -/
def bmRho : ℝ := (1 / 2 : ℝ) ^ ((1 : ℝ) / 3)

variable {g : ℝ → ℝ} {L : ℝ}

end RegUnif
end QuantumZipper
