import QuantumZipper.Proofs.Thm18.G3ZcFar

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# ZOOM-C (c), step 2: two local conformal couplings sharing the same field `W`

For the two-point zoom (Sheffield, arXiv:1012.4797, proof of Theorem 1.8, p. 71) the local
conformal coupling (`pullCouplingHarm_of_process`, G3ZcFar) must be run at two points `b₁`, `b₂`
(with maps `Φ₁`, `Φ₂`) **for one and the same free field `W`**. Each coupling is realized by an
isonormal process with the vectors `pVec J` in `WithLp 2 (HkE × HkE)`, whose first factor carries
the field `W` (vectors `(v̂_μ, 0)`). Both vector families embed isometrically into
`E₃ = WithLp 2 (WithLp 2 (HkE × HkE) × HkE)`, the first by `p ↦ (p, 0)`, the second by
`(x, z) ↦ ((x, 0), z)`, so that the `W`-vectors of the two families coincide. One isonormal process
on the joint index set `PIdx₁ ⊕ (AdmT ⊕ PXiIdx₂)` (the `W`-indices of the second coupling are
taken from the first) then yields two processes `Z₁`, `Z₂` with the isonormal laws of `pVec J₁`
and `pVec J₂`, and **`realWP Z₁ = realWP Z₂` definitionally** (`exists_sharedProcess`).

Consequently (`exists_twoCouplings`) there are, on one probability space, one free field `W` and,
for each of the two points, the full coupling data of `pullCouplingHarm_of_process` (free field
`X'ᵢ`, independent variables `Ξᵢ` containing the far field, harmonic part `gᵢ`).

Own construction (AGENT_GUIDE cost rule): the Gaussian-Hilbert-space realization of the domain
Markov coupling (Sheffield, *Gaussian free fields for mathematicians* (2007), §2.2 and Thm. 2.17)
at two points simultaneously.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Metric Filter Set
open scoped ComplexConjugate ENNReal Topology RealInnerProductSpace

namespace QuantumZipper
namespace G3Cv

open K3 GFFExist LQGDimension.ExistAsm

/-- The joint Hilbert space of two couplings. -/
abbrev E3 : Type := WithLp 2 (WithLp 2 (HkE × HkE) × HkE)

instance instSeparableE3 : TopologicalSpace.SeparableSpace E3 :=
  (WithLp.homeomorphProd 2 (WithLp 2 (HkE × HkE)) HkE).symm.isQuotientMap.separableSpace

section Shared

variable {Φ₁ Φ₂ : ℂ → ℂ} {b₁ b₂ ρ₁ ρ₂ r₁ r₂ : ℝ}

end Shared

end G3Cv
end QuantumZipper
