import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic

/-! Frozen anchor (ruling A15, author-delegated approval of 2026-10-25 of revision 2.2: planning/candidates/rev2.2/APPROVAL-REQUEST.md, sha256 cbc72606…, commit bb67bbe3c). One declaration: `IsConformalBijection`. Declaration unchanged from the candidate `CandIsConformalBijection.lean` (sha256 c1433aa54740d034…). -/

set_option autoImplicit false

noncomputable section

open Set

namespace SupercriticalConformalCovariance

/-- Paper l. 22–23 (Theorem 1.1): `φ` is a **conformal bijection** of the domain `U` onto the domain `V`:
`φ` is holomorphic on `U` and restricts to a bijection `U → V` (`Set.BijOn`: `φ` maps `U` into `V`, is
injective on `U`, and is onto `V`). The values of `φ` off `U` play no role. On an open `U` an injective
holomorphic map has non-vanishing derivative (`QuantumZipper.CA.deriv_ne_zero_of_injOn`) and a holomorphic
inverse on `V` (`SmallGammaGeodesics.CC.differentiableOn_leftInv`), so no derivative condition is added. -/
def IsConformalBijection (φ : ℂ → ℂ) (U V : Set ℂ) : Prop :=
  DifferentiableOn ℂ φ U ∧ BijOn φ U V

end SupercriticalConformalCovariance
