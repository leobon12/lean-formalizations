import LQGMetric.Statement.GFF

/-!
# Mean-zero test functions supported in a set

`TestC0On W` is shared by the §7 Möbius-law packet (`Lower/MobiusLaw.lean`) and the conformal-covariance
interfaces (`Core/Interfaces.lean`).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace SmallGammaGeodesics

open LQGMetric

/-- Mean-zero test functions supported in `W`: the index set of the σ-algebra
`LQGMetric.Blueprint.fieldSigma0On h W` of `h|_W` modulo additive constants. -/
abbrev TestC0On (W : Set ℂ) : Type := {ψ : TestC0 // tsupport (ψ.1 : ℂ → ℝ) ⊆ W}

end SmallGammaGeodesics
