import LQGMetric.Statement.Field
import QuantumZipper.GFF.Defs
import QuantumZipper.Statements.Thm11

/-! Frozen anchor (ruling A15, author-delegated approval of 2026-10-25 of revision 2.2: planning/candidates/rev2.2/APPROVAL-REQUEST.md, sha256 cbc72606…, commit bb67bbe3c). One declaration: `IsGreenian`. Declaration unchanged from the candidate `CandIsGreenian.lean` (sha256 40b18d172a6875e3…). -/

set_option autoImplicit false

noncomputable section

open TopologicalSpace

namespace SupercriticalConformalCovariance

/-- Ruling A14 (the author: "assume that U, V are greenian domains so that the GFF actually exists"):
the open set `U` is **Greenian**, i.e. the zero-boundary GFF on `U` exists. For every test function
`ψ ∈ 𝓓(U)` the measures `ψ⁺ dz` and `ψ⁻ dz` are admissible for QuantumZipper's dual Dirichlet norm on `U`:
finite, compactly supported in `closure U` (automatic for test functions), and of finite dual Dirichlet norm
`sup_{g ∈ C_c^∞(U), (g, g)_∇ > 0} (∫ g dμ)² / (g, g)_∇ < ∞`, i.e. finite `H⁻¹(U)` norm (finite Green energy).
This is the body of LQGMetric's `ZBAdmissible U`, written out. It is exactly the condition under which
LQGMetric's zero-boundary GFF on `U` (`LQGMetric.IsZeroBoundaryGFF`, covariance
`zeroGFFTestCov U = ⟨·, ·⟩_{H⁻¹(U)}`) has its honest, finite variances (Sheffield, math/0312099, §2). Every
bounded open set is Greenian (`LQGMetric.zbAdmissible_of_isBounded`).

Classically, for an open `U ⊆ ℂ`, this is equivalent to `ℂ ∖ U` being non-polar (of positive
logarithmic capacity), i.e. to `U` having a Green's function; so `ℂ` and `ℂ` minus a closed polar set
(for instance finitely many points) are not Greenian. That equivalence is **not** proved here, and no
Lean library defines polar sets or logarithmic capacity. -/
def IsGreenian (U : Opens ℂ) : Prop :=
  ∀ ψ : LQGMetric.TestOn U,
    QuantumZipper.IsAdmissibleDual U (QuantumZipper.zeroSpace U) (QuantumZipper.testMeasPos ψ) ∧
      QuantumZipper.IsAdmissibleDual U (QuantumZipper.zeroSpace U) (QuantumZipper.testMeasNeg ψ)

end SupercriticalConformalCovariance
