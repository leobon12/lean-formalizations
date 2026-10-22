import HigherDimLQGMetric.Frozen.DistOnMeasurableSpace
import HigherDimLQGMetric.Frozen.DistRd
import HigherDimLQGMetric.Frozen.TestRd0
import HigherDimLQGMetric.Frozen.LogCovRd
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Def
import Mathlib.Probability.Moments.Covariance

/-!
# Frozen definition: `IsWholeSpaceLGF`

Anchor of the statement surface of the higher-dimensional LQG metric formalization (manifest
`HigherDimLQGMetric/Frozen/frozen-anchors.json`; rulings `planning/RULINGS.md`, M1, M13).
Source: `source/higher-dimensional-lqg-metric.pdf` ([S], cited by line of the text extraction `.txt`):
[S] l. 50–56 ("the whole-space log-correlated Gaussian field ... Modulo constants its covariance is
∫∫ ϕ(x)ψ(y) log(1/|x − y|) dx dy, ∫ϕ = ∫ψ = 0"), [1] (1.1) and §1.1 ("we say that a random generalized
function `h` is a whole-space LGF if it has the same law as a whole-space LGF viewed modulo an additive
constant"): `h` is a random distribution whose pairings with mean-zero test functions form a centered
Gaussian process with covariance `logCovRd`. The additive constant is arbitrary (possibly random).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory

namespace HigherDimLQGMetric

open HigherDimLFPP (Rd)

/-- `h` is a whole-space LGF on `ℝ^d` (with an arbitrary, possibly random, additive constant): its
pairings with mean-zero test functions form a centered Gaussian process with covariance `logCovRd`. -/
structure IsWholeSpaceLGF {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (h : Ω → DistRd d)
    (P : Measure Ω) : Prop where
  measurable : Measurable h
  gaussian : IsGaussianProcess (fun (φ : TestRd0 d) (ω : Ω) => h ω φ.1) P
  centered : ∀ φ : TestRd0 d, ∫ ω, h ω φ.1 ∂P = 0
  covariance_eq : ∀ φ ψ : TestRd0 d,
    cov[fun ω => h ω φ.1, fun ω => h ω ψ.1; P] = logCovRd φ.1 ψ.1

end HigherDimLQGMetric
