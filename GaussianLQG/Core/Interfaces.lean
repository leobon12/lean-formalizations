import GaussianLQG.Core.Setup
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Interface propositions between the proof layers (internal)

Each proposition is the exact conclusion of one blueprint result for an arbitrary `Setup`. A packet
that proves the result proves the proposition for every `S : Setup`; a packet that consumes it takes
it as a hypothesis. The assembly discharges every such hypothesis before anything is sealed. These
are implementation interfaces, never frozen declarations.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory Filter Topology

namespace GaussianLQG.Setup

variable (S : Setup)

/-- Blueprint Proposition `prop:crossing`: `𝖸_γ = (log C_γ - b_γ) / ξ_γ → M` in probability as
`γ ↓ 0`, where `C_γ` is the left–right crossing distance of the unit square. -/
def CrossingConv : Prop :=
  TendstoInMeasure stdP
    (fun γ ω => (Real.log (LQGMetric.GM.crossFn (S.D γ ω).1) - S.b γ) / S.ξ γ) (𝓝[>] 0) S.M

/-- Blueprint Corollary `cor:fixed-pair`: `(log D^γ(0,1) - b_γ) / ξ_γ → H(0,0)` in probability as
`γ ↓ 0`. -/
def FixedPairConv : Prop :=
  TendstoInMeasure stdP
    (fun γ ω => (Real.log ((S.D γ ω).1 (0, 1)) - S.b γ) / S.ξ γ) (𝓝[>] 0) (S.H 0 0)

/-- Blueprint Lemma `lem:law-M`: `q` is the unique median of `M`, and `q < 0`. -/
def LawM : Prop :=
  (LQGMetric.IsMedian (stdP.map S.M) S.q ∧
    ∀ m, LQGMetric.IsMedian (stdP.map S.M) m → m = S.q) ∧ S.q < 0

/-- `H(0,0) ~ N(0, 3/2)`: blueprint Lemma `lem:field`(b) with Lemma `lem:segments`(a). -/
def H00Law : Prop :=
  stdP.map (S.H 0 0) = ProbabilityTheory.gaussianReal 0 (3 / 2 : NNReal)

end GaussianLQG.Setup
