import GaussianLQG.Core.Defs
import LQGMetric.Basic
import LQGMetric.Papers.GM.S1.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.ContinuousMap

/-!
# The abstract setup for Sections 3–7 (internal interface)

`Setup` packages the six properties (S1)–(S6) of blueprint §1.6 in coordinate form, for metrics
`D γ : Coord → ContMetric` driven by a GFF frame `e` on `(ℝ^ℕ, stdP)`. Sections 3–7 of the blueprint
are proved for an arbitrary `Setup`. The main theorem instantiates it: the realization (blueprint
Prop. `prop:realization`) and the canonical GM21 metric (Prop. `prop:S2-S5`) give (S2)–(S5), and the
two inputs give (S1) and (S6).

This is an internal implementation interface, not a source-facing statement. It never appears in a
frozen declaration.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal

namespace GaussianLQG

/-- `(u, v) ↦ (z + a u, z + a v)`. -/
def affinePair (z a : ℂ) : C(ℂ × ℂ, ℂ × ℂ) :=
  ⟨fun p => (z + a * p.1, z + a * p.2), by fun_prop⟩

/-- The properties (S1)–(S6) of blueprint §1.6 in coordinate form. -/
structure Setup where
  /-- the GFF frame -/
  e : ℕ → ℂ → ℝ
  frame : IsGFFFrame e
  /-- `ξ_γ = γ / d_γ` -/
  ξ : ℝ → ℝ
  ξ_pos : ∀ γ, 0 < γ → γ < 2 → 0 < ξ γ
  /-- the metrics `D^γ(ω)` (continuous metrics inducing the Euclidean topology) -/
  D : ℝ → Coord → LQGMetric.ContMetric
  /-- (S1) exponents: `|d_γ - 2| ≤ C₀ γ` for small `γ`, with `d_γ = γ / ξ_γ` -/
  S1 : ∃ γ₀ C₀ : ℝ, 0 < γ₀ ∧ ∀ γ ∈ Ioc (0 : ℝ) γ₀, |γ / ξ γ - 2| ≤ C₀ * γ
  /-- (S2) measurability -/
  measurable_D : ∀ γ, Measurable (D γ)
  /-- (S2) length metric and (S3) Weyl scaling at every base point of a full-measure set -/
  good : ∀ γ, 0 < γ → γ < 2 → ∃ Ωγ : Set Coord, MeasurableSet Ωγ ∧ stdP Ωγᶜ = 0 ∧
    ∀ ω ∈ Ωγ, (D γ ω).IsLength ∧
      ∀ (v : ℕ →₀ ℝ) (z w : ℂ), ENNReal.ofReal ((D γ (shiftBy ω v)).1 (z, w)) =
        LQGMetric.weylScale (ξ γ) (frameFunC e frame.1 v) (D γ ω) z w
  /-- (S4) affine covariance in law, with `h_r(z)` the frame pairing with the circle measure -/
  S4 : ∀ γ, 0 < γ → γ < 2 → ∀ z a : ℂ, a ≠ 0 →
    stdP.map (fun ω => ((‖a‖ ^ (-(ξ γ * LQGMetric.Q γ)) *
        Real.exp (-(ξ γ) * pairing e (circleMeasure z ‖a‖) ω)) •
          (D γ ω).1.comp (affinePair z a) : C(ℂ × ℂ, ℝ))) =
      stdP.map (fun ω => (D γ ω).1)
  /-- (S5) normalization: `1` is a median of the left–right crossing distance -/
  S5 : ∀ γ, 0 < γ → γ < 2 →
    LQGMetric.IsMedian (stdP.map fun ω => LQGMetric.GM.crossFn (D γ ω).1) 1
  /-- (S6) uniform moments (source Lemma 2.1) -/
  S6 : ∀ p : ℝ, 1 ≤ p → ∃ γp : ℝ, 0 < γp ∧ ∀ K : Set ℂ, IsCompact K → ∀ δ : ℝ, 0 < δ →
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ γ ∈ Ioc (0 : ℝ) γp,
      (∫⁻ ω, holderConst (D γ ω).1 K ^ p ∂stdP) ≤ C ∧
      (∫⁻ ω, (sepInf (D γ ω).1 K δ)⁻¹ ^ p ∂stdP) ≤ C

namespace Setup

variable (S : Setup)

/-- The segment pairing `H(s,t) = (h, λ_{is,1+it})` in coordinates. -/
def H (s t : ℝ) (ω : Coord) : ℝ :=
  pairing S.e (segMeasure ((s : ℂ) * Complex.I) (1 + (t : ℂ) * Complex.I)) ω

/-- The dyadic rationals in `[0,1]`. -/
def dyadicUnit : Set ℝ := {y | ∃ n k : ℕ, k ≤ 2 ^ n ∧ y = (k : ℝ) / 2 ^ n}

/-- `M = inf_{y dyadic} H(y,y)` in coordinates. -/
def M (ω : Coord) : ℝ := ⨅ y : dyadicUnit, S.H y y ω

/-- `q = med M`, the lower median of the law of `M`. -/
def q : ℝ := LQGMetric.lowerMedian stdP S.M

/-- `b_γ = E log D^γ(0,1)`. -/
def b (γ : ℝ) : ℝ := ∫ ω, Real.log ((S.D γ ω).1 (0, 1)) ∂stdP

end Setup

end GaussianLQG

/-! ## Interface statements shared by packets W7 and W8 (blueprint Lemma `lem:scaling`(c),(d))

W7 proves these two propositions for every `Setup`; W8 consumes them. They are internal
interface propositions, not source theorems. -/

namespace GaussianLQG.Setup

open MeasureTheory Set
open scoped ENNReal

variable (S : Setup)

/-- Lemma `lem:scaling`(c): for each `p ≥ 1` there are `γ* > 0` and `C` such that for `γ ∈ (0, γ*]` and
`R ≥ 1`, `E[A_γ(B̄_R)^p] ≤ C R^{p(ξQ - 1/2) + p² ξ²}`. -/
def HolderScaling : Prop :=
  ∀ p : ℝ, 1 ≤ p → ∃ γs C : ℝ, 0 < γs ∧ ∀ γ ∈ Ioc (0 : ℝ) γs, ∀ R : ℝ, 1 ≤ R →
    (∫⁻ ω, holderConst (S.D γ ω).1 (Metric.closedBall (0 : ℂ) R) ^ p ∂stdP) ≤
      ENNReal.ofReal (C * R ^ (p * (S.ξ γ * LQGMetric.Q γ - 1 / 2) + p ^ 2 * S.ξ γ ^ 2))

/-- Lemma `lem:scaling`(d): for each `p ≥ 1` there are `γ* > 0` and `C` such that for `γ ∈ (0, γ*]` and
`R ≥ 1`, `E[L_R^{-p}] ≤ C R^{-p ξQ + p² ξ²}`. -/
def AnnulusScaling : Prop :=
  ∀ p : ℝ, 1 ≤ p → ∃ γs C : ℝ, 0 < γs ∧ ∀ γ ∈ Ioc (0 : ℝ) γs, ∀ R : ℝ, 1 ≤ R →
    (∫⁻ ω, (annulusCross (S.D γ ω).1 R)⁻¹ ^ p ∂stdP) ≤
      ENNReal.ofReal (C * R ^ (-(p * (S.ξ γ * LQGMetric.Q γ)) + p ^ 2 * S.ξ γ ^ 2))

end GaussianLQG.Setup
