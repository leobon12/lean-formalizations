import HigherDimLQGMetric.Events.Defs

/-!
# Section 5 frequency statements

The statement shapes are those of MA3 Details (c), §4. The frequency package
keeps the same regularity constants while the witness threshold is decreased.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

/-- Absence of a short witness improves the ratio on a crossing geodesic. -/
def Lemma51 (d : ℕ) : Prop :=
  ∀ (A B : DistRd d → ContMetric d) (ξ Q U a A₀ ℓ β₀ t r : ℝ) (z : Rd d) (h : DistRd d),
    0 < r → 0 < ℓ → ℓ < a / 100 → 0 ≤ t → (A h).IsLength →
    h ∈ RegEvent A B ξ Q U a A₀ ℓ β₀ r z → h ∉ WitEvent A B ξ Q U a A₀ ℓ β₀ t r z →
    ∀ P : ℝ → Rd d, IsGeod (A h) P →
      P 0 ∈ Metric.sphere z r → P 1 ∈ Metric.sphere z (2 * r) →
      (∀ τ ∈ Icc (0 : ℝ) 1, P τ ∈ annCl z r (2 * r)) →
      ENNReal.ofReal ((B h).1 (P 0, P 1)) ≤ ENNReal.ofReal t * (A h).len P 0 1

/-- Proposition 5.4, with `θ = a/A₀`. -/
def FrequencyLemma (d : ℕ) (ξ Q : ℝ) (A B : DistRd d → ContMetric d)
    (U a A₀ ℓ β₀ pstar : ℝ) : Prop :=
  ∀ t u β : ℝ, 0 < t → t < U → U - a / A₀ * (U - t) < u → 0 < β →
  ∃ ε₀ : ℝ, 0 < ε₀ ∧
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d), IsWholeSpaceLGF h P →
  ∀ R : ℝ, 0 < R → ENNReal.ofReal β ≤ P (h ⁻¹' GEvent A B ξ Q u β R) →
  ∀ ε : ℝ, 0 < ε → ε < ε₀ →
    (3 / 4 : ℝ) * (scaleWin ε R).ncard ≤
      ({j ∈ scaleWin ε R | ENNReal.ofReal pstar ≤
        P (h ⁻¹' WitEvent A B ξ Q U a A₀ ℓ β₀ t ((64 : ℝ) ^ j) 0)} : Set ℤ).ncard

/-- The §5 package, including monotonicity under decreasing `pstar`. -/
def Section5Package (d : ℕ) (ξ Q : ℝ) (A B : DistRd d → ContMetric d) (U : ℝ) : Prop :=
  ∃ a A₀ ℓ β₀ pstar : ℝ, 0 < a ∧ a < A₀ ∧ 0 < ℓ ∧ ℓ < a / 100 ∧
    0 < β₀ ∧ β₀ < 1 ∧ 0 < pstar ∧
    ∀ pstar' ∈ Ioc 0 pstar, FrequencyLemma d ξ Q A B U a A₀ ℓ β₀ pstar'

/-- The essential upper comparison and its optimality for every LGF. -/
def IsOptUpper (d : ℕ) (A B : DistRd d → ContMetric d) (U : ℝ) : Prop :=
  (∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d), IsWholeSpaceLGF h P →
      ∀ᵐ ω ∂P, ∀ x y : Rd d, (B (h ω)).1 (x, y) ≤ U * (A (h ω)).1 (x, y)) ∧
  ∀ U' : ℝ, U' < U → ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (h : Ω → DistRd d), IsWholeSpaceLGF h P →
      ¬ ∀ᵐ ω ∂P, ∀ x y : Rd d, (B (h ω)).1 (x, y) ≤ U' * (A (h ω)).1 (x, y)

/-- Corollary 5.5 for a finite list of thresholds and an enlargeable radius. -/
def Cor55 (d : ℕ) (ξ Q : ℝ) (A B : DistRd d → ContMetric d)
    (U a A₀ ℓ β₀ pstar : ℝ) : Prop :=
  ∀ ts : Finset ℝ, (∀ t ∈ ts, 0 < t ∧ t < U) → ∃ R₀ : ℝ, 0 < R₀ ∧ ∀ R₁ : ℝ, R₀ ≤ R₁ →
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ t ∈ ts,
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d), IsWholeSpaceLGF h P → ∀ ε : ℝ, 0 < ε → ε < ε₀ →
    (3 / 4 : ℝ) * (scaleWin ε R₁).ncard ≤
      ({j ∈ scaleWin ε R₁ | ENNReal.ofReal pstar ≤
        P (h ⁻¹' WitEvent A B ξ Q U a A₀ ℓ β₀ t ((64 : ℝ) ^ j) 0)} : Set ℤ).ncard

end HigherDimLQGMetric
