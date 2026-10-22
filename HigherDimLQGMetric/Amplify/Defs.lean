import HigherDimLQGMetric.Events.Defs

/-!
# Fine field amplification: event statements

The trial event and simple arc predicate follow MA3 Details (c). The amplification
statement includes the nonempty interior condition of ruling M15(i).
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace HigherDimLQGMetric

open MeasureTheory Set
open HigherDimLFPP (Rd)
open scoped ENNReal

variable {d : ℕ}

/-- The trial event `𝒲_{w,s}(X)` of source (13)–(14). -/
def TrialEvent (D Dt : DistRd d → ContMetric d) (ξ Q cs c1 ℓ δ s : ℝ) (w : Rd d) :
    Set (DistRd d) :=
  {X | ENNReal.ofReal (Real.exp (-ξ * δ) * (4 * max 1 cs⁻¹ * ℓ) * sNorm ξ Q X s w) <
      setDistIn (D X) (ann w (s / 2) (5 * s)) (annCl w s (2 * s))
        (Metric.sphere w (3 * s / 4) ∪ Metric.sphere w (3 * s)) ∧
    ∃ P : ℝ → Rd d, ContinuousOn P (Icc 0 1) ∧
      (∀ τ ∈ Icc (0 : ℝ) 1, P τ ∈ annCl w s (2 * s)) ∧
      ENNReal.ofReal (Real.exp (-ξ * δ) * (ℓ / (2 * c1)) * sNorm ξ Q X s w) ≤
        (D X).internal (ann w (3 * s / 4) (3 * s)) (P 0) (P 1) ∧
      (Dt X).len P 0 1 ≤ ENNReal.ofReal (Real.exp (ξ * δ) * ℓ * sNorm ξ Q X s w) ∧
      (Dt X).len P 0 1 ≤ ENNReal.ofReal (Real.exp (2 * ξ * δ) * c1) *
        (D X).internal (ann w (3 * s / 4) (3 * s)) (P 0) (P 1)}

/-- A simple arc on `[0,1]`. -/
def IsSimpleArc (γ : ℝ → Rd d) : Prop :=
  ContinuousOn γ (Icc 0 1) ∧ InjOn γ (Icc 0 1)

/-- Lemma 6.1, with the nonempty interior correction of ruling M15(i). -/
def FineFieldAmplification (d : ℕ) (ξ Q : ℝ) (D Dt : DistRd d → ContMetric d)
    (cs c1 c2 a A₀ ℓ β₀ pstar : ℝ) : Prop :=
  ∀ (M : ℕ) (O K : Fin M → Set (Rd d)),
    (∀ i, IsOpen (O i)) → (∀ i, IsCompact (K i)) → (∀ i, K i ⊆ O i) →
    (∀ i, (interior (K i)).Nonempty) →
    (∀ i, O i ⊆ ann 0 1 3) → Pairwise (fun i j => Disjoint (O i) (O j)) →
  ∀ p : ℝ, p < 1 → ∃ (m : ℕ) (a₁ A₁ : ℝ), 0 < a₁ ∧ a₁ < A₁ ∧
  ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (h : Ω → DistRd d), IsWholeSpaceLGF h P → ∀ r : ℝ, 0 < r →
    ENNReal.ofReal pstar ≤
      P (h ⁻¹' WitEvent Dt D ξ Q cs⁻¹ a A₀ ℓ β₀ c1⁻¹ ((64 : ℝ)⁻¹ ^ m * r) 0) →
    ENNReal.ofReal p ≤ P {ω | ∀ i, ∃ γ : ℝ → Rd d, IsSimpleArc γ ∧
      (∀ τ ∈ Icc (0 : ℝ) 1, γ τ ∈ (fun x => r • x) '' K i) ∧
      (Dt (h ω)).len γ 0 1 ≤ ENNReal.ofReal (c2 * (D (h ω)).1 (γ 0, γ 1)) ∧
      a₁ * sNorm ξ Q (h ω) r 0 ≤ (D (h ω)).1 (γ 0, γ 1) ∧
      (D (h ω)).len γ 0 1 ≤ ENNReal.ofReal (A₁ * sNorm ξ Q (h ω) r 0)}

end HigherDimLQGMetric
