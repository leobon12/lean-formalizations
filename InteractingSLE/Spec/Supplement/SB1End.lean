/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SBLemmaS
import InteractingSLE.Spec.Theorem15Inputs

/-!
# Lemma SB1 and Lemma S6: the terminal-endpoint step

Packet PROVE-T14-SB2. Lemma SB1 (supplement p. 630, `source/spec/p625-671.md` L106–L111) and Lemma S6 (p. 583,
`source/spec/p577-624.md` L124–L133) extend W5's strict-prefix ordered completions to the finite terminal endpoints.
Their proofs have the same two steps:

* **the middle exclusion** (path-specific): no terminal endpoint of either path meets the other prefix inside the
  closed seed interval. For SB1: "On a middle interval where the upper cumulative weight is inadmissible, the lower
  flow cannot visit that open interval [localized noncollision] [...] At every middle transition mark [...] G12 excludes
  its exact visit. Opposite original seeds are excluded by W0a. The lower path cannot terminate on any middle interval
  [...] Therefore no common middle point can be a terminal endpoint of either path." For S6: "It suffices here that no
  genuine continuation threshold can occur in the closed interval between the seeds; opposite-seed polarity supplies
  the two endpoint exclusions." Named `SB1MiddleStatement`, `S6MiddleStatement`;
* **the endpoint step** (common): "Now adjoin a finite terminal endpoint of either prefix while the other stop is
  strict. If it misses the other prefix, compact clearance and W4 extend an earlier ordered pair through that endpoint.
  If it meets the other prefix, it is an exterior original-real point, and G15 supplies actual proper completions
  through it, with any surviving outer continuation included. Adjoin the other finite endpoint in the same way."
  Named `TerminalEndpointStatement`.

Main results: **`sb1Statement_of_inputs`** (`SB1Statement` from W5, `SB1MiddleStatement` and
`TerminalEndpointStatement`) and **`s6Statement_of_inputs`** (`S6Statement` from W5, `S6MiddleStatement` and
`TerminalEndpointStatement`).
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
open QuantumZipper (chiC H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE

namespace Theorem14

namespace SB

/-- **Terminal contacts are exterior original-real points**: whenever a finite terminal endpoint of either available
prefix (`a = ζ₁` or `c = ζ₂`) is a common point `α(a) = β(c)`, it is a real point outside the closed seed interval
`[x₂, x₁]`. -/
def TerminalContactsExterior (α : ℝ≥0 → ℂ) (ζ₁ : ℝ≥0∞) (β : ℝ≥0 → ℂ) (ζ₂ : ℝ≥0∞) (x₂ x₁ : ℝ) : Prop :=
  ∀ a c : ℝ≥0, (a : ℝ≥0∞) ≤ ζ₁ → (c : ℝ≥0∞) ≤ ζ₂ → ((a : ℝ≥0∞) = ζ₁ ∨ (c : ℝ≥0∞) = ζ₂) → α a = β c →
    ∃ x : ℝ, α a = x ∧ (x < x₂ ∨ x₁ < x)

/-- **The terminal-endpoint step of S6 and SB1** (supplement pp. 583–584 and p. 630; uses W4's clearance extension
and G15's actual proper completions through an exterior real contact): for the two canonical constant-angle flows of
W5 (`x₂ ≤ x₁`, `θ₁ < θ₂`), almost surely, if every pair of strict prefixes has the ordered proper completions of W0
and every terminal contact is an exterior original-real point, then every pair of finite available prefixes,
including terminal ones, has them. -/
def TerminalEndpointStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ → θ₁ < θ₂ →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
      ∀ᵐ ω ∂P, (∀ a c : ℝ≥0, (a : ℝ≥0∞) < ζ₁ ω → (c : ℝ≥0∞) < ζ₂ ω →
          HasOrderedProperCompletions (η₁ ω) a (η₂ ω) c) →
        TerminalContactsExterior (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) x₂ x₁ →
        ∀ a c : ℝ≥0, (a : ℝ≥0∞) ≤ ζ₁ ω → (c : ℝ≥0∞) ≤ ζ₂ ω → HasOrderedProperCompletions (η₁ ω) a (η₂ ω) c

/-- **SB1's middle exclusion** (supplement p. 630), in the setting of `SB1Statement`: almost surely every terminal
contact of the lower flow (from `v`, angle `−π/2`) and the upper flow (from `u < v`, angle `ψ`) is an exterior
original-real point. -/
def SB1MiddleStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ u v ψ : ℝ, u < v → -(Real.pi / 2) < ψ →
      (∀ x ∈ Ioo u v, x ∉ jumps → -2 < Sec4.cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
      (∀ x ∈ Ioo u v, x ∉ jumps → -2 < Sec4.cumWeightRight κ (b x + ψ * chiC κ) ∨
        κ / 2 - 2 ≤ Sec4.cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
    ∀ (ηL ηU : Ω → ℝ≥0 → ℂ) (ζL ζU : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps v (-(Real.pi / 2)) P h ηL ζL → IsFlowLine κ b jumps u ψ P h ηU ζU →
      (∀ᵐ ω ∂P, 0 < ζL ω) → (∀ᵐ ω ∂P, 0 < ζU ω) →
      ∀ᵐ ω ∂P, TerminalContactsExterior (ηL ω) (ζL ω) (ηU ω) (ζU ω) u v

/-- **S6's middle exclusion** (supplement p. 583: "no genuine continuation threshold can occur in the closed interval
between the seeds; opposite-seed polarity supplies the two endpoint exclusions"), in the setting of `S6Statement`:
almost surely every terminal contact is an exterior original-real point. -/
def S6MiddleStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ x₁ x₂ θ₁ θ₂ : ℝ, x₂ ≤ x₁ → θ₁ < θ₂ →
      (∀ x ∈ Ioo x₂ x₁, x ∉ jumps → -2 < Sec4.cumWeightLeft κ (b x + θ₁ * chiC κ)) →
      (∀ x ∈ Ioo x₂ x₁, x ∉ jumps → -2 < Sec4.cumWeightRight κ (b x + θ₂ * chiC κ)) →
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (η₁ η₂ : Ω → ℝ≥0 → ℂ) (ζ₁ ζ₂ : Ω → ℝ≥0∞),
      IsFlowLine κ b jumps x₁ θ₁ P h η₁ ζ₁ → IsFlowLine κ b jumps x₂ θ₂ P h η₂ ζ₂ →
      (∀ᵐ ω ∂P, 0 < ζ₁ ω) → (∀ᵐ ω ∂P, 0 < ζ₂ ω) →
      ∀ᵐ ω ∂P, TerminalContactsExterior (η₁ ω) (ζ₁ ω) (η₂ ω) (ζ₂ ω) x₂ x₁

/-- **Lemma SB1 from W5, its middle exclusion and the terminal-endpoint step** (supplement p. 630: "W5 supplies the
strict-prefix assertion. [...] This is the endpoint proof of S6 with every possible middle terminal contact excluded
by the displayed hybrid condition."). -/
theorem sb1Statement_of_inputs (hW5 : Theorem15.W5Statement.{u}) (hM : SB1MiddleStatement.{u})
    (hE : TerminalEndpointStatement.{u}) : SB1Statement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ P _ h hh u v ψ huv hψ hL hH ηL ηU ζL ζU hηL hηU hζL hζU
  filter_upwards [hW5 κ hκ hκ4 b jumps hb v u (-(Real.pi / 2)) ψ huv.le hψ P h hh ηL ηU ζL ζU hηL hηU,
    hM κ hκ hκ4 b jumps hb P h hh u v ψ huv hψ hL hH ηL ηU ζL ζU hηL hηU hζL hζU,
    hE κ hκ hκ4 b jumps hb v u (-(Real.pi / 2)) ψ huv.le hψ P h hh ηL ηU ζL ζU hηL hηU] with ω h5 hm he
  exact he h5 hm

/-- **Lemma S6 from W5, its middle exclusion and the terminal-endpoint step** (supplement pp. 583–584). -/
theorem s6Statement_of_inputs (hW5 : Theorem15.W5Statement.{u}) (hM : S6MiddleStatement.{u})
    (hE : TerminalEndpointStatement.{u}) : S6Statement.{u} := by
  intro κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ hL hR Ω _ P _ h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ hζ₁ hζ₂
  filter_upwards [hW5 κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂,
    hM κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ hL hR P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂ hζ₁ hζ₂,
    hE κ hκ hκ4 b jumps hb x₁ x₂ θ₁ θ₂ hx hθ P h hh η₁ η₂ ζ₁ ζ₂ hη₁ hη₂] with ω h5 hm he
  exact he h5 hm

end SB

end Theorem14

end InteractingSLE
