/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.SB2Remainder

/-!
# Lemma SB3: the stage induction and the final topology

Packet PROVE-T14-SB2. The proof of Lemma SB3 (supplement pp. 633–634, `source/spec/p625-671.md` L163–L171) has two
parts:

* the **stage induction**: "The induction gives S1 for every finite actual prefix of the proper lower walk" (from W5,
  S6, SB1, SB2(1) and S5 over the finitely many stages; named here `SB3InductionStatement`);
* the **final certificate** (deterministic): "A point of `b` on its open right side would give a finite crossing or
  initial-germ certificate between a finite upper prefix and an interior-in-parameter compact subarc of `B`. In a small
  Jordan collar of those retained subarcs any proper completion of the upper prefix has the same local sides [...].
  The lower subarc then has points on both sides of that completion, contradicting S1." Named here
  `SB3TopologyStatement`, for a proper simple parametrization `γ` of the walk.

The walk is "an actual finite simple proper concatenation" (GW1, p. 630); its parametrization is the named statement
`GW1ParamStatement`.

Main result: **`sb3Statement_of_inputs`**: `SB3Statement` from `GW1ParamStatement`, `SB3InductionStatement` and
`SB3TopologyStatement` (the continuity and seed of the upper path come from the frozen `IsFlowLine`).
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

/-- **SB3's final certificate** (deterministic; supplement p. 634): let `γ` be a proper simple curve in `closure ℍ`
from `0` (the completed lower walk), and `η` a path from `u ≤ 0`, continuous on its available range `[0, ζ]`, such that
S1 holds for every finite prefix `γ([0, s])` of the walk, with the bridge `[u, 0]` adjoined, and every available prefix
of `η`. Then the whole available range of `η` misses the open right side of the walk. -/
def SB3TopologyStatement : Prop :=
  ∀ (γ η : ℝ≥0 → ℂ) (ζ : ℝ≥0∞) (u : ℝ), Supp9B.IsProperCurve γ → γ 0 = 0 → u ≤ 0 → η 0 = u →
    ContinuousOn η {t | (t : ℝ≥0∞) ≤ ζ} →
    (∀ s a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ → IsOneSided (γ '' Icc 0 s ∪ ((↑) : ℝ → ℂ) '' Icc u 0) η a) →
    η '' {t | (t : ℝ≥0∞) ≤ ζ} ∩ rightSideOf (range γ) = ∅

/-- **GW1: the completed lower walk is a proper simple curve** (supplement p. 618 and p. 630: "an actual finite simple
proper concatenation [...] The finite construction and its properness are those of GW1"), in the setting of
Theorem 1.4: almost surely the physical set of the lower walk is the range of a proper simple curve in `closure ℍ`
from `0`. -/
def GW1ParamStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      ∀ᵐ ω ∂P, ∃ γ : ℝ≥0 → ℂ, Supp9B.IsProperCurve γ ∧ γ 0 = 0 ∧ range γ = lowerWalkSet κ b jumps E ω

/-- **SB3's stage induction** (supplement pp. 633–634: "Induct on the finite ordinary stages of the lower walk. The
induction assertion is S1: each retained lower prefix lies on the closed right of a proper completion of every
available upper prefix. [...] The induction gives S1 for every finite actual prefix of the proper lower walk."), in
the setting of `SB3Statement`: almost surely, for every proper simple parametrization `γ` of the completed lower walk
from `0`, S1 holds for every finite prefix `γ([0, s])` (with the bridge `[u, 0]`) and every available prefix of the
upper flow `η`. -/
def SB3InductionStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
    ∀ u ψ : ℝ, u ≤ 0 → -(Real.pi / 2) < ψ →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < Sec4.cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
      (∀ x ∈ Ioo u 0, x ∉ jumps → -2 < Sec4.cumWeightRight κ (b x + ψ * chiC κ) ∨
        κ / 2 - 2 ≤ Sec4.cumWeightLeft κ (b x + -(Real.pi / 2) * chiC κ)) →
    ∀ (η : Ω → ℝ≥0 → ℂ) (ζ : Ω → ℝ≥0∞), IsFlowLine κ b jumps u ψ P h η ζ → (∀ᵐ ω ∂P, 0 < ζ ω) →
      ∀ᵐ ω ∂P, ∀ γ : ℝ≥0 → ℂ, Supp9B.IsProperCurve γ → γ 0 = 0 → range γ = lowerWalkSet κ b jumps E ω →
        ∀ s a : ℝ≥0, (a : ℝ≥0∞) ≤ ζ ω → IsOneSided (γ '' Icc 0 s ∪ ((↑) : ℝ → ℂ) '' Icc u 0) (η ω) a

/-- The seed and the continuity of a flow line's path, from its generating trace. -/
theorem IsFlowLine.ae_seed_continuousOn {κ : ℝ} {b : ℝ → ℝ} {jumps : Finset ℝ} {x θ : ℝ} {Ω : Type*}
    [MeasurableSpace Ω] {P : Measure Ω} {h : Ω → DistOn upperHalfPlaneOpens} {η : Ω → ℝ≥0 → ℂ} {ζ : Ω → ℝ≥0∞}
    (hη : IsFlowLine κ b jumps x θ P h η ζ) :
    ∀ᵐ ω ∂P, η ω 0 = x ∧ ContinuousOn (η ω) {t | (t : ℝ≥0∞) ≤ ζ ω} := by
  obtain ⟨-, -, W, -, -, -, -, -, htr⟩ := hη
  filter_upwards [htr] with ω hω
  refine ⟨sub_eq_zero.1 hω.1, ?_⟩
  have e : η ω = fun t => (η ω t - x) + x := funext fun t => (sub_add_cancel _ _).symm
  rw [e]
  exact hω.2.1.add continuousOn_const

/-- **Lemma SB3 from its stage induction and its final certificate** (supplement pp. 633–634), with GW1's proper
simple parametrization of the completed lower walk. -/
theorem sb3Statement_of_inputs (hP : GW1ParamStatement.{u}) (hI : SB3InductionStatement.{u})
    (hT : SB3TopologyStatement) : SB3Statement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE u ψ hu hψ hL hH η ζ hη hζ
  filter_upwards [hP κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE,
    hI κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE u ψ hu hψ hL hH η ζ hη hζ,
    IsFlowLine.ae_seed_continuousOn hη] with ω ⟨γ, hγ, hγ0, hγR⟩ hS ⟨h0, hc⟩
  have := hT γ (η ω) (ζ ω) u hγ hγ0 hu h0 hc (hS γ hγ hγ0 hγR)
  rw [hγR] at this
  exact this

end SB

end Theorem14

end InteractingSLE
