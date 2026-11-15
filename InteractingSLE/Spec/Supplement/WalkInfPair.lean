/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkBdryPair
import InteractingSLE.Spec.Supplement.GW4BarrierSelf

/-!
# Theorem 1.4's walk leaves: the common-arc geometry given the contact order

Packet PROVE-T14-WALKINF. PROVE-T14-WALKBDRY's named input `WalkBdry.WalkPairGeomStatement` asks, at a nondegenerate
common continuum of an ordinary piece of `R` and one of `L`, for **left** side points of both prefixes joined by
an increasing transition. That holds only when the two walks traverse the common arc in the same direction —
Theorem GW4's "Every common contact is ordered the same way on the two walks"
(`GW4BarrierSelf.WalkContactOrderRegStatement`, derived in the wiring from other leaves, independently of the pair
clause). Its hypotheses are among those of `WalkPairGeomStatement`, so:

* **`WalkPairGeomCOStatement`**: `WalkPairGeomStatement` with the pathwise facts the common-arc geometry uses as an
  almost sure hypothesis (`WalkPairPathFacts`: proper parametrizations of both walks from `0`, and the contact order
  for every pair of complete simple flow parametrizations) — the remaining pathwise input;
* **`walkPairGeomStatement_of_co`**: `WalkPairGeomStatement` from the contact order, the two proper-parametrization
  statements and `WalkPairGeomCOStatement`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology TopologicalSpace Complex Metric
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (TestOn DistOn)

universe u

namespace InteractingSLE.Theorem14.WalkInf

open WalkLaw GW3Between LocalSets WalkMean WalkBdry

/-- **The pathwise facts of a common-arc argument at one sample**: both walks have proper parametrizations from `0`, and
every pair of complete simple flow parametrizations of the two walks orders their common contacts the same way. -/
def WalkPairPathFacts (κ : ℝ) (b : ℝ → ℝ) (jumps : Finset ℝ) {Ω : Type*} (E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞)
    (ω : Ω) : Prop :=
  (∃ γ : ℝ≥0 → ℂ, Supp9B.IsProperCurve γ ∧ γ 0 = 0 ∧
    range γ = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω)) ∧
  (∃ γ : ℝ≥0 → ℂ, Supp9B.IsProperCurve γ ∧ γ 0 = 0 ∧
    range γ = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
      (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω)) ∧
  ∀ αR αL : ℝ≥0 → ℂ,
    range αR = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω) →
    range αL = ExplState.physSet κ b jumps (boundaryWalkSpec b jumps (Real.pi / 2) false)
      (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω) →
    GB11.IsCompleteSimpleFlow αR → GB11.IsCompleteSimpleFlow αL →
      ∀ s s' t t' : ℝ≥0, αR s = αL t → αR s' = αL t' → (s < s' ↔ t < t')

/-- **Named input: the local geometry of a common arc of the two walks, given the contact order** (Theorem GW4, proof,
p. 637: "Every common contact is ordered the same way on the two walks … An interior common open subarc is impossible";
`WalkBdry.WalkPairGeomStatement` with the pathwise facts `WalkPairPathFacts` as an almost sure hypothesis). -/
def WalkPairGeomCOStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ), IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (h : Ω → DistOn upperHalfPlaneOpens), IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞), IsCenteredCounterflowDriver κ P h W' ζ' →
      (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      (∀ (spec : ExplSpec) (k : ℕ) (ω : Ω), Exist.Staged.IsRegularDriver (E spec k ω)) →
      (∀ᵐ ω ∂P, WalkPairPathFacts κ b jumps E ω) →
      ∀ᵐ ω ∂P, ∀ pR ∈ (walkRuns κ b jumps E ω).1.1, ∀ pL ∈ (walkRuns κ b jumps E ω).2.1,
        ∀ S ⊆ closure (pR.1.tipSet pR.2.1 pR.2.2) ∩ closure (pL.1.tipSet pL.2.1 pL.2.2),
          IsPreconnected S → ¬ S.Subsingleton →
          ∃ (preR postR preL postL : List Piece) (pcR pcL : Piece) (τR τL : ℚ≥0) (yR yL : ℝ) (p : ℂ)
            (r : ℝ) (n : ℤ),
            (walkRuns κ b jumps E ω).1.1 = preR ++ pcR :: postR ∧ (((τR : ℝ≥0)) : ℝ≥0∞) < pcR.2.2 ∧
            IsLeftSidePt pcR τR yR ∧
            (walkRuns κ b jumps E ω).2.1 = preL ++ pcL :: postL ∧ (((τL : ℝ≥0)) : ℝ≥0∞) < pcL.2.2 ∧
            IsLeftSidePt pcL τL yL ∧
            Tendsto (prefixChart pcR τR).2.1 (𝓝[H] (yR : ℂ)) (𝓝 p) ∧
            Tendsto (prefixChart pcL τL).2.1 (𝓝[H] (yL : ℂ)) (𝓝 p) ∧
            p ∈ wsetOf (walkRuns κ b jumps E ω).1 ∩ wsetOf (walkRuns κ b jumps E ω).2 ∧ 0 < r ∧
            wsetOf (walkRuns κ b jumps E ω).1 ∩ ball p r ⊆ prefixSet preR pcR τR ∧
            wsetOf (walkRuns κ b jumps E ω).2 ∩ ball p r ⊆ prefixSet preL pcL τL ∧
            wsetOf (walkRuns κ b jumps E ω).1 ∩ ball p r = wsetOf (walkRuns κ b jumps E ω).2 ∩ ball p r ∧
            (∀ᶠ ζ in 𝓝[H] (yR : ℂ), (prefixChart pcR τR).2.1 ζ ∈
              H \ (wsetOf (walkRuns κ b jumps E ω).1 ∪ wsetOf (walkRuns κ b jumps E ω).2)) ∧
            Tendsto (fun ζ => (prefixChart pcL τL).1 ((prefixChart pcR τR).2.1 ζ)) (𝓝[H] (yR : ℂ))
              (𝓝 (yL : ℂ)) ∧
            (∀ᶠ ζ in 𝓝[H] (yR : ℂ), (prefixChart pcL τL).1 ((prefixChart pcR τR).2.1 ζ) ∈ H ∧
              (prefixChart pcL τL).2.1 ((prefixChart pcL τL).1 ((prefixChart pcR τR).2.1 ζ)) =
                (prefixChart pcR τR).2.1 ζ) ∧
            Tendsto (fun ζ => (prefixChart pcL τL).2.2 ((prefixChart pcR τR).2.1 ζ) -
                (prefixChart pcR τR).2.2 ((prefixChart pcR τR).2.1 ζ)) (𝓝[H] (yR : ℂ))
              (𝓝 (2 * Real.pi * n))


/-- **`WalkBdry.WalkPairGeomStatement` from the contact order** (`GW4BarrierSelf.WalkContactOrderRegStatement`), the
proper parametrizations of the two walks and `WalkPairGeomCOStatement`. -/
theorem walkPairGeomStatement_of_co (hCO : GW4BarrierSelf.WalkContactOrderRegStatement.{u})
    (hPR : WalkCont.RightWalkProperRegStatement.{u}) (hPL : GW3SidedProof.LeftWalkProperRegStatement.{u})
    (hPGco : WalkPairGeomCOStatement.{u}) : WalkPairGeomStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hR hreg
  refine hPGco κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hR hreg ?_
  filter_upwards [hPR κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hR,
    hPL κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hR,
    hCO κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hR] with ω h1 h2 h3
  exact ⟨h1, h2, h3⟩

end InteractingSLE.Theorem14.WalkInf
