/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkWdCore
import InteractingSLE.Spec.Supplement.WalkWordsChron
import InteractingSLE.Spec.Supplement.WalkWordsJunction
import InteractingSLE.Spec.Supplement.WalkIntRunChronHistory
import InteractingSLE.Spec.Supplement.GW3LawJointUnion

/-!
# Theorem 1.4's walk leaf: the finite-word matches `hMatch`, almost surely

Packet PROVE-WALK-WORDS2. **`WalkFiniteMatchStatement`** is, verbatim, the binder `hMatch` of PROVE-T14-WALKINT's
`WalkIntBoundCut.walkNormChartLocStatement_of_finite_matches` (which gives `WalkNorm.WalkNormChartLocStatement`, the
`hNL` of `Wire.theorem14Statement_assembled2`, from Theorem 1.3 and `hMatch`): almost surely, for every full proper
parametrization `α`, `β` of the two walks and every component `C` between them, a component chart with a finite word,
a finite exceptional set, and at every other real point a prefix match (with its `RetainedPair` and, for bounded `C`,
its `BeforeExit` data) or a real match.

**`walkFiniteMatchStatement_of_inputs`** proves it from Theorem 1.3 (both universes), the five named inputs of
`GW3SidedProof.gw3GeometryRegStatement_of_walks` (`hPR hPL hA hF hNR`, as in PROVE-WALK-WORDS), and two named inputs:

* **`WalkTouchMatchStatement`**: the controlled prefix match (`IsControlledMatch`) at a positive (negative) real point
  whose landing is a **real** ordinary point of the right (left) walk off its piece ends — a point where a recorded
  piece touches `ℝ` at a positive own time before its stop. The central matches (landings in `ℍ`) are proved
  (`WalkWd.exists_controlledMatch_right` / `_left`); PROVE-WALK-WORDS' fibre lemma and side identification assume the
  trace point in `ℍ`, and a boundary-hitting piece can touch `ℝ` at infinitely many points of a component's boundary
  arc, so these points cannot be put into the finite exceptional set.
* **`WalkLiveStatement`**: if there is a component between the walks, each walk has a live recorded piece (positive
  stop). `hMatch` asks for a `RetainedPair` (a live prefix of each walk) at all but finitely many points, so it fails
  when one walk has no live piece (every launch of that walk dies at once and the wall is real); such samples need a
  one-walk variant of PROVE-T14-WALKINT's consumer.

Everything else is proved: the landings avoid the other wall (`WalkWd.pocket_landing_facts`), the closing contact of a
bounded component, the controlled central matches, the empty live prefixes (`exists_walkPrefix_raw_eq_empty`), the raw
initial segments (PROVE-T14-WALKINT's `exists_raw_initial_segment_of_run`, from Theorem 1.3), the real matches, the
word (`walkComponentWordStatement_of_walks`) and the finiteness of the exceptional set.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology Metric Complex
open scoped NNReal ENNReal
open QuantumZipper (H Hbar)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.WalkWd

open Exist WalkBdry WalkMean WalkNorm WalkInf WalkWords WalkIntFill WalkIntFiber WalkIntActive
open GW1WalkFinish GW1WalkChain

/-- **The finite-word matches** (verbatim the binder `hMatch` of `WalkIntBoundCut.walkNormChartLocStatement_of_finite_
matches`; see the module docstring). -/
def WalkFiniteMatchStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ),
    IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens),
      IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞),
      IsCenteredCounterflowDriver κ P h W' ζ' → (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      (∀ (spec : ExplSpec) (k : ℕ) (ω : Ω), Exist.Staged.IsRegularDriver (E spec k ω)) →
      (∀ᵐ ω ∂P, WalkBetweenFacts κ b jumps E ω) →
      ∀ᵐ ω ∂P, ∀ α β : ℝ≥0 → ℂ,
        Supp9B.IsProperCurve α → Supp9B.IsProperCurve β → α 0 = 0 → β 0 = 0 →
        range α = physOf (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (walkRuns κ b jumps E ω).1 →
        range β = physOf (boundaryWalkSpec b jumps (Real.pi / 2) false) (walkRuns κ b jumps E ω).2 →
        ∀ C ∈ betweenComponents
          (physOf (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (walkRuns κ b jumps E ω).1)
          (physOf (boundaryWalkSpec b jumps (Real.pi / 2) false) (walkRuns κ b jumps E ω).2),
        ∃ (t : Chart × (ℝ → ℝ) × Finset ℝ) (F : Set ℝ), F.Finite ∧
          IsComponentChart
            (physOf (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (walkRuns κ b jumps E ω).1)
            (physOf (boundaryWalkSpec b jumps (Real.pi / 2) false) (walkRuns κ b jumps E ω).2) C t.1 ∧
          IsPiecewiseConstantBoundaryData t.2.1 t.2.2 ∧
          IsComponentBoundaryData κ b (ordOf (walkRuns κ b jumps E ω).1)
            (ordOf (walkRuns κ b jumps E ω).2) t.1.2.1 t.2.1 t.2.2 ∧
          ∀ x : ℝ, x ∉ F →
            (0 < x → ∃ J : RetainedPair (walkRuns κ b jumps E ω).1 (walkRuns κ b jumps E ω).2,
              (((Bornology.IsBounded (t.1.dom : Set ℂ) →
                  Nonempty (BeforeExit J (t.1.dom : Set ℂ) α β)) ∧
                IsPiecePhysicalMatch (walkRuns κ b jumps E ω).1 (walkRuns κ b jumps E ω).2
                  true t.1 J.model x ∧ t.2.1 x = -bigLambda κ) ∨
                WalkIntGerm.IsRealIncidentMatch (walkRuns κ b jumps E ω).1
                  (walkRuns κ b jumps E ω).2 b jumps t.1 J.model x (t.2.1 x))) ∧
            (x < 0 → ∃ J : RetainedPair (walkRuns κ b jumps E ω).1 (walkRuns κ b jumps E ω).2,
              (((Bornology.IsBounded (t.1.dom : Set ℂ) →
                  Nonempty (BeforeExit J (t.1.dom : Set ℂ) α β)) ∧
                IsPiecePhysicalMatch (walkRuns κ b jumps E ω).2 (walkRuns κ b jumps E ω).1
                  false t.1 J.model x ∧ t.2.1 x = bigLambda κ) ∨
                WalkIntGerm.IsRealIncidentMatch (walkRuns κ b jumps E ω).1
                  (walkRuns κ b jumps E ω).2 b jumps t.1 J.model x (t.2.1 x)))

/-- **The finite-word matches on the live event**: `WalkFiniteMatchStatement` for the samples on which each walk has a
recorded piece with positive stop (proved from the inputs without `WalkLiveStatement`). -/
def WalkFiniteMatchOnLiveStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ),
    IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens),
      IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞),
      IsCenteredCounterflowDriver κ P h W' ζ' → (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      (∀ (spec : ExplSpec) (k : ℕ) (ω : Ω), Exist.Staged.IsRegularDriver (E spec k ω)) →
      (∀ᵐ ω ∂P, WalkBetweenFacts κ b jumps E ω) →
      ∀ᵐ ω ∂P, (∃ pc ∈ (walkRuns κ b jumps E ω).1.1, (0 : ℝ≥0∞) < pc.2.2) →
        (∃ pc ∈ (walkRuns κ b jumps E ω).2.1, (0 : ℝ≥0∞) < pc.2.2) → ∀ α β : ℝ≥0 → ℂ,
        Supp9B.IsProperCurve α → Supp9B.IsProperCurve β → α 0 = 0 → β 0 = 0 →
        range α = physOf (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (walkRuns κ b jumps E ω).1 →
        range β = physOf (boundaryWalkSpec b jumps (Real.pi / 2) false) (walkRuns κ b jumps E ω).2 →
        ∀ C ∈ betweenComponents
          (physOf (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (walkRuns κ b jumps E ω).1)
          (physOf (boundaryWalkSpec b jumps (Real.pi / 2) false) (walkRuns κ b jumps E ω).2),
        ∃ (t : Chart × (ℝ → ℝ) × Finset ℝ) (F : Set ℝ), F.Finite ∧
          IsComponentChart
            (physOf (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (walkRuns κ b jumps E ω).1)
            (physOf (boundaryWalkSpec b jumps (Real.pi / 2) false) (walkRuns κ b jumps E ω).2) C t.1 ∧
          IsPiecewiseConstantBoundaryData t.2.1 t.2.2 ∧
          IsComponentBoundaryData κ b (ordOf (walkRuns κ b jumps E ω).1)
            (ordOf (walkRuns κ b jumps E ω).2) t.1.2.1 t.2.1 t.2.2 ∧
          ∀ x : ℝ, x ∉ F →
            (0 < x → ∃ J : RetainedPair (walkRuns κ b jumps E ω).1 (walkRuns κ b jumps E ω).2,
              (((Bornology.IsBounded (t.1.dom : Set ℂ) →
                  Nonempty (BeforeExit J (t.1.dom : Set ℂ) α β)) ∧
                IsPiecePhysicalMatch (walkRuns κ b jumps E ω).1 (walkRuns κ b jumps E ω).2
                  true t.1 J.model x ∧ t.2.1 x = -bigLambda κ) ∨
                WalkIntGerm.IsRealIncidentMatch (walkRuns κ b jumps E ω).1
                  (walkRuns κ b jumps E ω).2 b jumps t.1 J.model x (t.2.1 x))) ∧
            (x < 0 → ∃ J : RetainedPair (walkRuns κ b jumps E ω).1 (walkRuns κ b jumps E ω).2,
              (((Bornology.IsBounded (t.1.dom : Set ℂ) →
                  Nonempty (BeforeExit J (t.1.dom : Set ℂ) α β)) ∧
                IsPiecePhysicalMatch (walkRuns κ b jumps E ω).2 (walkRuns κ b jumps E ω).1
                  false t.1 J.model x ∧ t.2.1 x = bigLambda κ) ∨
                WalkIntGerm.IsRealIncidentMatch (walkRuns κ b jumps E ω).1
                  (walkRuns κ b jumps E ω).2 b jumps t.1 J.model x (t.2.1 x)))

/-- **Named input: controlled matches at the real touch points of the pieces** (see the module docstring). -/
def WalkTouchMatchStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ),
    IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens),
      IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞),
      IsCenteredCounterflowDriver κ P h W' ζ' → (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      (∀ (spec : ExplSpec) (k : ℕ) (ω : Ω), Exist.Staged.IsRegularDriver (E spec k ω)) →
      (∀ᵐ ω ∂P, WalkBetweenFacts κ b jumps E ω) →
      ∀ᵐ ω ∂P, ∀ C ∈ betweenComponents
        (physOf (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (walkRuns κ b jumps E ω).1)
        (physOf (boundaryWalkSpec b jumps (Real.pi / 2) false) (walkRuns κ b jumps E ω).2),
        ∀ c : Chart, IsComponentChart
          (physOf (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (walkRuns κ b jumps E ω).1)
          (physOf (boundaryWalkSpec b jumps (Real.pi / 2) false) (walkRuns κ b jumps E ω).2) C c →
        (∀ (x : ℝ) (p : ℂ), 0 < x → Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 p) → p.im = 0 →
          p ∈ ordOf (walkRuns κ b jumps E ω).1 → p ∉ pieceEnds (walkRuns κ b jumps E ω).1.1 →
          IsControlledMatch (walkRuns κ b jumps E ω).1 (walkRuns κ b jumps E ω).2 true c x p) ∧
        (∀ (x : ℝ) (p : ℂ), x < 0 → Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 p) → p.im = 0 →
          p ∈ ordOf (walkRuns κ b jumps E ω).2 → p ∉ pieceEnds (walkRuns κ b jumps E ω).2.1 →
          IsControlledMatch (walkRuns κ b jumps E ω).2 (walkRuns κ b jumps E ω).1 false c x p)

/-- **Named input: live walks** — if there is a component between the walks, each walk has a recorded piece with
positive stop (see the module docstring). -/
def WalkLiveStatement : Prop :=
  ∀ κ : ℝ, 0 < κ → κ < 4 → ∀ (b : ℝ → ℝ) (jumps : Finset ℝ),
    IsPiecewiseConstantBoundaryData b jumps →
    ∀ {Ω : Type u} [MeasurableSpace Ω] [StandardBorelSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P] (h : Ω → DistOn upperHalfPlaneOpens),
      IsGFFWithBoundaryData P h b jumps →
    ∀ (W' : ℝ≥0 → Ω → ℝ) (ζ' : Ω → ℝ≥0∞),
      IsCenteredCounterflowDriver κ P h W' ζ' → (∀ᵐ ω ∂P, ζ' ω = ⊤) →
    ∀ E : ExplSpec → ℕ → Ω → (ℝ≥0 → ℝ) × ℝ≥0∞,
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        IsStagedHistory κ b jumps P h spec (E spec)) →
      (∀ spec : ExplSpec, IsBoundaryContinuedProgram spec.2.2 →
        StagedPiecesRegular κ b jumps P spec (E spec)) →
      (∀ (spec : ExplSpec) (k : ℕ) (ω : Ω), Exist.Staged.IsRegularDriver (E spec k ω)) →
      (∀ᵐ ω ∂P, WalkBetweenFacts κ b jumps E ω) →
      ∀ᵐ ω ∂P, (betweenComponents
        (physOf (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (walkRuns κ b jumps E ω).1)
        (physOf (boundaryWalkSpec b jumps (Real.pi / 2) false) (walkRuns κ b jumps E ω).2)).Nonempty →
        (∃ pc ∈ (walkRuns κ b jumps E ω).1.1, (0 : ℝ≥0∞) < pc.2.2) ∧
          ∃ pc ∈ (walkRuns κ b jumps E ω).2.1, (0 : ℝ≥0∞) < pc.2.2

/-- **`WalkFiniteMatchOnLiveStatement`** from Theorem 1.3, the five named inputs of
`GW3SidedProof.gw3GeometryRegStatement_of_walks`, and the named input `WalkTouchMatchStatement`. -/
theorem walkFiniteMatchOnLiveStatement_of_inputs (hT13 : Theorem13Statement.{u})
    (hT13₀ : Theorem13Statement.{0}) (hPR : WalkCont.RightWalkProperRegStatement.{u})
    (hPL : GW3SidedProof.LeftWalkProperRegStatement.{u}) (hA : GW2aContainmentStatement.{u})
    (hF : SB.SBFrontierRegStatement.{u}) (hNR : GW3SidedProof.RightWalkNegRealRegStatement.{u})
    (hTouch : WalkTouchMatchStatement.{u}) : WalkFiniteMatchOnLiveStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hR hreg hfacts
  have hpi := Real.pi_pos
  have hRR := hR _ (GW1X.isBoundaryContinuedProgram_walkR b jumps)
  have hRL := hR _ (GW1X.isBoundaryContinuedProgram_walkL b jumps)
  have hD4 := GW1WalkExit.walkD4GeometryStatement_of_theorem13 hT13 hT13₀
  have hTip := walkTipCoordinatesStatement_of_d4 hT13 hD4
  have hClear := walkConnectorClearanceStatement_of_d4_and_exit
    (GW1WalkExit.walkExitClassificationStatement_of_theorem13 hT13₀) hD4
  filter_upwards [hfacts, hRR, hRL, hF κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hR,
    hA κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE _
      (isBoundaryContinuedProgram_boundaryWalkSpec b jumps (θ := -(Real.pi / 2)) ⟨le_rfl, by linarith⟩ true),
    hA κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE _
      (isBoundaryContinuedProgram_boundaryWalkSpec b jumps (θ := Real.pi / 2) ⟨by linarith, le_rfl⟩ false),
    hTip κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg true,
    hTip κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg false,
    hClear κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg true,
    hClear κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg false,
    walkComponentOrientationStatement_of_theorem13 hT13 hT13₀ hPR hPL hA hF hNR κ hκ hκ4 b jumps hb P h hh W' ζ'
      hcf hζ' E hE hR hreg hfacts,
    walkComponentWordStatement_of_walks hPR hPL hA hF hNR κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hR hreg
      hfacts,
    walkComponentLandingStatement_of_walks hPR hPL hA hF hNR κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hR hreg
      hfacts,
    hTouch κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hR hreg hfacts]
    with ω hf hωR hωL hS hAR hAL hTipR hTipL hClR hClL hor hwd hld hto
  intro hlR hlL α β hα hβ hα0 hβ0 hrR hrL C hC
  have hfα : GB11.IsCompleteSimpleFlow α := ⟨hα.1, hα.2.1, hα0, fun t => hα.2.2.1 t, hα.2.2.2⟩
  have hfβ : GB11.IsCompleteSimpleFlow β := ⟨hβ.1, hβ.2.1, hβ0, fun t => hβ.2.2.1 t, hβ.2.2.2⟩
  have hco := hf.1.2.2 α β hrR hrL hfα hfβ
  -- the pocket shape of the two walls
  have hno : ∀ a b' : ℝ≥0, a < b' → ¬ α '' Icc a b' ⊆ range β := by
    intro a b' hab hsub
    have hS' : α '' Icc a b' ⊆ physOf (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (walkRuns κ b jumps E ω).1 ∩
        physOf (boundaryWalkSpec b jumps (Real.pi / 2) false) (walkRuns κ b jumps E ω).2 :=
      fun z hz => ⟨hrR ▸ image_subset_range _ _ hz, hrL ▸ hsub hz⟩
    have hsing := hf.2.2.1 _ hS' (isPreconnected_Icc.image _ hfα.1.continuousOn)
    have he := hsing ⟨a, ⟨le_rfl, hab.le⟩, rfl⟩ ⟨b', ⟨hab.le, le_rfl⟩, rfl⟩
    exact absurd (hfα.2.1 he) hab.ne
  have hdL : Disjoint (range β) (rightSideOf (range α)) := by
    rw [hrR, hrL, Set.disjoint_left]
    intro z hzL hzR
    exact eq_empty_iff_forall_notMem.1 hS.1 z ⟨hAL hzL, hzR⟩
  have hdR : Disjoint (range α) (leftSideOf (range β)) := by
    rw [hrR, hrL, Set.disjoint_left]
    intro z hzR hzL
    exact eq_empty_iff_forall_notMem.1 hS.2 z ⟨hAR hzR, hzL⟩
  have hgeo : ∀ C' ∈ betweenComponents (range α) (range β),
      GW3.IsTwoArcJordanComponent (range α) (range β) C' ∨ GW3.HasOrientedUniformizer (range α) (range β) C' := by
    rw [hrR, hrL]; exact hf.2.2.2
  have hW := PocketMirror.pocketShapeDetStatement α β hfα hfβ hco hno hdL hdR hgeo
  -- the component chart
  obtain ⟨c, hc⟩ := GW3.exists_isComponentChart_of_geometry (hf.2.2.2 C hC)
  have hCoH : IsOpen C ∧ C ⊆ H := by
    rcases hf.2.2.2 C hC with hJ | hU
    · exact ⟨hJ.1, hJ.2.2.1⟩
    · exact ⟨hU.1, hU.2.1⟩
  have hcc : c.IsConformal := GW3Law.isConformal_of_isComponentChart hc hCoH.1 hCoH.2
  have hdom : (c.dom : Set ℂ) = C := by rw [hcc.coe_dom, GW3Joint.image_inv_eq_of_isComponentChart hc]
  obtain ⟨ℓ, -, hℓi, hℓ⟩ := hld C hC c hc
  obtain ⟨jumpsC, hpw, hcbd⟩ := hwd C hC c hc
  obtain ⟨horR, horL⟩ := hor C hC c hc
  obtain ⟨htR, htL⟩ := hto C hC c hc
  -- the runs
  have hregR := fun k c θ hl => pieceRegular_of_event hωR k c θ hl
  have hregL := fun k c θ hl => pieceRegular_of_event hωL k c θ hl
  have hDR : ∀ k, Exist.Staged.IsRegularDriver (E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω) :=
    fun k => hreg _ k ω
  have hDL : ∀ k, Exist.Staged.IsRegularDriver (E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω) :=
    fun k => hreg _ k ω
  have hdR' := fun pre post pc (hs : (walkRuns κ b jumps E ω).1.1 = pre ++ pc :: post) =>
    exists_pieceData (boundaryWalkSpec b jumps (-(Real.pi / 2)) true)
      (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω) hregR
      (fun k c θ hl => hf.2.1 true k c θ hl) hs
  have hdL' := fun pre post pc (hs : (walkRuns κ b jumps E ω).2.1 = pre ++ pc :: post) =>
    exists_pieceData (boundaryWalkSpec b jumps (Real.pi / 2) false)
      (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω) hregL
      (fun k c θ hl => hf.2.1 false k c θ hl) hs
  have hpdR : ∀ pc ∈ (walkRuns κ b jumps E ω).1.1,
      ∃ (A : Set ℂ) (f : ℂ → ℂ) (W : ℝ≥0 → ℝ) (α : ℝ≥0 → ℂ), PieceData pc A f W α := fun pc hpc => by
    obtain ⟨pre, post, hs'⟩ := List.append_of_mem hpc
    obtain ⟨f, W, α, hd⟩ := hdR' _ _ _ hs'
    exact ⟨_, f, W, α, hd⟩
  have hpdL : ∀ pc ∈ (walkRuns κ b jumps E ω).2.1,
      ∃ (A : Set ℂ) (f : ℂ → ℂ) (W : ℝ≥0 → ℝ) (α : ℝ≥0 → ℂ), PieceData pc A f W α := fun pc hpc => by
    obtain ⟨pre, post, hs'⟩ := List.append_of_mem hpc
    obtain ⟨f, W, α, hd⟩ := hdL' _ _ _ hs'
    exact ⟨_, f, W, α, hd⟩
  have hfR := fun pre post pc (hs : (walkRuns κ b jumps E ω).1.1 = pre ++ pc :: post)
      (h0 : (((0 : ℝ≥0)) : ℝ≥0∞) < pc.2.2) =>
    WalkIntFill.frontier_prefixChart_subset_prefixSet (-(Real.pi / 2)) true
      (fun k => E (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) k ω) hregR hDR hs h0
  have hfL := fun pre post pc (hs : (walkRuns κ b jumps E ω).2.1 = pre ++ pc :: post)
      (h0 : (((0 : ℝ≥0)) : ℝ≥0∞) < pc.2.2) =>
    WalkIntFill.frontier_prefixChart_subset_prefixSet (Real.pi / 2) false
      (fun k => E (boundaryWalkSpec b jumps (Real.pi / 2) false) k ω) hregL hDL hs h0
  have hCsub : C ⊆ H \ (physOf (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (walkRuns κ b jumps E ω).1 ∪
      physOf (boundaryWalkSpec b jumps (Real.pi / 2) false) (walkRuns κ b jumps E ω).2) :=
    Sec7.Prop74B.subset_of_mem_betweenComponents hC
  have hCR : Disjoint C (wsetOf (walkRuns κ b jumps E ω).1) := Set.disjoint_left.2 fun z hz hzw =>
    (hCsub hz).2 (Or.inl (Or.inl (Or.inr hzw.1)))
  have hCL : Disjoint C (wsetOf (walkRuns κ b jumps E ω).2) := Set.disjoint_left.2 fun z hz hzw =>
    (hCsub hz).2 (Or.inr (Or.inl (Or.inr hzw.1)))
  have hcC : MapsTo c.2.1 H C := hc.2.2.1
  have hland := hc.2.2.2.2.1
  have hpH : ∀ (x : ℝ) (p : ℂ), Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 p) → p.im ≠ 0 → p ∈ H := by
    intro x p hp him
    have : (𝓝[H] (x : ℂ)).NeBot := GW1P.neBot_nhdsWithin_H (show (0 : ℝ) ≤ ((x : ℂ)).im by simp)
    have hbar : p ∈ Hbar := QuantumZipper.isClosed_Hbar.mem_of_tendsto hp
      (eventually_nhdsWithin_of_forall fun w hw => le_of_lt (show (0 : ℝ) < (c.2.1 w).im from hCoH.2 (hcC hw)))
    exact lt_of_le_of_ne hbar (Ne.symm him)
  -- the controlled matches
  have hctlR : ∀ (x : ℝ) (p : ℂ), 0 < x → Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 p) → p ∈ ordOf (walkRuns κ b jumps E ω).1 →
      p ∉ pieceEnds (walkRuns κ b jumps E ω).1.1 → p ∉ closure (wsetOf (walkRuns κ b jumps E ω).2) →
      IsControlledMatch (walkRuns κ b jumps E ω).1 (walkRuns κ b jumps E ω).2 true c x p := by
    intro x p hx hp hpo hpE hpL
    by_cases him : p.im = 0
    · exact htR x p hx hp him hpo hpE
    · exact fun U hU hpU => exists_controlledMatch_right hdR' hfR hCR hcc hcC
        (fun x hx => by
          obtain ⟨z, hz, hzR, -⟩ := hland x
          exact ⟨z, hz, mem_ordOf_or_im_eq_zero (hzR hx)⟩) hx hp (hpH x p hp him) hU hpU hpo hpE hpL horR
  have hctlL : ∀ (x : ℝ) (p : ℂ), x < 0 → Tendsto c.2.1 (𝓝[H] (x : ℂ)) (𝓝 p) → p ∈ ordOf (walkRuns κ b jumps E ω).2 →
      p ∉ pieceEnds (walkRuns κ b jumps E ω).2.1 → p ∉ closure (wsetOf (walkRuns κ b jumps E ω).1) →
      IsControlledMatch (walkRuns κ b jumps E ω).2 (walkRuns κ b jumps E ω).1 false c x p := by
    intro x p hx hp hpo hpE hpR
    by_cases him : p.im = 0
    · exact htL x p hx hp him hpo hpE
    · exact fun U hU hpU => exists_controlledMatch_left hdL' hfL hCL hcc hcC
        (fun x hx => by
          obtain ⟨z, hz, -, hzL⟩ := hland x
          exact ⟨z, hz, mem_ordOf_or_im_eq_zero (hzL hx)⟩) hx hp (hpH x p hp him) hU hpU hpo hpE hpR horL
  -- prefixes
  obtain ⟨R₀, hR₀⟩ := exists_walkPrefix_raw_eq_empty (-(Real.pi / 2)) true _ hregR hDR hTipR hlR
  obtain ⟨L₀, hL₀⟩ := exists_walkPrefix_raw_eq_empty (Real.pi / 2) false _ hregL hDL hTipL hlL
  have hrawR : ∀ R : WalkPrefix (walkRuns κ b jumps E ω).1, ∃ a : ℝ≥0, R.raw = α '' Icc 0 a ∩ H := fun R =>
    WalkIntRunChron.exists_raw_initial_segment_of_run
      (fun k c θ' hl hseed => WalkIntRunChron.pieceSimpleAt_at_launch _ _ (hf.2.1 true) hTipR hl hseed)
      hClR hα hα0 hrR hDR R
  have hrawL : ∀ R : WalkPrefix (walkRuns κ b jumps E ω).2, ∃ a : ℝ≥0, R.raw = β '' Icc 0 a ∩ H := fun R =>
    WalkIntRunChron.exists_raw_initial_segment_of_run
      (fun k c θ' hl hseed => WalkIntRunChron.pieceSimpleAt_at_launch _ _ (hf.2.1 false) hTipL hl hseed)
      hClL hβ hβ0 hrL hDL R
  exact finite_matches_of_sample hα hβ hα0 hβ0 hrR hrL hco hW hC hc hdom hℓi hℓ
    (ordOf_facts hα hrR hpdR).1 (ordOf_facts hβ hrL hpdL).1 hctlR hctlL
    (fun pre post pc hs τ hτ => exists_walkPrefix (-(Real.pi / 2)) true _ hregR hDR hs hτ)
    (fun pre post pc hs τ hτ => exists_walkPrefix (Real.pi / 2) false _ hregL hDL hs hτ)
    hrawR hrawL R₀ hR₀ L₀ hL₀ hpw hcbd

/-- **`WalkFiniteMatchStatement` from its live form** and `WalkLiveStatement`. -/
theorem walkFiniteMatchStatement_of_onLive (hOL : WalkFiniteMatchOnLiveStatement.{u})
    (hLive : WalkLiveStatement.{u}) : WalkFiniteMatchStatement.{u} := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hR hreg hfacts
  filter_upwards [hOL κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hR hreg hfacts,
    hLive κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hR hreg hfacts] with ω h1 h2
  intro α β hα hβ hα0 hβ0 hrR hrL C hC
  exact h1 (h2 ⟨C, hC⟩).1 (h2 ⟨C, hC⟩).2 α β hα hβ hα0 hβ0 hrR hrL C hC

/-- **`WalkFiniteMatchStatement`** (PROVE-T14-WALKINT's `hMatch`) from Theorem 1.3, the five named inputs of
`GW3SidedProof.gw3GeometryRegStatement_of_walks`, `WalkTouchMatchStatement` and `WalkLiveStatement`. -/
theorem walkFiniteMatchStatement_of_inputs (hT13 : Theorem13Statement.{u}) (hT13₀ : Theorem13Statement.{0})
    (hPR : WalkCont.RightWalkProperRegStatement.{u}) (hPL : GW3SidedProof.LeftWalkProperRegStatement.{u})
    (hA : GW2aContainmentStatement.{u}) (hF : SB.SBFrontierRegStatement.{u})
    (hNR : GW3SidedProof.RightWalkNegRealRegStatement.{u}) (hTouch : WalkTouchMatchStatement.{u})
    (hLive : WalkLiveStatement.{u}) : WalkFiniteMatchStatement.{u} :=
  walkFiniteMatchStatement_of_onLive (walkFiniteMatchOnLiveStatement_of_inputs hT13 hT13₀ hPR hPL hA hF hNR hTouch)
    hLive

end InteractingSLE.Theorem14.WalkWd
