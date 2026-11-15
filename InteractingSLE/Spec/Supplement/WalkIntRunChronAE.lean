/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntRunChronDirection
import InteractingSLE.Spec.Supplement.WalkIntRunChronClosed

/-!
# Almost-sure actual closed-prefix histories from Theorem 1.3

Both the live cap and finite completed cases have proved carriers. The
committed GW1 exit and D.4 results discharge all run-chronology inputs.
The conclusion is uniform over every recorded prefix and full-walk map.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.WalkIntRunChron

open GW1WalkChain GW1Bookkeep GW1WalkFinish GW1ParamEvery Exist Exist.Staged Exist.StagedLaw
open WalkBdry WalkMean WalkNorm WalkInf WalkIntClosed

/-- Chronological histories for every actual completed-prefix reference,
with no hCaps, hChron, tip-coordinate or clearance input. -/
theorem ae_closed_histories (hT13 : Theorem13Statement.{u})
    (hT13₀ : Theorem13Statement.{0}) :
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
      (∀ᵐ ω ∂P, WalkInf.WalkPairPathFacts κ b jumps E ω) →
      (∀ᵐ ω ∂P, WalkNorm.WalkPiecesSimple κ b jumps E ω) →
      ∀ right : Bool, ∀ᵐ ω ∂P, ∀ α : ℝ≥0 → ℂ, α 0 = 0 →
        range α = ExplState.physSet κ b jumps (GW1Z.walkSpec b jumps right)
          (fun j => E (GW1Z.walkSpec b jumps right) j ω) →
        ∀ R : ClosedPrefix (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
          (fun j => E (GW1Z.walkSpec b jumps right) j ω) (GW1Z.walkSpec b jumps right).2.2.length),
          ∃ (A : Set ℂ) (q : ℂ), ArcHistory (α 0) A q ∧ A ∩ H = R.raw ∧ A ⊆ range α := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE _hR hreg _hfacts hsimple right
  have hD4 := GW1WalkExit.walkD4GeometryStatement_of_theorem13 hT13 hT13₀
  have hTip := walkTipCoordinatesStatement_of_d4 hT13 hD4
  have hClear := walkConnectorClearanceStatement_of_d4_and_exit
    (GW1WalkExit.walkExitClassificationStatement_of_theorem13 hT13₀) hD4
  filter_upwards [hTip κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg right,
    hClear κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg right, hsimple]
    with ω ht hc hs α hα0 hRange R
  exact exists_closed_history_of_run
    (fun k c θ' hl hseed => pieceSimpleAt_at_launch _ _ (hs right) ht hl hseed)
    hc hα0 hRange (fun k => hreg _ k ω) R

/-- Every actual closed prefix has an exact raw initial-segment identity
in every proper full parametrization, simultaneously almost surely. -/
theorem ae_closed_raw_initial_segments (hT13 : Theorem13Statement.{u})
    (hT13₀ : Theorem13Statement.{0}) :
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
      (∀ᵐ ω ∂P, WalkInf.WalkPairPathFacts κ b jumps E ω) →
      (∀ᵐ ω ∂P, WalkNorm.WalkPiecesSimple κ b jumps E ω) →
      ∀ right : Bool, ∀ᵐ ω ∂P, ∀ α : ℝ≥0 → ℂ, Supp9B.IsProperCurve α → α 0 = 0 →
        range α = ExplState.physSet κ b jumps (GW1Z.walkSpec b jumps right)
          (fun j => E (GW1Z.walkSpec b jumps right) j ω) →
        ∀ R : ClosedPrefix (ExplState.run κ b jumps (GW1Z.walkSpec b jumps right)
          (fun j => E (GW1Z.walkSpec b jumps right) j ω) (GW1Z.walkSpec b jumps right).2.2.length),
          ∃ a : ℝ≥0, R.raw = (α '' Icc 0 a) ∩ H := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE hR hreg hfacts hsimple right
  filter_upwards [ae_closed_histories hT13 hT13₀ κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ'
    E hE hR hreg hfacts hsimple right] with ω hω α hα hα0 hRange R
  obtain ⟨A, q, hhist, hraw, hrange⟩ := hω α hα0 hRange R
  obtain ⟨a, hA, _⟩ := WalkIntOrient.arcHistory_endpoint_initial_segment hα hhist hrange
  exact ⟨a, hraw.symm.trans (congrArg (fun B => B ∩ H) hA)⟩

end InteractingSLE.Theorem14.WalkIntRunChron
