/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntRunChronSimple
import InteractingSLE.Spec.Supplement.GW1WalkExitParam
import InteractingSLE.Spec.Supplement.WalkNormFacts

/-!
# Actual-run traversal direction from Theorem 1.3

The committed GW1 exit theorem supplies D.4, physical tip coordinates and
connector clearance. Recorded own-time order follows from actual run
histories. This theorem spells out WalkWords' direction conclusion without
importing its in-flight definition or taking hChron as a hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.WalkIntRunChron

open GW1WalkChain GW1Bookkeep GW1WalkFinish GW1ParamEvery Exist Exist.Staged Exist.StagedLaw
open WalkBdry WalkMean WalkNorm WalkInf WalkIntOrient

/-- The exact actual-run tipAt direction implication. Theorem 1.3 and
piece simplicity discharge chronology; no hChron or direction input. -/
theorem ae_recorded_piece_direction (hT13 : Theorem13Statement.{u})
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
      ∀ᵐ ω ∂P, ∀ pR ∈ (WalkMean.walkRuns κ b jumps E ω).1.1, ∀ pL ∈ (WalkMean.walkRuns κ b jumps E ω).2.1,
        ∀ (a a' c c' : ℝ≥0) (z z' : ℂ), (a : ℝ≥0∞) ≤ pR.2.2 → (a' : ℝ≥0∞) ≤ pR.2.2 →
          (c : ℝ≥0∞) ≤ pL.2.2 → (c' : ℝ≥0∞) ≤ pL.2.2 →
          pR.1.tipAt pR.2.1 a z → pR.1.tipAt pR.2.1 a' z' → pL.1.tipAt pL.2.1 c z → pL.1.tipAt pL.2.1 c' z' →
          a < a' → c < c' := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE _hR hreg hfacts hsimple
  have hD4 := GW1WalkExit.walkD4GeometryStatement_of_theorem13 hT13 hT13₀
  have hTip := walkTipCoordinatesStatement_of_d4 hT13 hD4
  have hClear := walkConnectorClearanceStatement_of_d4_and_exit
    (GW1WalkExit.walkExitClassificationStatement_of_theorem13 hT13₀) hD4
  filter_upwards [hTip κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg true,
    hTip κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg false,
    hClear κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg true,
    hClear κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg false,
    hfacts, hsimple] with ω hTipR hTipL hClearR hClearL hf hs
  obtain ⟨⟨γR, hγR, hγR0, hrγR⟩, ⟨γL, hγL, hγL0, hrγL⟩, horder⟩ := hf
  have horder' := horder γR γL hrγR hrγL
    (GW4Leaf.isCompleteSimpleFlow_of_isProperCurve hγR hγR0)
    (GW4Leaf.isCompleteSimpleFlow_of_isProperCurve hγL hγL0)
  intro pR hpR pL hpL a a' c c' z z' ha ha' hc hc' hza hza' hzc hzc' haa'
  have hoR := recorded_piece_clock_order_of_mem
    (fun k c θ' hl hseed => pieceSimpleAt_at_launch _ _ (hs true) hTipR hl hseed)
    hClearR hγR hγR0 hrγR hpR
  have hoL := recorded_piece_clock_order_of_mem
    (fun k c θ' hl hseed => pieceSimpleAt_at_launch _ _ (hs false) hTipL hl hseed)
    hClearL hγL hγL0 hrγL hpL
  have hmemR (t : ℝ≥0) (w : ℂ) (ht : (t : ℝ≥0∞) ≤ pR.2.2)
      (hw : pR.1.tipAt pR.2.1 t w) : w ∈ range γR := by
    rw [hrγR]
    exact Or.inl (Or.inr (mem_iUnion₂.2 ⟨pR, hpR, t, ht, hw⟩))
  have hmemL (t : ℝ≥0) (w : ℂ) (ht : (t : ℝ≥0∞) ≤ pL.2.2)
      (hw : pL.1.tipAt pL.2.1 t w) : w ∈ range γL := by
    rw [hrγL]
    exact Or.inl (Or.inr (mem_iUnion₂.2 ⟨pL, hpL, t, ht, hw⟩))
  have hz := (apply_curveTime (hmemR a z ha hza)).trans (apply_curveTime (hmemL c z hc hzc)).symm
  have hz' := (apply_curveTime (hmemR a' z' ha' hza')).trans (apply_curveTime (hmemL c' z' hc' hzc')).symm
  exact (hoL c c' z z' hc hc' hzc hzc').2
    ((horder' _ _ _ _ hz hz').1 ((hoR a a' z z' ha ha' hza hza').1 haa'))

end InteractingSLE.Theorem14.WalkIntRunChron
