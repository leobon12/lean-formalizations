/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.WalkIntBoundCutSelect

/-!
# Actual hSelect from Theorem 1.3 and the existing between-region facts

There is one almost-sure event for every full parametrization, component
chart and finite boundary coordinate. No physical selection premise is
added to the source inputs.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

universe u

namespace InteractingSLE.Theorem14.WalkIntBoundCut

open WalkBdry WalkMean WalkNorm WalkInf WalkIntClosed GW1WalkFinish
open Exist Exist.Staged Exist.StagedLaw

/-- The full actual bounded/unbounded hSelect conclusion, uniformly
almost surely, with no chronology or cutoff-selection hypothesis. -/
theorem ae_initial_selection (hT13 : Theorem13Statement.{u}) (hT13₀ : Theorem13Statement.{0}) :
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
      (∀ (spec : ExplSpec) (k : ℕ) (ω : Ω), IsRegularDriver (E spec k ω)) →
      (∀ᵐ ω ∂P, WalkBetweenFacts κ b jumps E ω) →
      ∀ᵐ ω ∂P, ∀ α β : ℝ≥0 → ℂ,
        Supp9B.IsProperCurve α → Supp9B.IsProperCurve β → α 0 = 0 → β 0 = 0 →
        range α = physOf (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (walkRuns κ b jumps E ω).1 →
        range β = physOf (boundaryWalkSpec b jumps (Real.pi / 2) false) (walkRuns κ b jumps E ω).2 →
        ∀ C ∈ betweenComponents
          (physOf (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (walkRuns κ b jumps E ω).1)
          (physOf (boundaryWalkSpec b jumps (Real.pi / 2) false) (walkRuns κ b jumps E ω).2),
        ∀ c : Chart, IsComponentChart
          (physOf (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (walkRuns κ b jumps E ω).1)
          (physOf (boundaryWalkSpec b jumps (Real.pi / 2) false) (walkRuns κ b jumps E ω).2) C c →
        ∀ x : ℝ, ∃ (J : ClosedPair (walkRuns κ b jumps E ω).1 (walkRuns κ b jumps E ω).2) (a b' : ℝ≥0),
          J.right.raw = (α '' Icc 0 a) ∩ H ∧ J.left.raw = (β '' Icc 0 b') ∩ H ∧
          (∀ u, α u = GW4Traverse.invExt c (x : ℂ) → u < a) ∧
          (∀ v, β v = GW4Traverse.invExt c (x : ℂ) → v < b') ∧
          (Bornology.IsBounded (c.dom : Set ℂ) → ∃ s t : ℝ≥0,
            a < s ∧ b' < t ∧ α s = β t ∧ α s ∈ closure (c.dom : Set ℂ)) := by
  intro κ hκ hκ4 b jumps hb Ω _ _ P _ h hh W' ζ' hcf hζ' E hE _hR hreg hfacts
  have hD4 := GW1WalkExit.walkD4GeometryStatement_of_theorem13 hT13 hT13₀
  have hTip := walkTipCoordinatesStatement_of_d4 hT13 hD4
  have hClear := walkConnectorClearanceStatement_of_d4_and_exit
    (GW1WalkExit.walkExitClassificationStatement_of_theorem13 hT13₀) hD4
  filter_upwards [hTip κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg true,
    hTip κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg false,
    hClear κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg true,
    hClear κ hκ hκ4 b jumps hb P h hh W' ζ' hcf hζ' E hE hreg false,
    hfacts] with ω htR htL hcR hcL hf α β hα hβ hα0 hβ0 hRangeR hRangeL C hC c hchart
  have horder := hf.1.2.2 α β hRangeR hRangeL
    (GW4Leaf.isCompleteSimpleFlow_of_isProperCurve hα hα0)
    (GW4Leaf.isCompleteSimpleFlow_of_isProperCurve hβ hβ0)
  have hno : ∀ a b' : ℝ≥0, a < b' → ¬ α '' Icc a b' ⊆ range β := by
    intro a b' hab hsub
    have hnc := hf.2.2.1 (α '' Icc a b') (by
      change α '' Icc a b' ⊆
        physOf (boundaryWalkSpec b jumps (-(Real.pi / 2)) true) (walkRuns κ b jumps E ω).1 ∩
        physOf (boundaryWalkSpec b jumps (Real.pi / 2) false) (walkRuns κ b jumps E ω).2
      rw [← hRangeR, ← hRangeL]
      exact fun z hz => ⟨image_subset_range α _ hz, hsub hz⟩)
      (isPreconnected_Icc.image α hα.1.continuousOn)
    exact hab.ne (hα.2.1 (hnc ⟨a, ⟨le_rfl, hab.le⟩, rfl⟩ ⟨b', ⟨hab.le, le_rfl⟩, rfl⟩))
  have hCoH : IsOpen C ∧ C ⊆ H := by
    rcases hf.2.2.2 C hC with hJ | hU
    · exact ⟨hJ.1, hJ.2.2.1⟩
    · exact ⟨hU.1, hU.2.1⟩
  have hdom : (c.dom : Set ℂ) = C := by
    rw [(GW3Law.isConformal_of_isComponentChart hchart hCoH.1 hCoH.2).coe_dom,
      GW3Joint.image_inv_eq_of_isComponentChart hchart]
  have hC' : (c.dom : Set ℂ) ∈ betweenComponents (range α) (range β) := by
    rw [hdom, hRangeR, hRangeL]
    exact hC
  have hc' : IsComponentChart (range α) (range β) (c.dom : Set ℂ) c := by
    rw [hdom, hRangeR, hRangeL]
    exact hchart
  exact initial_selection_of_component_chart hα hβ hα0 hβ0 horder hno hC' hc'
    (fun a => exists_actual_closedPrefix_at_parameter (hf.2.1 true) htR hcR
      (fun k => hreg _ k ω) hα hα0 hRangeR a)
    (fun a => exists_actual_closedPrefix_at_parameter (hf.2.1 false) htL hcL
      (fun k => hreg _ k ω) hβ hβ0 hRangeL a)

end InteractingSLE.Theorem14.WalkIntBoundCut
