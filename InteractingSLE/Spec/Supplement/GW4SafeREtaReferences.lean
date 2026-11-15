/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeREtaLaw

/-! # GW4: actual rational references for the given component means

The actual own-reference cover and the conditioned increment laws now apply
to every version of the given B means. The countable intersection is taken
before selecting a rational reference for each realized boundary access.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open Set Filter Topology Metric MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
open QuantumZipper (H)
open LQGMetric (DistOn)

namespace InteractingSLE.Theorem14.GW4Fix

open LocalSets WholeField Restart Sec7.Aux119Heights

/-- Actual rational references, selected after the common probability-one
event, supply both zero increments at every nonzero live boundary access. -/
theorem exists_component_rational_references_of_mean {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {c₀ : BoundaryWord} {F : Frame} {ν : Measure Ω} [IsProbabilityMeasure ν]
    {X : Ω → DistOn upperHalfPlaneOpens} {Wd R : ℝ≥0 → Ω → ℝ}
    {GT : Set Ω} {V : Ω → ℝ≥0∞} {hWm : ∀ r, Measurable (Wd r)}
    {u₀ : ℂ → ℝ} {ℋ : ℝ≥0 → MeasurableSpace Ω} {B : ℝ≥0 → Ω → Set ℂ}
    (hF : F.IsOk) (hX : IsGFFWithBoundaryData ν X c₀.fn c₀.jumps)
    (hGT : ∀ ω ∈ GT, F.IsPathOk (fun r => Wd r ω))
    (hGTm : MeasurableSet GT) (hGTae : ∀ᵐ ω ∂ν, ω ∈ GT)
    (hver : IsGW4RelVersionR ν Wd F.c F.C R V)
    (hloc : ComponentLineLocality c₀ F ν X Wd GT R V hWm u₀ ℋ B) :
    ∃ G : ℚ → Ω → DistOn upperHalfPlaneOpens,
      (∀ s : ℚ, IsLocalSetMean (B (s : ℝ).toNNReal)
        (centredField X u₀) ν (G s)) ∧
      ∀ (t : ℝ≥0) (g : Ω → DistOn upperHalfPlaneOpens),
        IsLocalSetMean (B t) (centredField X u₀) ν g →
        ∀ᵐ ω ∂ν, lineClock F Wd GT V t ω < V ω →
          0 < (lineClock F Wd GT V t ω).toNNReal → ∀ ξ : ℝ, ξ ≠ 0 →
          ∃ s : ℚ, (F.ent (fun u => Wd u ω) : ℝ) < s ∧ (s : ℝ) < t ∧
            trc (fun u => Wd u ω) (s : ℝ).toNNReal ≠ 0 ∧
            -(trc (fun u => Wd u ω) (s : ℝ).toNNReal)⁻¹ ∈ F.C ∧
            lineClock F Wd GT V (s : ℝ).toNNReal ω < lineClock F Wd GT V t ω ∧
            ∃ x r : ℝ, 0 < r ∧
              (componentLineChart F Wd GT R V (s : ℝ).toNNReal ω).2.1 ''
                (H ∩ ball (x : ℂ) r) ⊆ ((componentLineChart F Wd GT R V t ω).dom : Set ℂ) ∧
              Tendsto (fun z => (componentLineChart F Wd GT R V (s : ℝ).toNNReal ω).1
                  ((componentLineChart F Wd GT R V t ω).2.1 z))
                (𝓝[H] (ξ : ℂ)) (𝓝 (x : ℂ)) ∧
              Tendsto (fun z => harmRep (g ω) (H \ B t ω)
                    ((componentLineChart F Wd GT R V t ω).2.1 z) -
                  harmRep (G s ω) (H \ B (s : ℝ).toNNReal ω)
                    ((componentLineChart F Wd GT R V t ω).2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 0) ∧
              Tendsto (fun z => (componentLineChart F Wd GT R V t ω).2.2
                    ((componentLineChart F Wd GT R V t ω).2.1 z) -
                  (componentLineChart F Wd GT R V (s : ℝ).toNNReal ω).2.2
                    ((componentLineChart F Wd GT R V t ω).2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 0) := by
  have hExists : ∀ s : ℚ, ∃ g : Ω → DistOn upperHalfPlaneOpens,
      IsLocalSetMean (B (s : ℝ).toNNReal) (centredField X u₀) ν g := by
    intro s
    obtain ⟨g, hg, -⟩ := exists_component_initial_reference hX hloc
      hver.1.1.2.2.1 hver.1.1.2.1 (s : ℝ).toNNReal
    exact ⟨g, hg⟩
  choose G hG using hExists
  refine ⟨G, hG, ?_⟩
  intro t g hg
  have hAll := ae_all_iff.2 (fun s : {s : ℚ // (s : ℝ).toNNReal ≤ t} =>
    ae_component_reference_zero_germ_of_mean hF hX hGT hGTm hGTae hver hloc s.property
      (G s.val) g (hG s.val) hg)
  filter_upwards [hAll, hGTae, hver.1.1.2.2.2.2] with ω hAllω hω hHull hLive hq ξ hξ
  obtain ⟨s, hsEnt, hst, hs0, hsC, hsClock, x, r, hr, hCol, hTr, hLift⟩ :=
    exists_component_rat_reference hF hGT hω (hver.1.1.2.1 ω) (hver.1.1.2.2.1 ω)
      hHull hLive hq hξ
  have hs : (s : ℝ).toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.2 hst.le
  exact ⟨s, hsEnt, hst, hs0, hsC, hsClock, x, r, hr, hCol, hTr,
    hAllω ⟨s, hs⟩ hLive ξ x r hr hCol hTr, hLift⟩

end InteractingSLE.Theorem14.GW4Fix
