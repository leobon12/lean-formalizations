/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Supplement.GW4SafeRZetaGerm
import InteractingSLE.Spec.Supplement.GW4SafeRZetaCover

/-!
# GW4: countably many actual references cover every nonzero access

Choose canonical local-set means at the rational physical times and
intersect their zero-increment events before selecting a reference from
the realized geometry. Both the mean increment and the inherited lift
tend to zero. This includes exposed accesses; identifying the old ambient
height and its common lattice phase is a separate remaining step.
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
theorem exists_component_rational_references {Ω : Type*} [mΩ : MeasurableSpace Ω]
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
      (∀ s : ℚ, IsLocalSetMean (safeHull F Wd GT R V (s : ℝ).toNNReal)
        (centredField X u₀) ν (G s)) ∧
      ∀ (t : ℝ≥0) (g : Ω → DistOn upperHalfPlaneOpens),
        IsLocalSetMean (safeHull F Wd GT R V t) (centredField X u₀) ν g →
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
              Tendsto (fun z => harmRep (g ω) (H \ safeHull F Wd GT R V t ω)
                    ((componentLineChart F Wd GT R V t ω).2.1 z) -
                  harmRep (G s ω) (H \ safeHull F Wd GT R V (s : ℝ).toNNReal ω)
                    ((componentLineChart F Wd GT R V t ω).2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 0) ∧
              Tendsto (fun z => (componentLineChart F Wd GT R V t ω).2.2
                    ((componentLineChart F Wd GT R V t ω).2.1 z) -
                  (componentLineChart F Wd GT R V (s : ℝ).toNNReal ω).2.2
                    ((componentLineChart F Wd GT R V t ω).2.1 z)) (𝓝[H] (ξ : ℂ)) (𝓝 0) := by
  have hZero := isZeroBoundaryGFF_centredField_of_isGFFWithBoundaryData hX hloc.1
  have hExists : ∀ s : ℚ, ∃ g : Ω → DistOn upperHalfPlaneOpens,
      IsLocalSetMean (safeHull F Wd GT R V (s : ℝ).toNNReal) (centredField X u₀) ν g := by
    intro s
    have hAm := (Frame.measurable_safeHull hF hGT hWm hGTm hGTae hver (s : ℝ).toNNReal).mono
      ((Supp8.RelSafe.physFilt Frame.measurable_gw4Rec hWm ν).le _) le_rfl
    exact (isGermConditionalLaw_iff (A := safeHull F Wd GT R V (s : ℝ).toNNReal)
      (h := centredField X u₀) (P := ν)).1
      ((component_safeHull_locality hF hGT hGTm hGTae hver hloc _).isAvoidanceLocal.isGermConditionalLaw
        hZero hAm (Eventually.of_forall fun ω =>
          ⟨safeHull_subset_H F Wd GT R V _ ω, Frame.isOpen_H_diff_safeHull hver _ ω⟩))
  choose G hG using hExists
  refine ⟨G, hG, ?_⟩
  intro t g hg
  have hAll := ae_all_iff.2 (fun s : {s : ℚ // (s : ℝ).toNNReal ≤ t} =>
    ae_component_reference_zero_germ hF hX hGT hGTm hGTae hver hloc s.property
      (G s.val) g (hG s.val) hg)
  filter_upwards [hAll, hGTae, hver.1.1.2.2.2.2] with ω hAllω hω hHull hLive hq ξ hξ
  obtain ⟨s, hsEnt, hst, hs0, hsC, hsClock, x, r, hr, hCol, hTr, hLift⟩ :=
    exists_component_rat_reference hF hGT hω (hver.1.1.2.1 ω) (hver.1.1.2.2.1 ω)
      hHull hLive hq hξ
  have hs : (s : ℝ).toNNReal ≤ t := Real.toNNReal_le_iff_le_coe.2 hst.le
  exact ⟨s, hsEnt, hst, hs0, hsC, hsClock, x, r, hr, hCol, hTr,
    hAllω ⟨s, hs⟩ hLive ξ x r hr hCol hTr, hLift⟩

end InteractingSLE.Theorem14.GW4Fix
