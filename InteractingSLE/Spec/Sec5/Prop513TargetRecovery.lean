/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Prop513TargetGeometry
import InteractingSLE.Spec.Sec5.Prop513Assembly

/-! # Recovery with an almost surely equal measurable cone version

The compact-path decoder gives exact field measurability and almost sure cone
equality. The existing light-cone recovery uses that equality only almost surely.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Set Topology
open scoped Real NNReal ENNReal

namespace InteractingSLE.Sec5.Prop513Target
open QuantumZipper

/-- The tip-to-light-cone argument with its representation equality needed only
almost surely. All recovery and time-density results are reused unchanged. -/
theorem path_of_tips_of_evolution_ae_cones {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hκ : 4 < κ)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    (hsep : ∀ r : ℝ≥0, 0 < r → ∀ᵐ ω ∂P, (∀ i, VL i r ω < W r ω) ∧ ∀ j, W r ω < VR j r ω)
    {𝒢 : MeasurableSpace Ω} {γ : Ω → ℝ≥0 → ℂ} {z : ℕ → Ω → ℂ} {S L : ℕ → Ω → Set ℂ}
    (hz : ∀ n, Measurable[𝒢] (z n)) (hL : ∀ n, @Measurable Ω (Set ℂ) 𝒢 hittingSigma (L n))
    (hLS : ∀ᵐ ω ∂P, ∀ n, L n ω = closure (insert (z n ω) (S n ω)))
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω))
    (hzγ : ∀ᵐ ω ∂P, ∀ n, ∃ t, γ ω t = z n ω)
    (hord : ∀ᵐ ω ∂P, ∀ n, ∀ p ∈ S n ω, ∃ v, γ ω v = p ∧ ∀ w ≤ v, γ ω w ≠ z n ω)
    (htip : ∀ n, ∀ q : ℚ, 0 ≤ q → ∀ᵐ ω ∂P,
      (q : ℝ) < traceFirstVisit (γ ω) (z n ω) → γ ω (q : ℝ).toNNReal ∈ L n ω)
    (htip0 : ∀ q : ℚ, 0 ≤ q → ∀ᵐ ω ∂P, γ ω (q : ℝ).toNNReal ∈ closure (range fun n => z n ω)) :
    ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[𝒢] fun ω => Γ' ω t) ∧ ∀ᵐ ω ∂P, Γ' ω = γ ω := by
  have htip' : ∀ᵐ ω ∂P, ∀ n, ∀ q : ℚ, 0 ≤ q →
      (q : ℝ) < traceFirstVisit (γ ω) (z n ω) → γ ω (q : ℝ).toNNReal ∈ L n ω := by
    refine ae_all_iff.2 fun n => ae_all_iff.2 fun q => ?_
    by_cases hq : 0 ≤ q
    · filter_upwards [htip n q hq] with ω hω _ using hω
    · exact Eventually.of_forall fun ω h => absurd h hq
  have htip0' : ∀ᵐ ω ∂P, ∀ q : ℚ, 0 ≤ q → γ ω (q : ℝ).toNNReal ∈ closure (range fun n => z n ω) := by
    refine ae_all_iff.2 fun q => ?_
    by_cases hq : 0 ≤ q
    · filter_upwards [htip0 q hq] with ω hω _ using hω
    · exact Eventually.of_forall fun ω h => absurd h hq
  refine @prop513_path_of_lightCone_of_evolution κ nL nR xL xR ρL ρR Ω mΩ P _ 𝓕 W VL VR B ζ hκ hE hζ hsep 𝒢
    γ z L hz hL htr hzγ ?_ ?_
  · filter_upwards [htr, hzγ, hord, htip', hLS] with ω hη hzω hoω htω hLSω n
    exact lightCone_eq_image_Icc (continuous_of_isGeneratingTrace_top hη) (hzω n) (hLSω n) (hoω n)
      (htω n)
  · filter_upwards [htr, htip0'] with ω hη htω
    exact range_subset_of_rat (continuous_of_isGeneratingTrace_top hη) isClosed_closure htω

/-- **Recovery from almost surely represented measurable cones**
(conditional helper; distinct name). As `path_of_tips_of_evolution_ae_cones`, with the separation of the force points
at fixed times derived from the non-boundary-intersecting property of the counterflow: almost surely its trace is in
the open half-plane at every positive time (`sep_of_trace_mem_H`). -/
theorem path_of_tips_ae_cones {κ : ℝ} {nL nR : ℕ} {xL : Fin nL → ℝ} {xR : Fin nR → ℝ}
    {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ} {VL : Fin nL → ℝ≥0 → Ω → ℝ}
    {VR : Fin nR → ℝ≥0 → Ω → ℝ} {B : ℝ≥0 → Ω → ℝ} {ζ : Ω → ℝ≥0∞} (hκ : 4 < κ)
    (hE : IsIntegratedSLEEvolution κ xL xR ρL ρR P 𝓕 W VL VR B ζ) (hζ : ∀ᵐ ω ∂P, ζ ω = ⊤)
    {𝒢 : MeasurableSpace Ω} {γ : Ω → ℝ≥0 → ℂ} {z : ℕ → Ω → ℂ} {S L : ℕ → Ω → Set ℂ}
    (hz : ∀ n, Measurable[𝒢] (z n)) (hL : ∀ n, @Measurable Ω (Set ℂ) 𝒢 hittingSigma (L n))
    (hLS : ∀ᵐ ω ∂P, ∀ n, L n ω = closure (insert (z n ω) (S n ω)))
    (htr : ∀ᵐ ω ∂P, IsGeneratingTrace (fun t => W t ω) ⊤ (γ ω))
    (htrH : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → γ ω t ∈ H)
    (hzγ : ∀ᵐ ω ∂P, ∀ n, ∃ t, γ ω t = z n ω)
    (hord : ∀ᵐ ω ∂P, ∀ n, ∀ p ∈ S n ω, ∃ v, γ ω v = p ∧ ∀ w ≤ v, γ ω w ≠ z n ω)
    (htip : ∀ n, ∀ q : ℚ, 0 ≤ q → ∀ᵐ ω ∂P,
      (q : ℝ) < traceFirstVisit (γ ω) (z n ω) → γ ω (q : ℝ).toNNReal ∈ L n ω)
    (htip0 : ∀ q : ℚ, 0 ≤ q → ∀ᵐ ω ∂P, γ ω (q : ℝ).toNNReal ∈ closure (range fun n => z n ω)) :
    ∃ Γ' : Ω → ℝ≥0 → ℂ, (∀ t, StronglyMeasurable[𝒢] fun ω => Γ' ω t) ∧ ∀ᵐ ω ∂P, Γ' ω = γ ω := by
  refine @path_of_tips_of_evolution_ae_cones κ nL nR xL xR ρL ρR Ω mΩ P _ 𝓕 W VL VR B ζ hκ hE hζ ?_ 𝒢 γ z S L
    hz hL hLS htr hzγ hord htip htip0
  intro r hr
  filter_upwards [hE.2.2.2.2, hζ, htr, htrH] with ω hp hζω hη hH
  have hc : Continuous fun t => W t ω := by
    have := hp.2.2.2.1
    rw [hζω] at this
    exact continuousOn_univ.1 (by simpa using this)
  exact sep_of_trace_mem_H hp hc hη (by rw [hζω]; exact ENNReal.coe_lt_top) (hH r hr)


end InteractingSLE.Sec5.Prop513Target
