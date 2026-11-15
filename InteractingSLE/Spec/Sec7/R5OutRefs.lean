/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec7.R5OutRelative

/-!
# Countable reference laws for incident components

PROVE-R5-OUTER, R88. A reference at relative level `p` is regularized
outside its live event and read at level zero with the earlier prefix
included among its marks. This changes no local-set mean or component.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H)
open LQGMetric (DistOn IsZeroBoundaryGFF)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec7.R5Out

open LocalSets PocketTraversal PocketAdapt PocketCoupling PocketUnionPt PocketStop
  PocketStopSide R5Enl R5Phase Lemma71C

variable {Ω : Type*}

/-- Taking the exterior of a regularized pocket reference a second time changes nothing. -/
theorem extHullSet_liveExt (A : Set Ω) (γ : Ω → ℝ → ℂ) (C F : Ω → Set ℂ)
    (p : ℝ≥0) (ω : Ω) : extHullSet (C ω) (liveExt A γ C F p ω) = liveExt A γ C F p ω := by
  by_cases hl : ω ∈ A ∧ (p : ℝ≥0∞) < capLife (γ ω)
  · rw [liveExt_of_live hl]
    ext z
    simp only [extHullSet, mem_inter_iff, mem_union, mem_compl_iff]
    tauto
  · rw [liveExt_of_not_live hl]
    ext z
    simp only [extHullSet, mem_inter_iff, mem_union, mem_compl_iff]
    tauto

/-- A regularized reference has the same physical set when read at level zero. -/
theorem liveExt_liveExt_zero {A : Set Ω} {γ : Ω → ℝ → ℂ} {C F : Ω → Set ℂ}
    (hγ : ∀ ω ∈ A, IsDrivenCurve (γ ω)) (p : ℝ≥0) :
    liveExt A γ C (liveExt A γ C F p) 0 = liveExt A γ C F p := by
  funext ω
  by_cases hω : ω ∈ A
  · rw [liveExt_of_live ⟨hω, PocketPhaseMeans.capLife_pos (hγ ω hω)⟩]
    exact extHullSet_liveExt A γ C F p ω
  · rw [liveExt_of_not_live (fun h => hω h.1), liveExt_of_not_live (fun h => hω h.1)]

/-- Earlier prefix marks already contain the level-zero prefix. -/
theorem locPrefixSigma_prefix_zero (𝓦 : MeasurableSpace Ω) (A : Set Ω)
    (γ : Ω → ℝ → ℂ) (p : ℝ≥0) :
    locPrefixSigma (locPrefixSigma 𝓦 A γ p) A γ 0 = locPrefixSigma 𝓦 A γ p := by
  refine le_antisymm (sup_le le_rfl ?_) le_sup_left
  exact le_sup_right.trans (PhaseCont.locPrefixSigma_mono 𝓦 A γ (show (0 : ℝ≥0) ≤ p from zero_le))

/-- The component union law at a relative level gives a raw reference law for the same set. -/
theorem pocketStopUnionLaw_reference {𝓦 : MeasurableSpace Ω} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {A : Set Ω} {γ : Ω → ℝ → ℂ}
    {C F : Ω → Set ℂ} {h₀ : Ω → DistOn upperHalfPlaneOpens}
    (p : ℝ≥0) (hpre : locPrefixSigma 𝓦 A γ p ≤ mΩ)
    (hU : PocketStopUnionLaw 𝓦 P A γ C F h₀ p) :
    PocketStopUnionLaw (locPrefixSigma 𝓦 A γ p) P A γ C
      (liveExt A γ C F p) h₀ 0 := by
  obtain ⟨E, hEm, hEloc, hEeq⟩ := hU
  have hLm := measurableSet_live (𝓦 := 𝓦) A γ p
  have hBmeas := measurable_liveExt (hpre _ hLm) hEm hEeq
  have hBloc := isHistoryAvoidanceLocal_liveExt hLm hEloc hEeq
  refine ⟨liveExt A γ C F p, hBmeas, ?_, fun ω _ _ => ?_⟩
  · rw [locPrefixSigma_prefix_zero]
    exact hBloc
  · exact (extHullSet_liveExt A γ C F p ω).symm

end InteractingSLE.Sec7.R5Out
