/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.CfConvOmega

/-!
# Removing zero-weight marks from the chart clause

Packet PROVE-CFCHART2. An embedding selecting every nonzero weight preserves the force
boundary data, the canonical chart clause and the continuation threshold. This permits a
zero-weight junction to be removed before classifying the word as a flow-line word.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open QuantumZipper (H)
open scoped NNReal ENNReal

namespace InteractingSLE.Sec5.CfConv

open CfGiven CfChart Restart Restart.DomainMarkov Sec7.PocketTraversal

open scoped Classical in
/-- A sum does not change when omitted indices have weight zero. -/
theorem sum_filter_reindex_zero {α β : Type*} [Fintype α] [Fintype β]
    (e : α ↪ β) (ρ : β → ℝ) (hzero : ∀ j, j ∉ range e → ρ j = 0) (p : β → Prop) :
    (∑ i ∈ Finset.univ.filter (fun i => p (e i)), ρ (e i)) = ∑ j ∈ Finset.univ.filter p, ρ j := by
  classical
  calc
    _ = ∑ j ∈ (Finset.univ.filter (fun i => p (e i))).image e, ρ j :=
      (Finset.sum_image (fun i _ j _ hij => e.injective hij)).symm
    _ = _ := Finset.sum_subset (by
      rintro j hj
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 hj
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hi).2⟩) (by
      intro j hj hnot
      apply hzero j
      rintro ⟨i, rfl⟩
      exact hnot (Finset.mem_image.2 ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, (Finset.mem_filter.1 hj).2⟩, rfl⟩))

/-- Zero-weight erasure preserves the entire force boundary function. -/
theorem forceBoundaryData_reindex_zero {nL nR kL kR : ℕ} (eL : Fin kL ↪ Fin nL) (eR : Fin kR ↪ Fin nR)
    (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (hL : ∀ j, j ∉ range eL → ρL j = 0) (hR : ∀ j, j ∉ range eR → ρR j = 0)
    (κ : ℝ) (vL : Fin nL → ℝ) (vR : Fin nR → ℝ) :
    forceBoundaryData κ (ρL ∘ eL) (ρR ∘ eR) (vL ∘ eL) (vR ∘ eR) = forceBoundaryData κ ρL ρR vL vR := by
  funext x
  simp only [forceBoundaryData, Function.comp_apply]
  rw [sum_filter_reindex_zero eL ρL hL (fun j => x < vL j),
    sum_filter_reindex_zero eR ρR hR (fun j => vR j ≤ x)]

section Chart

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {nL nR kL kR : ℕ} {κ a k : ℝ}
  {ρL : Fin nL → ℝ} {ρR : Fin nR → ℝ} {𝓐 : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}
  {VL : Fin nL → ℝ≥0 → Ω → ℝ} {VR : Fin nR → ℝ≥0 → Ω → ℝ}
  {ζ : Ω → ℝ≥0∞} {c : Ω → Chart} {h : Ω → LQGMetric.DistOn upperHalfPlaneOpens}

/-- The canonical chart clause survives deletion of zero-weight marks. -/
theorem IsChartCanon.reindex_zero (eL : Fin kL ↪ Fin nL) (eR : Fin kR ↪ Fin nR)
    (hL : ∀ j, j ∉ range eL → ρL j = 0) (hR : ∀ j, j ∉ range eR → ρR j = 0)
    (hc : ∀ ω, (c ω).IsConformal) (hWc : ∀ ω, Continuous fun s : ℝ => W s.toNNReal ω)
    (hcan : IsChartCanon κ ρL ρR P 𝓐 W VL VR ζ c a k h) :
    IsChartCanon κ (ρL ∘ eL) (ρR ∘ eR) P 𝓐 W (fun i => VL (eL i)) (fun j => VR (eR j)) ζ c a k h := by
  intro t φ
  filter_upwards [hcan t φ] with ω hω hE
  rw [hω hE]
  apply (chartRhs_congr hc hWc (ω := ω) (t := t) (φ := φ) (ζ := ζ) ?_ hE).symm
  have hu := isBoundedHarmonicExtension_bheProc (κ := κ) (ρL := ρL ∘ eL) (ρR := ρR ∘ eR)
    (W := W) (VL := fun i => VL (eL i)) (VR := fun j => VR (eR j)) ω t
  have hdata := forceBoundaryData_reindex_zero eL eR ρL ρR hL hR κ
    (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω)
  change IsBoundedHarmonicExtension
    (forceBoundaryData κ (ρL ∘ eL) (ρR ∘ eR) ((fun i => VL i t ω - W t ω) ∘ eL)
      ((fun j => VR j t ω - W t ω) ∘ eR)) _ _ at hu
  rw [hdata] at hu
  have hjumps : forceJumpSet (fun i => VL (eL i) t ω - W t ω) (fun j => VR (eR j) t ω - W t ω) ⊆
      forceJumpSet (fun i => VL i t ω - W t ω) (fun j => VR j t ω - W t ω) := by
    rintro x (rfl | hx | hx)
    · exact Or.inl rfl
    · obtain ⟨i, rfl⟩ := hx
      exact Or.inr (Or.inl ⟨eL i, rfl⟩)
    · obtain ⟨j, rfl⟩ := hx
      exact Or.inr (Or.inr ⟨eR j, rfl⟩)
  have hu' := LocalExt.IsBoundedHarmonicExtension.mono_set hu hjumps
  obtain ⟨_, _, huniq⟩ := Spec.Provider.existsUnique_isBoundedHarmonicExtension_forceBoundaryData (κ := κ)
    (ρL := ρL) (ρR := ρR) (vL := fun i => VL i t ω - W t ω) (vR := fun j => VR j t ω - W t ω)
  intro z hz
  exact (huniq _ hu' hz).trans
    (huniq _ (isBoundedHarmonicExtension_bheProc (W := W) (VL := VL) (VR := VR) ω t) hz).symm

end Chart

/-- Zero-weight erasure also preserves the exact geometric continuation threshold. -/
theorem thr_reindex_zero {Ω : Type*} {nL nR kL kR : ℕ} (eL : Fin kL ↪ Fin nL) (eR : Fin kR ↪ Fin nR)
    (ρL : Fin nL → ℝ) (ρR : Fin nR → ℝ)
    (hL : ∀ j, j ∉ range eL → ρL j = 0) (hR : ∀ j, j ∉ range eR → ρR j = 0)
    (W : ℝ≥0 → Ω → ℝ) (xL : Ω → Fin nL → ℝ) (xR : Ω → Fin nR → ℝ) (ω : Ω) :
    FCDet.thr (ρL ∘ eL) (ρR ∘ eR) W (fun ω => xL ω ∘ eL) (fun ω => xR ω ∘ eR) ω =
      FCDet.thr ρL ρR W xL xR ω := by
  classical
  have he : MartChar.thresholdSet (ρL ∘ eL) (ρR ∘ eR) (fun t => W t ω)
      (fun i t => geomLW W xL (eL i) t ω) (fun j t => geomRW W xR (eR j) t ω) =
      MartChar.thresholdSet ρL ρR (fun t => W t ω)
        (fun i t => geomLW W xL i t ω) (fun j t => geomRW W xR j t ω) := by
    ext t
    simp only [MartChar.thresholdSet, mem_ofPred_eq, ForceWord.ThresholdCondition, Function.comp_apply]
    rw [sum_filter_reindex_zero eL ρL hL (fun i => geomLW W xL i t ω = W t ω),
      sum_filter_reindex_zero eR ρR hR (fun j => geomRW W xR j t ω = W t ω)]
  change MartChar.thresholdTime (ρL ∘ eL) (ρR ∘ eR) (fun t => W t ω)
    (fun i t => geomLW W xL (eL i) t ω) (fun j t => geomRW W xR (eR j) t ω) = _
  unfold MartChar.thresholdTime
  rw [he]
  rfl

end InteractingSLE.Sec5.CfConv
