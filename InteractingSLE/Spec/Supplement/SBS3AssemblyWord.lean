/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Restart.ChartGauss

/-!
# S3: read the height of an unmarked canonical word coordinate

A physical mean with its background and exact derivative correction is read
as the bounded harmonic mean of a sorted word in the chosen chart. Its side
limit follows directly from the existing boundary theorem for that mean.
Identifying the word with a retained history is a separate obligation.
-/

set_option autoImplicit false

noncomputable section

open Filter Set Topology
open QuantumZipper (H chiC)
open InteractingSLE.Restart

namespace InteractingSLE.Theorem14.SB.S3

/-- An exact chart expression for a corrected physical mean on the selected
approach, with an unmarked boundary coordinate. No boundary limit of the
physical mean is assumed. -/
structure IsChartWordMean (κ : ℝ) (word : BoundaryWord) (x : ℝ)
    (F : Filter ℂ) (v u₀ : ℂ → ℝ) (L : ℂ → ℂ) : Prop where
  sorted : word.IsSorted
  unmarked : x ∉ word.jumps
  readout : ∃ q : ℂ → ℂ, Tendsto q F (𝓝[H] (x : ℂ)) ∧
    ∀ᶠ z in F, v z + u₀ z + chiC κ * (L z).im = word.mean (q z)

/-- The physical side height is precisely the unmarked word value. -/
theorem IsChartWordMean.tendsto {κ : ℝ} {word : BoundaryWord} {x : ℝ}
    {F : Filter ℂ} {v u₀ : ℂ → ℝ} {L : ℂ → ℂ}
    (h : IsChartWordMean κ word x F v u₀ L) :
    Tendsto (fun z => v z + u₀ z + chiC κ * (L z).im) F (𝓝 (word.fn x)) := by
  obtain ⟨q, hq, hread⟩ := h.readout
  have hword := (word.isBoundedHarmonicExtension_mean h.sorted).2.2 x h.unmarked
  refine (hword.comp hq).congr' ?_
  filter_upwards [hread] with z hz using hz.symm

end InteractingSLE.Theorem14.SB.S3
