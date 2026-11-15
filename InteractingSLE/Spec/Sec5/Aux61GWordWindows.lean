/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GWordBuffers

/-! # Countably many windows capture every completed interior slit

The indices consist of two finite basis unions and a rational seed gap.
They are fixed before seeing the slit. Compactness selects a capturing
member whose buffer meets the real axis only in the permitted open patches.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology
open QuantumZipper (H)
open scoped NNReal

namespace InteractingSLE.Sec5.Aux61GWord
open Aux61GInst

/-- A countable index for inner and outer buffers and a rational seed gap. -/
abbrev WindowIndex := BufferIndex × BufferIndex × ℚ

/-- The continuation window excludes real points outside its seed gap. -/
def bufferedWindow (i : WindowIndex) : Set ℂ :=
  seedExitWindow (basisBuffer i.1) (i.2.2 : ℝ)

/-- The outer buffer of a candidate window. -/
def outerBuffer (i : WindowIndex) : Set ℂ := basisBuffer i.2.1

/-- Valid seed windows, still a countable type: the seed is in the window,
the inner closure lies in the outer buffer, and the outer closure is compact. -/
abbrev SeedWindowIndex := {i : WindowIndex // 0 < (i.2.2 : ℝ) ∧
  (0 : ℂ) ∈ bufferedWindow i ∧ closure (basisBuffer i.1) ⊆ outerBuffer i ∧
  IsCompact (closure (outerBuffer i))}

/-- A completed interior slit with a nonzero real endpoint is captured by
one member of a fixed countable family, with a compact outer buffer. -/
theorem exists_bufferedWindow_of_completed_segment {γ : ℝ≥0 → ℂ} {e : ℝ≥0}
    (hc : ContinuousOn γ (Iic e)) (hγ0 : γ 0 = 0)
    (hinterior : ∀ t : ℝ≥0, 0 < t → t < e → γ t ∈ H)
    {y : ℝ} (hend : γ e = (y : ℂ)) (hy : y ≠ 0)
    {O : Set ℝ} (hO : IsOpen O) (hO0 : 0 ∈ O) (hOy : y ∈ O) :
    ∃ i : SeedWindowIndex, 0 < ((i : WindowIndex).2.2 : ℝ) ∧ IsOpen (bufferedWindow i) ∧
      (0 : ℂ) ∈ bufferedWindow i ∧
      closure (basisBuffer (i : WindowIndex).1) ⊆ outerBuffer i ∧
      bufferedWindow i ⊆ outerBuffer i ∧ γ '' Iic e ⊆ basisBuffer (i : WindowIndex).1 ∧
      IsCompact (closure (outerBuffer i)) ∧
      (∀ z ∈ closure (outerBuffer i), z.im = 0 → z.re ∈ O) ∧
      (∀ t : ℝ≥0, t < e → γ t ∈ bufferedWindow i) ∧ (y : ℂ) ∉ bufferedWindow i := by
  obtain ⟨δ, hδ0, hδy⟩ := exists_rat_btwn (abs_pos.2 hy)
  obtain ⟨-, U, -, hUo, -, -, hKU, -, -, -, hUr⟩ :=
    Aux61GCont.exists_window_of_completed_segment hc hγ0 hinterior hend hδ0 hδy.le hO hO0 hOy
  have hI : IsCompact (Iic e) := by
    convert isCompact_Icc (a := (0 : ℝ≥0)) (b := e) using 1
    ext t
    simp only [mem_Iic, mem_Icc, zero_le, true_and]
  have hK : IsCompact (γ '' Iic e) := hI.image_of_continuousOn hc
  obtain ⟨s, t, hKs, hst, htU, -, htc⟩ := exists_nested_basisBuffers hK hUo hKU
  have h0 : (0 : ℂ) ∈ basisBuffer s := hKs ⟨0, mem_Iic.2 zero_le, hγ0⟩
  have hV0 := zero_mem_seedExitWindow h0 hδ0
  let i : SeedWindowIndex := ⟨(s, t, δ), hδ0, hV0, hst, htc⟩
  refine ⟨i, hδ0, isOpen_seedExitWindow (isOpen_basisBuffer s) _, hV0,
    hst, sdiff_subset.trans (subset_closure.trans hst), hKs, htc, ?_, ?_, ?_⟩
  · intro z hz hz0
    exact hUr z (subset_closure (htU hz)) hz0
  · intro u hue
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ u) with hu0 | hu0
    · rw [← hu0, hγ0]
      exact hV0
    · exact ⟨hKs ⟨u, mem_Iic.2 hue.le, rfl⟩,
        fun hbad => (ne_of_gt (hinterior u hu0 hue)) hbad.1⟩
  · intro hbad
    exact hbad.2 ⟨Complex.ofReal_im y, by
      simpa only [Complex.ofReal_re] using hδy.le⟩

end InteractingSLE.Sec5.Aux61GWord
