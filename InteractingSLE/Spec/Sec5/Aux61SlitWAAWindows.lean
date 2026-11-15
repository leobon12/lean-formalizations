/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GWordWindows

/-! # Countable capturing windows inside a prescribed open neighborhood

The fixed countable buffer family can be selected inside any open set
containing the completed slit. This retains real-boundary control and an
arbitrarily small seed gap while controlling the whole outer closure.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology Metric
open QuantumZipper (H)
open scoped NNReal

namespace InteractingSLE.Sec5.Aux61SlitWAA
open Aux61GWord Aux61GInst

/-- A completed slit has a countable capturing window whose outer closure
stays in any prescribed open neighborhood of the whole completed slit. -/
theorem exists_bufferedWindow_in_open {γ : ℝ≥0 → ℂ} {e : ℝ≥0}
    (hc : ContinuousOn γ (Iic e)) (hγ0 : γ 0 = 0)
    (hinterior : ∀ t : ℝ≥0, 0 < t → t < e → γ t ∈ H)
    {y ε : ℝ} (hend : γ e = (y : ℂ)) (hy : y ≠ 0) (hε : 0 < ε)
    {O : Set ℝ} (hO : IsOpen O) (hO0 : 0 ∈ O) (hOy : y ∈ O)
    {A : Set ℂ} (hA : IsOpen A) (hγA : γ '' Iic e ⊆ A) :
    ∃ i : SeedWindowIndex,
      0 < ((i : WindowIndex).2.2 : ℝ) ∧ ((i : WindowIndex).2.2 : ℝ) < ε ∧
      IsOpen (bufferedWindow i) ∧ (0 : ℂ) ∈ bufferedWindow i ∧
      γ '' Iic e ⊆ basisBuffer (i : WindowIndex).1 ∧
      IsCompact (closure (outerBuffer i)) ∧ closure (outerBuffer i) ⊆ A ∧
      (∀ z ∈ closure (outerBuffer i), z.im = 0 → z.re ∈ O) ∧
      (∀ t : ℝ≥0, t < e → γ t ∈ bufferedWindow i) ∧ (y : ℂ) ∉ bufferedWindow i := by
  obtain ⟨δ, hδ0, hδ⟩ := exists_rat_btwn (lt_min hε (abs_pos.2 hy))
  obtain ⟨-, U, -, hUo, -, -, hKU, -, -, -, hUr⟩ :=
    Aux61GCont.exists_window_of_completed_segment hc hγ0 hinterior hend hδ0
      (hδ.trans_le (min_le_right _ _)).le hO hO0 hOy
  have hI : IsCompact (Iic e) := by
    convert isCompact_Icc (a := (0 : ℝ≥0)) (b := e) using 1
    ext t
    simp only [mem_Iic, mem_Icc, zero_le, true_and]
  have hK : IsCompact (γ '' Iic e) := hI.image_of_continuousOn hc
  obtain ⟨s, t, hKs, hst, htU, -, htc⟩ := exists_nested_basisBuffers hK (hUo.inter hA)
    (fun z hz => ⟨hKU hz, hγA hz⟩)
  have h0 : (0 : ℂ) ∈ basisBuffer s := hKs ⟨0, mem_Iic.2 zero_le, hγ0⟩
  have hV0 := zero_mem_seedExitWindow h0 hδ0
  let i : SeedWindowIndex := ⟨(s, t, δ), hδ0, hV0, hst, htc⟩
  refine ⟨i, hδ0, hδ.trans_le (min_le_left _ _),
    isOpen_seedExitWindow (isOpen_basisBuffer s) _, hV0, hKs, htc,
    fun z hz => (htU hz).2, ?_, ?_, ?_⟩
  · intro z hz hz0
    exact hUr z (subset_closure (htU hz).1) hz0
  · intro u hue
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ u) with hu0 | hu0
    · rw [← hu0, hγ0]
      exact hV0
    · exact ⟨hKs ⟨u, mem_Iic.2 hue.le, rfl⟩,
        fun hbad => (ne_of_gt (hinterior u hu0 hue)) hbad.1⟩
  · intro hbad
    exact hbad.2 ⟨Complex.ofReal_im y, by
      simpa only [Complex.ofReal_re] using (hδ.trans_le (min_le_right _ _)).le⟩

end InteractingSLE.Sec5.Aux61SlitWAA
