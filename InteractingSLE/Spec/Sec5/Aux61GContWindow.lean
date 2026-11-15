/-
Copyright (c) 2026 InteractingSLE contributors. All rights reserved.
-/
import InteractingSLE.Spec.Sec5.Aux61GInstCorrection
import InteractingSLE.Spec.Sec5.Aux61GInstExitWindow

/-! # Buffered windows containing the completed slit

The compact completed slit lies in the buffer, while the continuation
window contains its pre-contact part and excludes the comparison endpoint.
The construction reuses regular-space compact-neighbourhood selection.
-/

set_option autoImplicit false
noncomputable section
open Set Filter Topology Metric
open scoped NNReal
open QuantumZipper (H)

namespace InteractingSLE.Sec5.Aux61GCont
open Aux61GInst Aux61Cov

/-- A compact slit whose real points lie in the allowed boundary patches
has nested open buffers with compact closures in the reflected domain. -/
theorem exists_nested_buffers {K : Set ℂ} (hK : IsCompact K)
    {O : Set ℝ} (hO : IsOpen O) (hreal : ∀ z ∈ K, z.im = 0 → z.re ∈ O) :
    ∃ U₀ U : Set ℂ, IsOpen U₀ ∧ IsOpen U ∧ K ⊆ U₀ ∧ closure U₀ ⊆ U ∧
      IsCompact (closure U₀) ∧ IsCompact (closure U) ∧
      ∀ z ∈ closure U, z.im = 0 → z.re ∈ O := by
  have hKR : K ⊆ reflDom O := fun z hz hbad => hbad.2 (hreal z hz hbad.1)
  obtain ⟨U, hUo, hKU, hUR, hUc⟩ :=
    exists_open_between_and_isCompact_closure hK (isOpen_reflDom hO) hKR
  obtain ⟨U₀, hU₀o, hKU₀, hU₀U, hU₀c⟩ :=
    exists_open_between_and_isCompact_closure hK hUo hKU
  exact ⟨U₀, U, hU₀o, hUo, hKU₀, hU₀U, hU₀c, hUc,
    fun z hz hz0 => not_not.1 (fun hn => hUR hz ⟨hz0, hn⟩)⟩

/-- The continuation window contains zero and every interior point of the
compact slit. Its buffer contains the whole slit, including real endpoints. -/
theorem exists_buffered_seedWindow {K : Set ℂ} (hK : IsCompact K) (h0 : (0 : ℂ) ∈ K)
    {O : Set ℝ} (hO : IsOpen O) (hreal : ∀ z ∈ K, z.im = 0 → z.re ∈ O)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ V U : Set ℂ, IsOpen V ∧ IsOpen U ∧ (0 : ℂ) ∈ V ∧ V ⊆ U ∧
      K ⊆ U ∧ K ∩ H ⊆ V ∧ IsCompact (closure U) ∧
      (∀ z ∈ closure U, z.im = 0 → z.re ∈ O) ∧
      (∀ z ∈ V, z.im = 0 → |z.re| < δ) := by
  obtain ⟨U₀, U, hU₀o, hUo, hKU₀, hU₀U, -, hUc, hUr⟩ := exists_nested_buffers hK hO hreal
  refine ⟨seedExitWindow U₀ δ, U, isOpen_seedExitWindow hU₀o δ, hUo,
    zero_mem_seedExitWindow (hKU₀ h0) hδ, sdiff_subset.trans (subset_closure.trans hU₀U),
    hKU₀.trans (subset_closure.trans hU₀U), ?_, hUc, hUr, ?_⟩
  · intro z hz
    exact ⟨hKU₀ hz.1, fun hn => (ne_of_gt hz.2) hn.1⟩
  · intro z hz hz0
    exact lt_of_not_ge fun hn => hz.2 ⟨hz0, hn⟩

/-- For an actual continuous segment with exactly its seed and endpoint
on the real axis, open patches around those points suffice to select the
buffer and continuation window used in the cutoff construction. -/
theorem exists_window_of_completed_segment {γ : ℝ≥0 → ℂ} {e : ℝ≥0}
    (hc : ContinuousOn γ (Iic e)) (hγ0 : γ 0 = 0)
    (hinterior : ∀ t : ℝ≥0, 0 < t → t < e → γ t ∈ H)
    {y δ : ℝ} (hend : γ e = (y : ℂ)) (hδ : 0 < δ) (hyδ : δ ≤ |y|)
    {O : Set ℝ} (hO : IsOpen O) (hO0 : 0 ∈ O) (hOy : y ∈ O) :
    ∃ V U : Set ℂ, IsOpen V ∧ IsOpen U ∧ (0 : ℂ) ∈ V ∧ V ⊆ U ∧
      γ '' Iic e ⊆ U ∧ (∀ t : ℝ≥0, t < e → γ t ∈ V) ∧
      (y : ℂ) ∉ V ∧ IsCompact (closure U) ∧
      ∀ z ∈ closure U, z.im = 0 → z.re ∈ O := by
  let K := γ '' Iic e
  have hi : IsCompact (Iic e) := by
    have he : Icc (0 : ℝ≥0) e = Iic e := by
      ext t
      simp only [mem_Icc, mem_Iic, zero_le, true_and]
    rw [← he]
    exact isCompact_Icc
  have hK : IsCompact K := hi.image_of_continuousOn hc
  have h0 : (0 : ℂ) ∈ K := ⟨0, mem_Iic.2 zero_le, hγ0⟩
  have hreal : ∀ z ∈ K, z.im = 0 → z.re ∈ O := by
    rintro z ⟨t, ht, rfl⟩ hz0
    rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with ht0 | ht0
    · simpa only [← ht0, hγ0, Complex.zero_re] using hO0
    · rcases lt_or_eq_of_le (mem_Iic.1 ht) with hte | rfl
      · exact False.elim ((ne_of_gt (hinterior t ht0 hte)) hz0)
      · simpa only [hend, Complex.ofReal_re] using hOy
  obtain ⟨V, U, hVo, hUo, hV0, hVU, hKU, hKH, hUc, hUr, hVr⟩ :=
    exists_buffered_seedWindow hK h0 hO hreal hδ
  refine ⟨V, U, hVo, hUo, hV0, hVU, hKU, fun t ht => ?_, ?_, hUc, hUr⟩
  · rcases eq_or_lt_of_le (zero_le : (0 : ℝ≥0) ≤ t) with ht0 | ht0
    · simpa only [← ht0, hγ0] using hV0
    · exact hKH ⟨⟨t, mem_Iic.2 ht.le, rfl⟩, hinterior t ht0 ht⟩
  · intro hyV
    have hlt := hVr _ hyV (by simp only [Complex.ofReal_im])
    rw [Complex.ofReal_re] at hlt
    exact (not_lt_of_ge hyδ) hlt

end InteractingSLE.Sec5.Aux61GCont
